"""Build a lightweight LeanExplore-compatible index for a local Lean library.

The full LeanExplore database already supplies Mathlib and other public
libraries.  Benchmark-local domain libraries are much smaller, so rebuilding a
multi-gigabyte global FAISS database is unnecessary.  This module indexes only
explicitly selected source roots and is consumed as an overlay by
``lean_explore_overlay``.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


_DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>abbrev|axiom|class|def|inductive|instance|lemma|opaque|"
    r"structure|theorem)\s+"
    r"(?P<name>[A-Za-z_«][A-Za-z0-9_.'«»]*)\b"
)
_NAMESPACE_RE = re.compile(
    r"^[ \t]*namespace\s+(?P<name>[A-Za-z_«][A-Za-z0-9_.'«»]*)\s*$"
)
_SECTION_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|noncomputable)\s+)*"
    r"section(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*))?\s*$"
)
_END_RE = re.compile(
    r"^[ \t]*end(?:\s+(?P<name>[A-Za-z_«][A-Za-z0-9_.'«»]*))?\s*$"
)


def _git_value(project_path: Path, *args: str) -> str | None:
    proc = subprocess.run(
        ["git", *args],
        cwd=project_path,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return None
    value = proc.stdout.strip()
    return value or None


def _module_name(project_path: Path, source: Path) -> str:
    rel = source.relative_to(project_path).with_suffix("")
    return ".".join(rel.parts)


def _docstring_before(lines: list[str], line_index: int) -> str | None:
    cursor = line_index - 1
    while cursor >= 0 and not lines[cursor].strip():
        cursor -= 1
    if cursor < 0 or "-/" not in lines[cursor]:
        return None
    end = cursor
    while cursor >= 0 and "/--" not in lines[cursor]:
        if "/-!" in lines[cursor]:
            return None
        cursor -= 1
    if cursor < 0:
        return None
    raw = "".join(lines[cursor : end + 1])
    start = raw.find("/--")
    stop = raw.rfind("-/")
    if start < 0 or stop <= start:
        return None
    body = raw[start + 3 : stop]
    cleaned = " ".join(
        line.strip().lstrip("*").strip()
        for line in body.splitlines()
        if line.strip().lstrip("*").strip()
    )
    return cleaned or None


def _pop_scope(
    stack: list[tuple[str, str | None]],
    end_name: str | None,
) -> None:
    if not stack:
        return
    if not end_name:
        stack.pop()
        return
    target = end_name.split(".")[-1].strip("«»")
    while stack:
        kind, name = stack.pop()
        if name:
            tail = name.split(".")[-1].strip("«»")
            if tail == target:
                return


def _namespace_prefix(stack: list[tuple[str, str | None]]) -> str:
    return ".".join(
        str(name).strip("«»")
        for kind, name in stack
        if kind == "namespace" and name
    )


def _qualify_name(prefix: str, name: str) -> str:
    clean = name.strip("«»")
    if not prefix:
        return clean
    if clean == prefix or clean.startswith(prefix + "."):
        return clean
    return f"{prefix}.{clean}"


def _source_files(project_path: Path, roots: Iterable[Path]) -> list[Path]:
    files: set[Path] = set()
    for raw in roots:
        root = raw if raw.is_absolute() else project_path / raw
        root = root.resolve()
        try:
            root.relative_to(project_path)
        except ValueError as exc:
            raise ValueError(f"source root escapes project: {raw}") from exc
        if root.is_file():
            if root.suffix == ".lean":
                files.add(root)
            continue
        if not root.is_dir():
            raise FileNotFoundError(f"source root not found: {root}")
        files.update(path.resolve() for path in root.rglob("*.lean"))
    return sorted(files)


def _parse_file(
    project_path: Path,
    source: Path,
    *,
    package: str,
    repo_url: str | None,
    commit: str | None,
) -> list[dict[str, Any]]:
    text = source.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    module = _module_name(project_path, source)
    scopes: list[tuple[str, str | None]] = []
    declarations: list[dict[str, Any]] = []
    events: list[tuple[int, str, str, str | None]] = []

    for index, line in enumerate(lines):
        namespace = _NAMESPACE_RE.match(line)
        if namespace:
            scopes.append(("namespace", namespace.group("name")))
            events.append((index, "scope", "", None))
            continue
        section = _SECTION_RE.match(line)
        if section:
            scopes.append(("section", section.group("name")))
            events.append((index, "scope", "", None))
            continue
        ending = _END_RE.match(line)
        if ending:
            _pop_scope(scopes, ending.group("name"))
            events.append((index, "scope", "", None))
            continue
        match = _DECL_RE.match(line)
        if not match or match.group("indent"):
            continue
        name = _qualify_name(_namespace_prefix(scopes), match.group("name"))
        events.append((index, "declaration", name, match.group("kind")))

    declaration_events = [
        (position, name, kind)
        for position, event, name, kind in events
        if event == "declaration" and kind is not None
    ]
    event_positions = sorted({position for position, *_ in events})

    rel = source.relative_to(project_path).as_posix()
    for position, name, kind in declaration_events:
        following = next(
            (event for event in event_positions if event > position),
            len(lines),
        )
        source_text = "".join(lines[position:following]).rstrip()
        if not source_text:
            source_text = lines[position].rstrip()
        docstring = _docstring_before(lines, position)
        line_start = position + 1
        line_end = max(line_start, following)
        if repo_url and commit:
            source_link = (
                f"{repo_url.rstrip('/')}/blob/{commit}/{rel}"
                f"#L{line_start}-L{line_end}"
            )
        else:
            source_link = f"{source.as_uri()}#L{line_start}-L{line_end}"
        informalization = docstring or (
            f"**{name}.** {kind} declared in `{module}`. "
            + " ".join(source_text.split())[:600]
        )
        declarations.append(
            {
                "name": name,
                "kind": kind,
                "package": package,
                "module": module,
                "docstring": docstring,
                "source_text": source_text,
                "source_link": source_link,
                "dependencies": [],
                "informalization": informalization,
                "path": rel,
                "line_start": line_start,
                "line_end": line_end,
            }
        )
    return declarations


def build_project_index(
    project_path: Path,
    *,
    source_roots: Iterable[Path],
    package: str,
    output_path: Path,
    repo_url: str | None = None,
    commit: str | None = None,
) -> dict[str, Any]:
    project_path = project_path.resolve()
    files = _source_files(project_path, source_roots)
    if not files:
        raise ValueError("no Lean files selected for project index")
    commit = commit or _git_value(project_path, "rev-parse", "HEAD")
    repo_url = repo_url or _git_value(project_path, "remote", "get-url", "origin")
    declarations: list[dict[str, Any]] = []
    for source in files:
        declarations.extend(
            _parse_file(
                project_path,
                source,
                package=package,
                repo_url=repo_url,
                commit=commit,
            )
        )

    unique: dict[str, dict[str, Any]] = {}
    duplicates: list[str] = []
    for declaration in declarations:
        name = declaration["name"]
        if name in unique:
            duplicates.append(name)
            continue
        unique[name] = declaration

    toolchain_path = project_path / "lean-toolchain"
    payload = {
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "project_path": str(project_path),
        "package": package,
        "repo_url": repo_url,
        "commit": commit,
        "lean_toolchain": (
            toolchain_path.read_text(encoding="utf-8").strip()
            if toolchain_path.is_file()
            else None
        ),
        "source_files": [
            source.relative_to(project_path).as_posix() for source in files
        ],
        "declaration_count": len(unique),
        "duplicates_skipped": sorted(set(duplicates)),
        "declarations": list(unique.values()),
    }
    output_path = (
        output_path
        if output_path.is_absolute()
        else project_path / output_path
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build a project-local LeanExplore overlay index."
    )
    parser.add_argument("project_path", type=Path)
    parser.add_argument("--source-root", action="append", type=Path, required=True)
    parser.add_argument("--package", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(".archon/lean-explore/project-index.json"),
    )
    parser.add_argument("--repo-url")
    parser.add_argument("--commit")
    args = parser.parse_args()
    payload = build_project_index(
        args.project_path,
        source_roots=args.source_root,
        package=args.package,
        output_path=args.output,
        repo_url=args.repo_url,
        commit=args.commit,
    )
    print(
        json.dumps(
            {
                "package": payload["package"],
                "commit": payload["commit"],
                "lean_toolchain": payload["lean_toolchain"],
                "source_files": len(payload["source_files"]),
                "declaration_count": payload["declaration_count"],
                "duplicates_skipped": len(payload["duplicates_skipped"]),
            },
            ensure_ascii=False,
        )
    )


if __name__ == "__main__":
    main()
