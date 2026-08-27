#!/usr/bin/env python3
"""Build a neutral, offline Hugging Face bundle for the IChO 2026 Lean corpus.

The exporter intentionally has no upload support.  It copies only an explicit
allowlist, derives records from the checked-in source inventory and reports,
and refuses to publish an incomplete or provenance-ambiguous tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, NoReturn


# This is the release contract for this particular corpus, not a cached result
# from a previous run.  All other counts and provenance are derived at export.
REQUIRED_TARGET_COUNT = 32
SCHEMA_VERSION = "1.0"
DATA_FILE = PurePosixPath("data/icho_2026_lean.jsonl")

# Code that defines or prepares the public record schema is part of the
# provenance closure, just like the checked-in data it consumes.  Keep this
# allowlist explicit so a new release helper cannot silently change the bundle
# while it still claims an older source commit.
_EXPORTER_SOURCE_PATH = PurePosixPath("scripts/export_hf_dataset.py")
_SCHEMA_CRITICAL_SOURCE_PATHS = (
    _EXPORTER_SOURCE_PATH,
    PurePosixPath("scripts/select_theory_targets.py"),
)

_PROBLEM_NAME_RE = re.compile(r"problem_icho_2026_t\d+_a\d+\.lean\Z")
_THEORY_PAPER_RE = re.compile(r"T[1-9]\Z")
_IMPORT_RE = re.compile(r"(?m)^\s*import\s+(\S+)\s*$")
_ACTIVE_LEAN_RE = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|sorryAx)\b"
)
_STALE_WORKFLOW_PROSE_PATTERNS = (
    re.compile(r"\bredraft\b", re.IGNORECASE),
    re.compile(r"\bautoformaliz\w*\b", re.IGNORECASE),
    re.compile(r"\bproof\s+bodies\s+are\s+left\s+as\b", re.IGNORECASE),
    re.compile(
        r"\bcreate\s+a\s+compiling\s+Lean\s+file\s+with\s+sorry\s+bodies\b",
        re.IGNORECASE,
    ),
    re.compile(r"\bnot\s+a\s+proof\s+task\b", re.IGNORECASE),
    re.compile(r"\bby\s+sorry\b", re.IGNORECASE),
)
_USER_MARKER_RE = re.compile(r"\bUSER\b")
_SECRET_PATTERNS = (
    re.compile(r"\bhf_[A-Za-z0-9]{16,}\b"),
    re.compile(r"\bsk-[A-Za-z0-9_-]{16,}\b"),
    re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    re.compile(
        r"(?i)\b(?:api[_-]?key|auth[_-]?token|access[_-]?token|secret)"
        r"\s*[:=]\s*['\"]?[A-Za-z0-9_./+-]{12,}"
    ),
)
_ABSOLUTE_PATH_PATTERNS = (
    re.compile(r"(?<![:/\w])/(?!/)(?:[A-Za-z0-9._-]+/)+[A-Za-z0-9._-]+"),
    re.compile(r"/(?:root|home|Users|tmp)(?:/|\b)"),
    re.compile(r"\b[A-Za-z]:[\\/][^\s'\"]+"),
)
_BANNED_OUTPUT_COMPONENTS = {
    ".archon",
    ".lake",
    ".mcp",
    "blueprint",
    "blueprints",
    "runtime",
}


class ExportError(RuntimeError):
    """Raised when the public-release contract is not satisfied."""


@dataclass(frozen=True)
class Target:
    """One inventory entry and its corresponding Lean source."""

    entry: dict[str, object]
    lean_relative: PurePosixPath
    lean_source: str

    @property
    def module(self) -> str:
        return ".".join(self.lean_relative.with_suffix("").parts)


def _fail(message: str) -> NoReturn:
    raise ExportError(message)


def _read_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        _fail(f"cannot read JSON file {path}: {exc}")
    if not isinstance(value, dict):
        _fail(f"expected a JSON object in {path}")
    return value


def _read_jsonl(path: Path) -> list[dict[str, object]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        _fail(f"cannot read JSONL file {path}: {exc}")
    records: list[dict[str, object]] = []
    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            _fail(f"invalid JSON on {path}:{line_number}: {exc}")
        if not isinstance(record, dict):
            _fail(f"expected an object on {path}:{line_number}")
        records.append(record)
    return records


def _require_plain_file(path: Path) -> None:
    if path.is_symlink() or not path.is_file():
        _fail(f"required regular file is missing or is a symlink: {path}")


def _strip_lean_comments_and_strings(source: str) -> str:
    """Blank nested comments and string literals in Lean text."""

    chars = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    quote: str | None = None
    escaped = False

    while index < len(chars):
        current = chars[index]
        following = chars[index + 1] if index + 1 < len(chars) else ""

        if in_line_comment:
            if current == "\n":
                in_line_comment = False
            else:
                chars[index] = " "
            index += 1
            continue

        if block_depth:
            if current == "/" and following == "-":
                chars[index] = chars[index + 1] = " "
                block_depth += 1
                index += 2
            elif current == "-" and following == "/":
                chars[index] = chars[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if current != "\n":
                    chars[index] = " "
                index += 1
            continue

        if quote is not None:
            if current != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == quote:
                quote = None
            index += 1
            continue

        if current == "-" and following == "-":
            chars[index] = chars[index + 1] = " "
            in_line_comment = True
            index += 2
        elif current == "/" and following == "-":
            chars[index] = chars[index + 1] = " "
            block_depth = 1
            index += 2
        elif current == '"':
            chars[index] = " "
            quote = current
            index += 1
        else:
            index += 1

    return "".join(chars)


def _validate_lean_source(relative: PurePosixPath, source: str) -> None:
    active_source = _strip_lean_comments_and_strings(source)
    match = _ACTIVE_LEAN_RE.search(active_source)
    if match:
        line_number = active_source.count("\n", 0, match.start()) + 1
        _fail(
            f"active prohibited Lean token {match.group(0)!r} in "
            f"{relative}:{line_number}"
        )


def _safe_problem_path(raw_path: object) -> PurePosixPath:
    if not isinstance(raw_path, str) or "\\" in raw_path:
        _fail(f"invalid Lean output path in source report: {raw_path!r}")
    path = PurePosixPath(raw_path)
    if (
        path.is_absolute()
        or ".." in path.parts
        or len(path.parts) != 2
        or path.parts[0] != "IChO2026Problems"
        or not _PROBLEM_NAME_RE.fullmatch(path.name)
    ):
        _fail(f"Lean output path is outside the public problem directory: {raw_path}")
    return path


def _record_id(entry: dict[str, object], origin: Path) -> str:
    record_id = entry.get("id")
    if not isinstance(record_id, str) or not record_id:
        _fail(f"missing string id in {origin}")
    return record_id


def _validate_inventory_entry(entry: dict[str, object], origin: Path) -> None:
    string_fields = (
        "id",
        "source_index",
        "problem_id",
        "part_id",
        "current_question",
        "shared_context",
        "answer",
        "category",
        "dataset",
        "paper",
        "kind",
        "source_url",
        "solution_url",
        "source_pdf",
        "solution_pdf",
    )
    for field in string_fields:
        if not isinstance(entry.get(field), str) or not entry[field]:
            _fail(f"missing non-empty string {field!r} in {origin}")
    # `kind` is the answer/task modality, not the exam-paper family.  Some
    # selected theory-paper questions are intentionally tagged `classification`.
    if not _THEORY_PAPER_RE.fullmatch(entry["paper"]):
        _fail(
            f"non-theory paper in release inventory: "
            f"{entry['id']} ({entry['paper']})"
        )
    if not isinstance(entry.get("points"), (int, float)):
        _fail(f"missing numeric points in {origin}")
    if not isinstance(entry.get("source_page"), int) or not isinstance(
        entry.get("printed_page"), int
    ):
        _fail(f"missing integer page metadata in {origin}")
    if not isinstance(entry.get("previous_parts"), list):
        _fail(f"previous_parts must be a list in {origin}")
    images = entry.get("images")
    if not isinstance(images, list) or not all(isinstance(item, str) for item in images):
        _fail(f"images must be a list of filenames in {origin}")


def _load_targets(project: Path) -> list[Target]:
    inventory_path = project / "references" / "icho_2026_theory_ready.jsonl"
    _require_plain_file(inventory_path)
    inventory_records = _read_jsonl(inventory_path)
    inventory: dict[str, dict[str, object]] = {}
    for entry in inventory_records:
        _validate_inventory_entry(entry, inventory_path)
        record_id = _record_id(entry, inventory_path)
        if record_id in inventory:
            _fail(f"duplicate inventory id: {record_id}")
        inventory[record_id] = entry

    report_dir = project / "reports" / "icho_2026"
    report_paths = sorted(report_dir.glob("*.source.json"))
    problem_paths = sorted(
        path
        for path in (project / "IChO2026Problems").rglob("*.lean")
        if _PROBLEM_NAME_RE.fullmatch(path.name)
    )
    observed_counts = {
        "inventory records": len(inventory),
        "source reports": len(report_paths),
        "problem Lean files": len(problem_paths),
    }
    wrong_counts = {
        label: count
        for label, count in observed_counts.items()
        if count != REQUIRED_TARGET_COUNT
    }
    if wrong_counts:
        details = ", ".join(f"{label}={count}" for label, count in wrong_counts.items())
        _fail(f"release requires exactly {REQUIRED_TARGET_COUNT} targets; {details}")

    reports: dict[str, tuple[dict[str, object], PurePosixPath]] = {}
    for report_path in report_paths:
        _require_plain_file(report_path)
        report = _read_json(report_path)
        report_entry = report.get("entry")
        if not isinstance(report_entry, dict):
            _fail(f"missing entry object in {report_path}")
        if report.get("official_answer_seen") is not False:
            _fail(f"source report is not answer-blind: {report_path}")
        if report_entry.get("answer") is not None:
            _fail(
                f"source report contains an unredacted official answer: {report_path}"
            )
        if report_entry.get("evaluation_mode") != "answer_blind":
            _fail(f"source report has the wrong evaluation mode: {report_path}")
        if report_entry.get("protocol") != "icho-answer-blind-v1":
            _fail(f"source report has the wrong blind protocol: {report_path}")
        if report_entry.get("dataset") != (
            "IChO 2026 official English problem materials"
        ):
            _fail(f"source report has the wrong blind dataset label: {report_path}")
        for hidden_field in ("source_url", "solution_url", "solution_pdf"):
            if report_entry.get(hidden_field) is not None:
                _fail(
                    f"source report exposes hidden field {hidden_field}: {report_path}"
                )
        blind_previous_parts = report_entry.get("previous_parts")
        if not isinstance(blind_previous_parts, list) or any(
            not isinstance(part, dict) or "answer" in part
            for part in blind_previous_parts
        ):
            _fail(f"source report exposes a previous-part answer: {report_path}")
        if not isinstance(report_entry.get("shared_context"), str) or not report_entry[
            "shared_context"
        ]:
            _fail(f"source report has no shared problem context: {report_path}")
        record_id = _record_id(report_entry, report_path)
        if record_id in reports:
            _fail(f"duplicate source-report id: {record_id}")
        lean_relative = _safe_problem_path(report.get("output_lean"))
        expected_lean_name = f"problem_{record_id}.lean"
        expected_report_name = f"problem_{record_id}.source.json"
        if lean_relative.name != expected_lean_name or report_path.name != expected_report_name:
            _fail(f"source-report filenames do not match id {record_id}")
        reports[record_id] = (report_entry, lean_relative)

    if set(inventory) != set(reports):
        missing_reports = sorted(set(inventory) - set(reports))
        extra_reports = sorted(set(reports) - set(inventory))
        _fail(
            "inventory/source-report id mismatch: "
            f"missing={missing_reports}, extra={extra_reports}"
        )

    actual_problem_relatives = {
        PurePosixPath(path.relative_to(project).as_posix()) for path in problem_paths
    }
    reported_problem_relatives = {path for _, path in reports.values()}
    if actual_problem_relatives != reported_problem_relatives:
        missing = sorted(
            str(path)
            for path in reported_problem_relatives - actual_problem_relatives
        )
        extra = sorted(
            str(path)
            for path in actual_problem_relatives - reported_problem_relatives
        )
        _fail(f"source-report/Lean-file mismatch: missing={missing}, extra={extra}")

    emitted_source_fields = (
        "source_index",
        "problem_id",
        "part_id",
        "current_question",
        "category",
        "points",
        "paper",
        "kind",
        "images",
        "source_pdf",
        "source_page",
        "printed_page",
    )
    targets: list[Target] = []
    for record_id in sorted(inventory):
        entry = inventory[record_id]
        report_entry, lean_relative = reports[record_id]
        for field in emitted_source_fields:
            if entry.get(field) != report_entry.get(field):
                _fail(f"inventory/source-report mismatch for {record_id}.{field}")
        lean_path = project.joinpath(*lean_relative.parts)
        _require_plain_file(lean_path)
        try:
            lean_source = lean_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            _fail(f"cannot read Lean source {lean_path}: {exc}")
        _validate_lean_source(lean_relative, lean_source)
        release_entry = dict(entry)
        release_entry["shared_context"] = report_entry["shared_context"]
        targets.append(Target(release_entry, lean_relative, lean_source))

    umbrella_path = project / "IChO2026Problems.lean"
    _require_plain_file(umbrella_path)
    umbrella_imports = set(_IMPORT_RE.findall(umbrella_path.read_text(encoding="utf-8")))
    if "IChO2026Problems.All" not in umbrella_imports:
        _fail("problem umbrella does not import IChO2026Problems.All")

    all_path = project / "IChO2026Problems" / "All.lean"
    _require_plain_file(all_path)
    all_imports = set(_IMPORT_RE.findall(all_path.read_text(encoding="utf-8")))
    target_imports = {target.module for target in targets}
    if all_imports != target_imports:
        missing_imports = sorted(target_imports - all_imports)
        extra_imports = sorted(all_imports - target_imports)
        _fail(
            "IChO2026Problems.All import mismatch: "
            f"missing={missing_imports}, extra={extra_imports}"
        )
    return targets


def _public_source(entry: dict[str, object]) -> dict[str, object]:
    return {
        "competition": "International Chemistry Olympiad",
        "year": 2026,
        "dataset": entry.get("dataset"),
        "category": entry.get("category"),
        "paper": entry.get("paper"),
        "problem_id": entry.get("problem_id"),
        "part_id": entry.get("part_id"),
        "source_index": entry.get("source_index"),
        "kind": entry.get("kind"),
        "points": entry.get("points"),
        "printed_page": entry.get("printed_page"),
        "pdf_page": entry.get("source_page"),
        "question": entry.get("current_question"),
        "shared_context": entry.get("shared_context"),
        "official_answer": entry.get("answer"),
        "previous_parts": entry.get("previous_parts", []),
        "urls": {
            "problem": entry.get("source_url"),
            "solution": entry.get("solution_url"),
        },
        "source_files": {
            "problem_pdf": entry.get("source_pdf"),
            "solution_pdf": entry.get("solution_pdf"),
            "image_filenames": entry.get("images", []),
        },
    }


def _dataset_record(target: Target, source_commit: str) -> dict[str, object]:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": target.entry["id"],
        "source": _public_source(target.entry),
        "formalization": {
            "language": "Lean 4",
            "module": target.module,
            "file": target.lean_relative.as_posix(),
            "source": target.lean_source,
        },
        "provenance": {"source_commit": source_commit},
    }


def _git_metadata(project: Path, source_files: Iterable[Path]) -> tuple[Path, str]:
    try:
        repo_text = subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], cwd=project, text=True
        ).strip()
        source_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=project, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        _fail(f"cannot determine Git provenance: {exc}")
    repo = Path(repo_text).resolve()
    license_path = repo / "LICENSE"
    _require_plain_file(license_path)
    relative_files: list[str] = []
    for source in (*source_files, license_path):
        resolved = source.resolve()
        try:
            relative_files.append(resolved.relative_to(repo).as_posix())
        except ValueError:
            _fail(f"release source is outside the Git repository: {source}")
    relative_files = sorted(set(relative_files))
    tracked = subprocess.run(
        ["git", "ls-files", "--cached", "-z", "--", *relative_files],
        cwd=repo,
        check=False,
        capture_output=True,
    )
    if tracked.returncode != 0:
        stderr = tracked.stderr.decode(errors="replace").strip()
        _fail(f"cannot verify tracked release sources: {stderr}")
    tracked_files = {
        path.decode(errors="surrogateescape")
        for path in tracked.stdout.split(b"\0")
        if path
    }
    untracked_files = sorted(set(relative_files) - tracked_files)
    if untracked_files:
        _fail(
            "public release sources must be tracked and clean before export; "
            f"untracked={untracked_files}"
        )
    status = subprocess.run(
        [
            "git",
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--",
            *relative_files,
        ],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    if status.returncode != 0:
        _fail(f"cannot verify Git provenance: {status.stderr.strip()}")
    if status.stdout.strip():
        _fail("public release sources must be tracked and clean before export")
    return repo, source_commit


def _schema_critical_sources(project: Path) -> list[Path]:
    paths = [
        project.joinpath(*relative.parts)
        for relative in _SCHEMA_CRITICAL_SOURCE_PATHS
    ]
    for path in paths:
        _require_plain_file(path)
    running_exporter = Path(__file__).resolve()
    expected_exporter = project.joinpath(*_EXPORTER_SOURCE_PATH.parts).resolve()
    if running_exporter != expected_exporter:
        _fail(
            "the exporter must be executed from the release project so its "
            "Git provenance can be verified"
        )
    return paths


def _lean_sources(project: Path, targets: list[Target]) -> list[Path]:
    paths = [project.joinpath(*target.lean_relative.parts) for target in targets]
    roots = (
        project / "IChO2026Problems.lean",
        project / "IChO2026Problems" / "All.lean",
        project / "IChO2026Chem.lean",
        project / "IChO2026Run.lean",
    )
    paths.extend(roots)
    for directory in (project / "IChO2026Chem", project / "IChO2026Run"):
        if not directory.is_dir() or directory.is_symlink():
            _fail(f"required Lean source directory is missing or is a symlink: {directory}")
        paths.extend(sorted(directory.rglob("*.lean")))
    unique_paths = sorted(set(paths))
    for path in unique_paths:
        _require_plain_file(path)
        source = path.read_text(encoding="utf-8")
        relative = PurePosixPath(path.relative_to(project).as_posix())
        _validate_lean_source(relative, source)
    return unique_paths


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _copy_text(source: Path, destination: Path) -> None:
    _require_plain_file(source)
    _write_text(destination, source.read_text(encoding="utf-8"))


def _dataset_card(target_count: int, source_commit: str) -> str:
    return f"""---
language:
- en
license: other
pretty_name: IChO 2026 Lean 4 Formalizations
task_categories:
- text-generation
tags:
- chemistry
- lean
- theorem-proving
size_categories:
- n<1K
configs:
- config_name: default
  data_files:
  - split: test
    path: {DATA_FILE.as_posix()}
---

# IChO 2026 Lean 4 Formalizations

This release contains {target_count} theory subquestions selected from the
official 2026 International Chemistry Olympiad materials, paired with complete
Lean 4 source files. Practical papers are outside the selected corpus.

## Data schema

Each JSONL row has five top-level fields:

- `schema_version`: release schema version.
- `id`: stable subquestion identifier.
- `source`: paper metadata, question, shared context, official answer/rubric,
  preceding-part context, official links, and source-asset filenames.
- `formalization`: Lean language, module, relative file path, and full source.
- `provenance`: the Git commit from which the release was built.

The `test` split is used because these are evaluation-style competition tasks.

## Reproduce the Lean build

The `lean/` directory is a standalone pinned Lake project:

```bash
cd lean
lake exe cache get
lake build
```

The exporter checks inventory/report/file agreement and rejects active proof
placeholders, local axiom declarations, unpublished review markers, credentials,
and machine-local paths. Compilation and kernel-axiom audits remain separate
release checks and should be reported alongside this bundle.

Source commit: `{source_commit}`.

## Generation provenance and limitations

The formalizations were produced in a fresh answer-blind campaign with
OpenAI `gpt-5.6-sol` through Codex.  The solver workspace exposed the current
problem statement and images plus pinned shared libraries, but not the official
solution or sibling-target artifacts.  The results were then checked by Lean
compilation, source-aware semantic review, kernel-axiom inspection, and the
default Lake build.  Official-solution comparison was performed only after the
campaign terminated.  Prompts, model transcripts, and runtime logs are
intentionally not published; consequently the generation-process statement is
reported provenance and cannot be established from the public bundle alone.

## Known auxiliary-carrier limitation

The requested T7-A3 outputs, `5.6662 mol` and `189 cycles`, match the official
rubric.  An auxiliary previous-part carrier nevertheless labels mixture M1 as
containing `N2`, `CO2`, and `H2`, whereas the source figure shows `N2`, `CO`,
and `H2` at that stage.  This carrier is not used to derive either requested
T7-A3 output, but the release should not be described as free of every
non-output semantic defect.

## Known official-source inconsistency

For T8-A6 the official rubric reports a quantum yield of `1.94%`.  The
official givens instead give approximately `1.9334888%`, while the rubric's
own printed intermediate expression is `474/245%`, approximately
`1.9346939%`.  Both values round to `1.93%` at two decimal places.  The Lean
theorems therefore prove the mathematically derived `1.93%`; the source record
still preserves the official `1.94%` rubric text verbatim.

## Included and excluded material

The bundle includes the JSONL records, standalone Lean project, dependency
lockfile, release manifest, checksums, and the code license. It excludes
workflow state, logs, prompts, caches, connector settings, theorem blueprints,
and local runtime files. Original PDFs and images are not redistributed;
records retain their official URLs and source filenames instead.

## Rights

The Lean code and project-authored documentation follow the included Apache-2.0
license. Exam questions, marking material, and linked assets retain the rights
and terms of their original publishers.
"""


def _validate_public_bundle(bundle: Path) -> None:
    for path in sorted(bundle.rglob("*")):
        relative = path.relative_to(bundle)
        if any(part in _BANNED_OUTPUT_COMPONENTS for part in relative.parts):
            _fail(f"prohibited path in public bundle: {relative.as_posix()}")
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeError:
            _fail(f"non-text file in public bundle: {relative.as_posix()}")
        checks: tuple[tuple[str, re.Pattern[str]], ...] = (
            *(
                ("stale workflow prose", pattern)
                for pattern in _STALE_WORKFLOW_PROSE_PATTERNS
            ),
            ("review marker", _USER_MARKER_RE),
            *(("credential", pattern) for pattern in _SECRET_PATTERNS),
            *(("absolute path", pattern) for pattern in _ABSOLUTE_PATH_PATTERNS),
        )
        for label, pattern in checks:
            match = pattern.search(text)
            if match:
                line_number = text.count("\n", 0, match.start()) + 1
                _fail(
                    f"{label} is prohibited in public bundle: "
                    f"{relative.as_posix()}:{line_number}"
                )
        if path.suffix == ".lean":
            _validate_lean_source(PurePosixPath(relative.as_posix()), text)


def _write_checksums(bundle: Path) -> None:
    checksum_path = bundle / "checksums.sha256"
    rows: list[str] = []
    for path in sorted(candidate for candidate in bundle.rglob("*") if candidate.is_file()):
        if path == checksum_path:
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append(f"{digest}  {path.relative_to(bundle).as_posix()}")
    _write_text(checksum_path, "\n".join(rows) + "\n")


def export(project: Path, output: Path) -> Path:
    project = project.resolve()
    output = output.resolve()
    if output.exists():
        _fail(f"refusing to overwrite existing output path: {output}")
    if output == project or project in output.parents:
        _fail("output must be outside the Lean project")

    targets = _load_targets(project)
    lean_sources = _lean_sources(project, targets)
    environment_sources = [
        project / "lean-toolchain",
        project / "lakefile.toml",
        project / "lake-manifest.json",
    ]
    report_sources = sorted((project / "reports" / "icho_2026").glob("*.source.json"))
    inventory_source = project / "references" / "icho_2026_theory_ready.jsonl"
    for path in environment_sources:
        _require_plain_file(path)

    provenance_sources = [
        *lean_sources,
        *environment_sources,
        *report_sources,
        *_schema_critical_sources(project),
        inventory_source,
    ]
    repo, source_commit = _git_metadata(project, provenance_sources)
    license_path = repo / "LICENSE"
    _require_plain_file(license_path)

    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(
        tempfile.mkdtemp(prefix=f".{output.name}.staging-", dir=output.parent)
    )
    try:
        records = [_dataset_record(target, source_commit) for target in targets]
        data_text = "".join(
            json.dumps(record, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
            + "\n"
            for record in records
        )
        _write_text(staging.joinpath(*DATA_FILE.parts), data_text)

        for source in lean_sources:
            _copy_text(source, staging / "lean" / source.relative_to(project))
        for source in environment_sources:
            _copy_text(source, staging / "lean" / source.name)
        _copy_text(license_path, staging / "LICENSE")

        manifest = {
            "schema_version": SCHEMA_VERSION,
            "source_commit": source_commit,
            "split": "test",
            "data_file": DATA_FILE.as_posix(),
            "record_count": len(records),
            "problem_files": [target.lean_relative.as_posix() for target in targets],
            "release_checks": {
                "inventory_report_file_sets_match": True,
                "active_prohibited_lean_tokens": 0,
                "public_content_policy": "passed",
            },
        }
        _write_text(
            staging / "metadata" / "manifest.json",
            json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        )
        _write_text(staging / "README.md", _dataset_card(len(records), source_commit))

        _validate_public_bundle(staging)
        _write_checksums(staging)
        _validate_public_bundle(staging)
        os.replace(staging, output)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return output


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build an offline, neutral IChO 2026 Lean dataset bundle."
    )
    parser.add_argument("output", type=Path, help="new output directory")
    parser.add_argument(
        "--project",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="IChO Lean project (defaults to the script's parent project)",
    )
    args = parser.parse_args()
    try:
        result = export(args.project, args.output)
    except ExportError as exc:
        parser.exit(1, f"export refused: {exc}\n")
    print(result)


if __name__ == "__main__":
    main()
