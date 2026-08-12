#!/usr/bin/env python3
"""Build and verify a problem-only, answer-blind solver seed.

This program belongs on the trusted/controller side of an evaluation.  It
records a trusted patched-Archon provenance check, copies a deliberately small
IChO Lake project, then adds only the explicitly named problem artefacts.  The
Archon engine itself is installed separately in the controller-owned runtime;
no pipeline source code is copied into a solver-writable workspace.  It
does not copy Git metadata, old formalizations, reports, blueprints, reference
packs, or any controller-side dataset/script.

The seed itself is not a Git repository.  Optional GPT and K3 workspaces are
byte-for-byte copies of that seed followed by a fresh, template-free
``git init``; they have no commits and no remotes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, NamedTuple, Sequence


SCHEMA_VERSION = 1
PROTOCOL = "icho-problem-only-solver-seed-v1"
MANIFEST_NAME = "isolation_manifest.json"
BUNDLE_DESTINATION = "icho_2026_source/questions_only.jsonl"
PDF_DESTINATION_ROOT = "icho_2026_source/raw"
IMAGE_DESTINATION_ROOT = "icho_2026_source/image"

# The trusted engine is a sealed, separately inventoried wheel.  The solver
# seed deliberately carries no editable package source, pyproject, build hook,
# or package-data tree.  ``source_root`` remains a controller-only provenance
# input and never becomes solver-visible data.
REQUIRED_PROJECT_FILES: tuple[str, ...] = ()
OPTIONAL_PROJECT_FILES: tuple[str, ...] = ()
ENGINE_SOURCE_ROOT = "src/archon"

# Never recurse through the IChO run directory.  In the real checkout it also
# contains official-answer-derived Lean, reports, references, and blueprints.
# Only these generic Lake/core files are eligible to cross the boundary.
REQUIRED_LAKE_FILES = (
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "IChO2026Run/Basic.lean",
    "IChO2026Run/Dependencies.lean",
    "IChO2026Chem.lean",
    "IChO2026Chem/Core.lean",
    "IChO2026Chem/Reporting.lean",
)
OPTIONAL_LAKE_FILES = (
    ".gitignore",
    "archon-protected.yaml",
)

# These two entry points must not be inherited from an old solver run.  In
# particular, a historical IChO2026Problems umbrella can disclose all prior
# theorem names and IChO2026Run can transitively import it.  Trusted fixed
# content gives the new run an empty problem namespace while retaining the
# generic dependency probes.  Kinetics is intentionally not imported or
# present in REQUIRED_LAKE_FILES.
GENERATED_LAKE_FILES: Mapping[str, bytes] = {
    "IChO2026Problems.lean": (
        "import IChO2026Chem\n"
        "import IChO2026Problems.All\n\n"
        "/-! Fixed answer-blind umbrella. The trusted controller rewrites "
        "`IChO2026Problems/All.lean` from the authorized target scope only. -/\n"
    ).encode("utf-8"),
    "IChO2026Run.lean": (
        "import IChO2026Run.Basic\n"
        "import IChO2026Run.Dependencies\n"
        "import IChO2026Problems\n"
    ).encode("utf-8"),
}

# Harmless generated files are deliberately absent from a seed.  Directories
# capable of carrying prior-run evidence are omitted even inside package data.
IGNORED_ENGINE_COMPONENTS = {
    "__pycache__",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    "node_modules",
    "dist",
    "build",
    "references",
}
IGNORED_ENGINE_SUFFIXES = {".pyc", ".pyo", ".tsbuildinfo"}

ALLOWED_ENGINE_SUFFIXES = {
    ".css",
    ".html",
    ".in",
    ".json",
    ".lock",
    ".md",
    ".py",
    ".sh",
    ".toml",
    ".ts",
    ".tsx",
    ".txt",
    ".yaml",
    ".yml",
}
ALLOWED_ENGINE_BASENAMES = {
    ".gitignore",
    "LICENSE",
    "license",
    "pre-commit",
    "pre-push",
}
ALLOWED_IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".webp"}

FORBIDDEN_FIELD_STEMS = {
    "answer",
    "explanation",
    "grader",
    "marking",
    "reasoning",
    "rubric",
    "solution",
}
CREDENTIAL_FIELD_STEMS = {
    "credential",
    "credentials",
    "password",
    "secret",
    "token",
}
FORBIDDEN_DATA_DIRECTORIES = {
    ".git",
    ".hg",
    ".svn",
    "blueprint",
    "blueprints",
    "reports",
    "references",
}
FORBIDDEN_CREDENTIAL_NAMES = {
    ".env",
    ".gitconfig",
    ".gitcredentials",
    ".gitmodules",
    ".netrc",
    ".npmrc",
    "credentials",
    "credentials.json",
    "id_ed25519",
    "id_rsa",
}

SECRET_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("private key", re.compile(r"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----")),
    ("Anthropic token", re.compile(r"sk-ant-[A-Za-z0-9_-]{20,}")),
    ("OpenAI project token", re.compile(r"sk-proj-[A-Za-z0-9_-]{30,}")),
    ("generic provider token", re.compile(r"sk-[A-Za-z0-9]{40,}")),
    ("Google API key", re.compile(r"AIza[A-Za-z0-9_-]{30,}")),
    ("GitHub token", re.compile(r"gh[pousr]_[A-Za-z0-9]{36,251}")),
    ("GitHub fine-grained token", re.compile(r"github_pat_[A-Za-z0-9_]{82}")),
    ("GitLab token", re.compile(r"glpat-[A-Za-z0-9_-]{20,}")),
    ("AWS access-key id", re.compile(r"(?:AKIA|ASIA)[0-9A-Z]{16}")),
    ("Slack token", re.compile(r"xox[abprs]-[A-Za-z0-9-]{10,}")),
)
SECRET_ASSIGNMENT = re.compile(
    r"(?im)^\s*(?:export\s+)?"
    r"(?:[A-Z0-9_]*(?:API_KEY|AUTH_TOKEN|ACCESS_TOKEN|SECRET_KEY|PASSWORD|CREDENTIALS?))"
    r"\s*[=:]\s*['\"]?(?P<value>[A-Za-z0-9_./+\-=]{16,})"
)
ABSOLUTE_ROOT_PATH = re.compile(
    r"(?:(?<=^)|(?<=[\s'\"=:(]))/root(?:/|\b)", re.MULTILINE
)
ABSOLUTE_PROBLEM_PATH = re.compile(
    r"(?:(?<=^)|(?<=[\s'\"=(]))/"
    r"(?:etc|home|mnt|opt|private|root|srv|tmp|usr|var)(?:/|\b)",
    re.MULTILINE,
)
WINDOWS_PROBLEM_PATH = re.compile(
    r"(?i)(?:(?<=^)|(?<=[\s'\"=(]))[A-Z]:[\\/]", re.MULTILINE
)


class IsolationError(ValueError):
    """A candidate input would violate the solver isolation boundary."""


class PayloadFile(NamedTuple):
    destination: str
    data: bytes
    mode: int
    group: str


class BlindBundleContract(NamedTuple):
    """Controller-verified identity and asset contract for the blind rows."""

    target_ids: tuple[str, ...]
    asset_hashes: dict[str, str]
    image_paths: tuple[str, ...]
    pdf_path: str


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _hash_index(index: Mapping[str, str]) -> str:
    """Hash a path-to-content-hash index without depending on dict order."""

    return _sha256(_canonical_json_bytes(dict(sorted(index.items()))))


def _within(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _require_plain_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink():
        raise IsolationError(f"{label} must not be a symbolic link: {path}")
    resolved = path.resolve()
    if not resolved.is_dir():
        raise IsolationError(f"{label} is not a directory: {path}")
    return resolved


def _field_tokens(key: object) -> list[str]:
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", str(key))
    return [part.casefold() for part in re.split(r"[^A-Za-z0-9]+", text) if part]


def _forbidden_field(key: object) -> bool:
    tokens = _field_tokens(key)
    if "reusable" in tokens and any(token.startswith("conclusion") for token in tokens):
        return True
    return any(
        any(token == stem or token == stem + "s" for stem in FORBIDDEN_FIELD_STEMS)
        for token in tokens
    )


def _credential_field(key: object) -> bool:
    tokens = _field_tokens(key)
    if any(token in CREDENTIAL_FIELD_STEMS for token in tokens):
        return True
    return len(tokens) >= 2 and tokens[-2:] in (["api", "key"], ["private", "key"])


def _audit_structured(value: Any, *, location: str = "$") -> None:
    """Reject answer-bearing fields at every JSON nesting depth."""

    if isinstance(value, dict):
        for key, child in value.items():
            child_location = f"{location}.{key}"
            if str(key) == "official_answer_seen":
                if child is not False:
                    raise IsolationError(
                        f"{child_location}: answer-blind integrity flag must be false"
                    )
            elif _forbidden_field(key):
                raise IsolationError(f"{child_location}: forbidden answer-bearing field")
            elif _credential_field(key):
                raise IsolationError(f"{child_location}: forbidden credential field")
            _audit_structured(child, location=child_location)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _audit_structured(child, location=f"{location}[{index}]")
    elif isinstance(value, str):
        _audit_problem_string(value, location=location)


def _audit_problem_string(value: str, *, location: str) -> None:
    normalized = value.casefold().replace("\\", "/")
    if re.search(r"(?:^|/)solutions?(?:[./_-]|$)", normalized):
        raise IsolationError(f"{location}: forbidden solution path reference")
    if re.search(r"answer[-_ ]?page", normalized):
        raise IsolationError(f"{location}: forbidden answer-page reference")
    if ABSOLUTE_PROBLEM_PATH.search(value) or WINDOWS_PROBLEM_PATH.search(value):
        raise IsolationError(f"{location}: absolute filesystem path is forbidden")
    _audit_text(value, location=location)


def _audit_text(text: str, *, location: str) -> None:
    # Controller paths rooted in /root are never portable and can disclose
    # where sealed inputs live.  Generic engine code may legitimately parse
    # example POSIX/Windows absolute paths, so only the trusted-controller root
    # is treated as evidence here.
    if ABSOLUTE_ROOT_PATH.search(text):
        raise IsolationError(f"{location}: absolute /root path is forbidden")
    for label, pattern in SECRET_PATTERNS:
        if pattern.search(text):
            raise IsolationError(f"{location}: {label} pattern is forbidden")
    for match in SECRET_ASSIGNMENT.finditer(text):
        value = match.group("value")
        upper = value.upper()
        if not any(marker in upper for marker in ("EXAMPLE", "REDACTED", "PLACEHOLDER")):
            raise IsolationError(f"{location}: credential assignment is forbidden")


def _validate_relative_destination(raw: str) -> str:
    if "\\" in raw or "\x00" in raw:
        raise IsolationError(f"unsafe destination path: {raw!r}")
    path = PurePosixPath(raw)
    if path.is_absolute() or not path.parts or any(part in {"", ".", ".."} for part in path.parts):
        raise IsolationError(f"destination must be a normalized relative path: {raw!r}")

    folded = [part.casefold() for part in path.parts]
    for index, part in enumerate(folded):
        if part in FORBIDDEN_DATA_DIRECTORIES:
            raise IsolationError(f"forbidden directory in destination: {raw}")
        if part in FORBIDDEN_CREDENTIAL_NAMES or part.startswith(".env."):
            raise IsolationError(f"credential-bearing path is forbidden: {raw}")
        if part.endswith((".pem", ".key", ".log")):
            raise IsolationError(f"credential/task-log path is forbidden: {raw}")
        if part in {"archon_task_results", "task_logs", "task-log", "task-logs"}:
            raise IsolationError(f"task-log path is forbidden: {raw}")

        stem = PurePosixPath(part).stem
        tokens = [token for token in re.split(r"[-_.]+", stem) if token]
        if "solution" in tokens or "solutions" in tokens:
            raise IsolationError(f"solution-bearing path is forbidden: {raw}")
        if "answerpage" in tokens or (
            "answer" in tokens and "page" in tokens
        ):
            raise IsolationError(f"answer-page path is forbidden: {raw}")
        if part == "icho2026problems" or (
            part.startswith("icho2026problems.")
            and path.as_posix() != "IChO2026Problems.lean"
        ):
            raise IsolationError(f"old IChO Lean problem path is forbidden: {raw}")
        if part.startswith("problem_icho_2026_") and part.endswith(".lean"):
            raise IsolationError(f"old IChO Lean problem path is forbidden: {raw}")
        # A plain answer data file is unsafe.  Mechanism names such as
        # answer_blind.py remain eligible and still undergo content auditing.
        if "answer" in tokens and "blind" not in tokens:
            raise IsolationError(f"answer-bearing path is forbidden: {raw}")
        if index == 0 and part == ".git":  # kept explicit for audit clarity
            raise IsolationError(f"Git metadata is forbidden: {raw}")
    return path.as_posix()


def _read_regular_file(path: Path, *, label: str, reject_symlink: bool = True) -> bytes:
    if path.is_symlink() and reject_symlink:
        raise IsolationError(f"{label} must not be a symbolic link: {path}")
    if not path.is_file():
        raise IsolationError(f"{label} is not a regular file: {path}")
    return path.read_bytes()


def _text_for_audit(data: bytes, *, location: str) -> str:
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise IsolationError(f"{location}: expected UTF-8 text") from exc


def _audit_json_bytes(data: bytes, *, location: str, jsonl: bool = False) -> int:
    text = _text_for_audit(data, location=location)
    _audit_text(text, location=location)
    count = 0
    if jsonl:
        for line_number, line in enumerate(text.splitlines(), 1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise IsolationError(f"{location}:{line_number}: invalid JSON") from exc
            if not isinstance(value, dict):
                raise IsolationError(f"{location}:{line_number}: row must be an object")
            _audit_structured(value, location=f"{location}:{line_number}")
            count += 1
        if count == 0:
            raise IsolationError(f"{location}: questions-only JSONL is empty")
        return count

    try:
        value = json.loads(text)
    except json.JSONDecodeError as exc:
        raise IsolationError(f"{location}: invalid JSON") from exc
    _audit_structured(value, location=location)
    return 1


def _blind_bundle_contract(data: bytes, *, location: str) -> BlindBundleContract:
    """Parse the already-audited bundle and bind every declared source asset.

    The caller may provide assets only when they are named and hashed by at
    least one blind row.  Conversely every asset declared by a row must cross
    the seed boundary.  This prevents an innocuously named extra image/PDF, a
    substituted page, or a silently omitted target from becoming solver input.
    """

    text = _text_for_audit(data, location=location)
    target_ids: list[str] = []
    seen_ids: set[str] = set()
    asset_hashes: dict[str, str] = {}
    asset_kinds: dict[str, str] = {}
    all_images: set[str] = set()
    all_pdfs: set[str] = set()
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:  # defensive; audited by caller
            raise IsolationError(f"{location}:{line_number}: invalid JSON") from exc
        if not isinstance(row, dict):
            raise IsolationError(f"{location}:{line_number}: row must be an object")
        target_id = row.get("id")
        if not isinstance(target_id, str) or not re.fullmatch(
            r"icho_2026_t[1-9]_a[1-9]", target_id
        ):
            raise IsolationError(f"{location}:{line_number}: invalid target id")
        if target_id in seen_ids:
            raise IsolationError(f"{location}:{line_number}: duplicate target id {target_id}")
        seen_ids.add(target_id)
        target_ids.append(target_id)
        if str(row.get("evaluation_mode", "")).replace("-", "_") != "answer_blind":
            raise IsolationError(f"{location}:{line_number}: evaluation_mode is not answer_blind")
        if row.get("official_answer_seen") is not False or row.get("phase") != "solve":
            raise IsolationError(f"{location}:{line_number}: invalid blind solve state")

        raw_assets = row.get("problem_assets")
        if not isinstance(raw_assets, list) or not raw_assets:
            raise IsolationError(f"{location}:{line_number}: problem_assets must be non-empty")
        row_images: list[str] = []
        row_pdfs: list[str] = []
        for index, raw_asset in enumerate(raw_assets):
            if not isinstance(raw_asset, dict):
                raise IsolationError(
                    f"{location}:{line_number}: problem_assets[{index}] must be an object"
                )
            source_path = _validate_relative_destination(str(raw_asset.get("path", "")))
            if len(PurePosixPath(source_path).parts) != 1:
                raise IsolationError(
                    f"{location}:{line_number}: problem asset paths must be basenames"
                )
            kind = raw_asset.get("kind")
            expected_suffixes = ALLOWED_IMAGE_SUFFIXES if kind == "problem_page" else {".pdf"}
            if kind not in {"problem_page", "problem_pdf"} or (
                PurePosixPath(source_path).suffix.casefold() not in expected_suffixes
            ):
                raise IsolationError(
                    f"{location}:{line_number}: unsupported problem asset {source_path}"
                )
            digest = raw_asset.get("sha256")
            if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                raise IsolationError(
                    f"{location}:{line_number}: invalid asset SHA-256 for {source_path}"
                )
            prior_hash = asset_hashes.setdefault(source_path, digest)
            prior_kind = asset_kinds.setdefault(source_path, str(kind))
            if prior_hash != digest or prior_kind != kind:
                raise IsolationError(
                    f"{location}:{line_number}: inconsistent asset declaration for {source_path}"
                )
            if kind == "problem_page":
                row_images.append(source_path)
                all_images.add(source_path)
            else:
                row_pdfs.append(source_path)
                all_pdfs.add(source_path)

        images = row.get("images")
        if not isinstance(images, list) or images != row_images:
            raise IsolationError(
                f"{location}:{line_number}: images must exactly match problem_page assets"
            )
        if len(row_pdfs) != 1 or row.get("source_pdf") != row_pdfs[0]:
            raise IsolationError(
                f"{location}:{line_number}: source_pdf must match one problem_pdf asset"
            )

    if not target_ids:
        raise IsolationError(f"{location}: questions-only JSONL is empty")
    if len(all_pdfs) != 1:
        raise IsolationError(f"{location}: all rows must bind the same problem PDF")
    return BlindBundleContract(
        tuple(sorted(target_ids)),
        dict(sorted(asset_hashes.items())),
        tuple(sorted(all_images)),
        next(iter(all_pdfs)),
    )


def _audit_payload_file(item: PayloadFile) -> None:
    destination = _validate_relative_destination(item.destination)
    suffix = PurePosixPath(destination).suffix.casefold()
    if suffix == ".json":
        _audit_json_bytes(item.data, location=destination)
    elif suffix == ".jsonl":
        _audit_json_bytes(item.data, location=destination, jsonl=True)
    elif suffix not in ALLOWED_IMAGE_SUFFIXES and suffix != ".pdf":
        text = _text_for_audit(item.data, location=destination)
        _audit_text(text, location=destination)


def _source_mode(path: Path) -> int:
    return 0o755 if path.stat().st_mode & stat.S_IXUSR else 0o644


def _collect_engine_tree(source_root: Path) -> list[PayloadFile]:
    engine_root = source_root / ENGINE_SOURCE_ROOT
    if engine_root.is_symlink():
        raise IsolationError(f"engine source root must not be a symlink: {engine_root}")
    if not engine_root.is_dir():
        raise IsolationError(f"missing engine source root: {engine_root}")
    boundary = engine_root.resolve()
    result: list[PayloadFile] = []

    def walk(physical: Path, relative: PurePosixPath, stack: tuple[Path, ...]) -> None:
        resolved_dir = physical.resolve()
        if resolved_dir in stack:
            raise IsolationError(f"symbolic-link cycle below {ENGINE_SOURCE_ROOT}/{relative}")
        if not _within(resolved_dir, boundary):
            raise IsolationError(
                f"engine symlink escapes allowlisted root: {ENGINE_SOURCE_ROOT}/{relative}"
            )
        next_stack = stack + (resolved_dir,)
        try:
            entries = sorted(os.scandir(physical), key=lambda entry: entry.name)
        except OSError as exc:
            raise IsolationError(f"cannot inspect engine directory: {physical}") from exc

        for entry in entries:
            name = entry.name
            child_relative = relative / name
            destination = PurePosixPath(ENGINE_SOURCE_ROOT) / child_relative
            folded = name.casefold()

            # Metadata/history carriers are violations, not ignorable caches.
            if folded in {".git", ".hg", ".svn"}:
                raise IsolationError(f"Git/VCS metadata inside engine allowlist: {destination}")
            if folded in FORBIDDEN_CREDENTIAL_NAMES or folded.startswith(".env."):
                raise IsolationError(f"credential path inside engine allowlist: {destination}")
            if folded in IGNORED_ENGINE_COMPONENTS:
                continue

            child = Path(entry.path)
            if entry.is_symlink():
                try:
                    target = child.resolve(strict=True)
                except OSError as exc:
                    raise IsolationError(f"broken engine symlink: {destination}") from exc
                if not _within(target, boundary):
                    raise IsolationError(f"engine symlink escapes allowlisted root: {destination}")
                if target.is_dir():
                    walk(target, child_relative, next_stack)
                    continue
                if not target.is_file():
                    raise IsolationError(f"engine symlink has unsupported target: {destination}")
                source_file = target
            elif entry.is_dir(follow_symlinks=False):
                walk(child, child_relative, next_stack)
                continue
            elif entry.is_file(follow_symlinks=False):
                source_file = child
            else:
                raise IsolationError(f"unsupported engine filesystem entry: {destination}")

            suffix = source_file.suffix.casefold()
            if suffix in IGNORED_ENGINE_SUFFIXES:
                continue
            if suffix not in ALLOWED_ENGINE_SUFFIXES and name not in ALLOWED_ENGINE_BASENAMES:
                raise IsolationError(f"unallowlisted engine file type: {destination}")
            normalized_destination = _validate_relative_destination(destination.as_posix())
            item = PayloadFile(
                normalized_destination,
                _read_regular_file(source_file, label="engine file", reject_symlink=False),
                _source_mode(source_file),
                "engine",
            )
            _audit_payload_file(item)
            result.append(item)

    walk(engine_root, PurePosixPath(), ())
    if not result:
        raise IsolationError("engine allowlist selected no files")
    return result


def _collect_named_file(
    source: Path,
    destination: str,
    *,
    group: str,
    required: bool = True,
) -> PayloadFile | None:
    if not source.exists() and not source.is_symlink():
        if required:
            raise IsolationError(f"missing required {group} file: {source}")
        return None
    data = _read_regular_file(source, label=f"{group} file")
    item = PayloadFile(
        _validate_relative_destination(destination),
        data,
        _source_mode(source),
        group,
    )
    _audit_payload_file(item)
    return item


def _audit_lake_contract(item: PayloadFile) -> None:
    """Enforce the non-transitive portion of the Lake allowlist."""

    if item.destination != "IChO2026Chem.lean":
        return
    text = _text_for_audit(item.data, location=item.destination)
    imports = {
        line.split(maxsplit=1)[1].strip()
        for line in text.splitlines()
        if line.strip().startswith("import ") and len(line.split(maxsplit=1)) == 2
    }
    expected = {"IChO2026Chem.Core", "IChO2026Chem.Reporting"}
    if imports != expected:
        raise IsolationError(
            "IChO2026Chem.lean must import exactly Core and Reporting; "
            "Kinetics and other prior-run modules are forbidden"
        )


def _resolve_source_commit(source_root: Path, explicit: str | None) -> str:
    if explicit is not None:
        commit = explicit.strip().casefold()
    else:
        try:
            completed = subprocess.run(
                ["git", "-C", str(source_root), "rev-parse", "--verify", "HEAD^{commit}"],
                check=True,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.CalledProcessError) as exc:
            raise IsolationError(
                "source tree has no readable Git commit; pass --source-commit explicitly"
            ) from exc
        commit = completed.stdout.strip().casefold()
    if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit):
        raise IsolationError(f"invalid source commit id: {commit!r}")
    return commit


def _collect_problem_materials(
    *,
    questions_only: Path,
    problem_pdf: Path,
    image_root: Path,
    problem_images: Sequence[str | Path],
) -> tuple[list[PayloadFile], BlindBundleContract]:
    bundle_data = _read_regular_file(questions_only, label="questions-only bundle")
    _audit_json_bytes(
        bundle_data,
        location=BUNDLE_DESTINATION,
        jsonl=True,
    )
    contract = _blind_bundle_contract(bundle_data, location=BUNDLE_DESTINATION)
    bundle = PayloadFile(BUNDLE_DESTINATION, bundle_data, 0o644, "blind_bundle")

    if problem_pdf.suffix.casefold() != ".pdf":
        raise IsolationError(f"problem PDF must have a .pdf suffix: {problem_pdf}")
    if problem_pdf.is_symlink():
        raise IsolationError(f"problem PDF must not be a symbolic link: {problem_pdf}")
    _validate_relative_destination(problem_pdf.name)
    pdf_destination = f"{PDF_DESTINATION_ROOT}/{problem_pdf.name}"
    if problem_pdf.name != contract.pdf_path:
        raise IsolationError(
            "--problem-pdf must be the exact PDF declared by every blind row"
        )
    pdf_data = _read_regular_file(problem_pdf, label="problem PDF")
    if _sha256(pdf_data) != contract.asset_hashes[contract.pdf_path]:
        raise IsolationError("problem PDF hash does not match the blind bundle")
    pdf = PayloadFile(
        _validate_relative_destination(pdf_destination),
        pdf_data,
        0o644,
        "asset",
    )

    root = _require_plain_directory(image_root, label="problem image root")
    requested_images = tuple(
        sorted(_validate_relative_destination(Path(raw).as_posix()) for raw in problem_images)
    )
    if requested_images != contract.image_paths:
        missing = sorted(set(contract.image_paths) - set(requested_images))
        extra = sorted(set(requested_images) - set(contract.image_paths))
        raise IsolationError(
            f"problem image list does not match blind bundle (missing={missing}, extra={extra})"
        )
    images: list[PayloadFile] = []
    seen_relative: set[str] = set()
    for raw_image in problem_images:
        candidate = Path(raw_image)
        source = candidate if candidate.is_absolute() else image_root / candidate
        if source.is_symlink():
            raise IsolationError(f"problem image must not be a symbolic link: {source}")
        resolved = source.resolve()
        if not _within(resolved, root):
            raise IsolationError(f"problem image escapes image root: {raw_image}")
        relative = resolved.relative_to(root).as_posix()
        if relative in seen_relative:
            raise IsolationError(f"duplicate problem image: {relative}")
        seen_relative.add(relative)
        if resolved.suffix.casefold() not in ALLOWED_IMAGE_SUFFIXES:
            raise IsolationError(f"unsupported problem image type: {relative}")
        destination = _validate_relative_destination(
            f"{IMAGE_DESTINATION_ROOT}/{relative}"
        )
        image_data = _read_regular_file(resolved, label="problem image")
        if _sha256(image_data) != contract.asset_hashes[relative]:
            raise IsolationError(
                f"problem image hash does not match blind bundle: {relative}"
            )
        images.append(
            PayloadFile(
                destination,
                image_data,
                0o644,
                "asset",
            )
        )

    return [bundle, pdf, *images], contract


def _build_payload(
    *,
    source_root: Path,
    lake_root: Path,
    questions_only: Path,
    problem_pdf: Path,
    image_root: Path,
    problem_images: Sequence[str | Path],
) -> tuple[list[PayloadFile], BlindBundleContract]:
    source = _require_plain_directory(source_root, label="source root")
    lake = _require_plain_directory(lake_root, label="Lake skeleton root")
    payload: list[PayloadFile] = []

    # Do not copy ``source``.  Runtime installation and its full inventory are
    # controller responsibilities; including a second, solver-writable Archon
    # checkout would create a confusing executable/source split and expose
    # freeze/grader implementation details for no functional benefit.

    for relative in REQUIRED_LAKE_FILES:
        item = _collect_named_file(
            lake / Path(relative), relative, group="lake_skeleton", required=True
        )
        assert item is not None
        _audit_lake_contract(item)
        payload.append(item)
    for relative in OPTIONAL_LAKE_FILES:
        item = _collect_named_file(
            lake / Path(relative), relative, group="lake_skeleton", required=False
        )
        if item is not None:
            _audit_lake_contract(item)
            payload.append(item)
    for relative, data in sorted(GENERATED_LAKE_FILES.items()):
        item = PayloadFile(
            _validate_relative_destination(relative), data, 0o644, "lake_skeleton"
        )
        _audit_payload_file(item)
        payload.append(item)

    materials, contract = _collect_problem_materials(
        questions_only=questions_only,
        problem_pdf=problem_pdf,
        image_root=image_root,
        problem_images=problem_images,
    )
    payload.extend(materials)

    destinations: set[str] = set()
    for item in payload:
        if item.destination in destinations:
            raise IsolationError(f"duplicate seed destination: {item.destination}")
        destinations.add(item.destination)
        _audit_payload_file(item)
    return sorted(payload, key=lambda item: item.destination), contract


def _manifest_for(
    payload: Sequence[PayloadFile], *, contract: BlindBundleContract
) -> dict[str, Any]:
    by_group: dict[str, dict[str, str]] = {
        "engine": {},
        "lake_skeleton": {},
        "asset": {},
    }
    payload_index: dict[str, str] = {}
    bundle_item: PayloadFile | None = None
    for item in payload:
        digest = _sha256(item.data)
        payload_index[item.destination] = digest
        if item.group == "blind_bundle":
            bundle_item = item
        else:
            by_group[item.group][item.destination] = digest
    if bundle_item is None:
        raise IsolationError("internal error: blind bundle missing from seed plan")

    assets = dict(sorted(by_group["asset"].items()))
    engine_files = dict(sorted(by_group["engine"].items()))
    lake_files = dict(sorted(by_group["lake_skeleton"].items()))
    bundle_digest = _sha256(bundle_item.data)
    manifest: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        # The exact source revision remains in the controller-side build
        # receipt.  It is deliberately not disclosed to a network-capable
        # solver because it can be used to locate answer-bearing Git history.
        "source_revision_disclosed": False,
        "engine_files": engine_files,
        "engine_files_sha256": _hash_index(engine_files),
        "lake_skeleton_files": lake_files,
        "lake_skeleton_sha256": _hash_index(lake_files),
        "blind_bundle": {
            "path": bundle_item.destination,
            "row_count": len(contract.target_ids),
            "sha256": bundle_digest,
            "size": len(bundle_item.data),
        },
        "blind_bundle_sha256": bundle_digest,
        "target_ids": list(contract.target_ids),
        "target_ids_sha256": _sha256(_canonical_json_bytes(list(contract.target_ids))),
        "assets": assets,
        "assets_sha256": _hash_index(assets),
        "payload_files": dict(sorted(payload_index.items())),
        "payload_sha256": _hash_index(payload_index),
        "isolation_claims": {
            "filesystem": True,
            "network": False,
        },
        "workspace_policy": {
            "fresh_git_init": True,
            "history": False,
            "remotes": [],
            "solver_labels": ["GPT", "K3"],
        },
    }
    _audit_structured(manifest, location="manifest")
    return manifest


def _ensure_new_destination(path: Path, *, label: str) -> None:
    if path.exists() or path.is_symlink():
        raise IsolationError(f"{label} must be a new path: {path}")
    parent = path.parent.resolve()
    if not parent.is_dir():
        raise IsolationError(f"parent directory does not exist for {label}: {path.parent}")


def _write_payload_atomic(
    destination: Path,
    payload: Sequence[PayloadFile],
    manifest: Mapping[str, Any],
) -> None:
    _ensure_new_destination(destination, label="seed output")
    parent = destination.parent.resolve()
    staging = Path(tempfile.mkdtemp(prefix=f".{destination.name}.staging-", dir=parent))
    try:
        for item in payload:
            target = staging / Path(*PurePosixPath(item.destination).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(item.data)
            target.chmod(item.mode)
        manifest_path = staging / MANIFEST_NAME
        manifest_path.write_bytes(_pretty_json_bytes(manifest))
        manifest_path.chmod(0o644)
        validate_seed(staging)
        os.replace(staging, destination)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def build_seed(
    *,
    source_root: Path,
    questions_only: Path,
    problem_pdf: Path,
    image_root: Path,
    problem_images: Sequence[str | Path],
    output_dir: Path | None = None,
    lake_root: Path | None = None,
    source_commit: str | None = None,
    dry_run: bool = False,
    gpt_workspace: Path | None = None,
    k3_workspace: Path | None = None,
) -> dict[str, Any]:
    """Validate inputs and optionally materialize a new solver seed.

    ``dry_run=True`` performs the complete in-memory projection and audit but
    makes no directories and runs no ``git init``.  The returned manifest is
    exactly the one a non-dry build of the same bytes would write.
    """

    source = _require_plain_directory(Path(source_root), label="source root")
    lake = Path(lake_root) if lake_root is not None else source / "icho_2026_run"
    # Validate controller provenance when supplied (or when the source is a
    # Git checkout), but never serialize the resolvable revision into the
    # solver-visible seed manifest.
    _resolve_source_commit(source, source_commit)
    payload, contract = _build_payload(
        source_root=source,
        lake_root=lake,
        questions_only=Path(questions_only),
        problem_pdf=Path(problem_pdf),
        image_root=Path(image_root),
        problem_images=problem_images,
    )
    manifest = _manifest_for(payload, contract=contract)

    if dry_run:
        return manifest
    if output_dir is None:
        raise IsolationError("output_dir is required unless dry_run=True")

    destination = Path(output_dir)
    workspace_destinations = [
        Path(path) for path in (gpt_workspace, k3_workspace) if path is not None
    ]
    all_destinations = [destination, *workspace_destinations]
    resolved_destinations = [path.resolve() for path in all_destinations]
    if len(set(resolved_destinations)) != len(resolved_destinations):
        raise IsolationError("seed, GPT, and K3 output paths must be distinct")
    _ensure_new_destination(destination, label="seed output")
    for workspace in workspace_destinations:
        _ensure_new_destination(workspace, label="solver workspace")
    _write_payload_atomic(destination, payload, manifest)
    if gpt_workspace is not None:
        copy_seed_to_workspace(destination, Path(gpt_workspace), label="GPT")
    if k3_workspace is not None:
        copy_seed_to_workspace(destination, Path(k3_workspace), label="K3")
    return manifest


def build_solver_seed(**kwargs: Any) -> dict[str, Any]:
    """Descriptive alias retained for trusted-controller callers."""

    return build_seed(**kwargs)


def build_answer_blind_solver_seed(**kwargs: Any) -> dict[str, Any]:
    """Alias matching the script name for import-based callers."""

    return build_seed(**kwargs)


def _regular_files_below(root: Path) -> list[Path]:
    files: list[Path] = []

    def walk(directory: Path) -> None:
        for entry in sorted(os.scandir(directory), key=lambda candidate: candidate.name):
            path = Path(entry.path)
            relative = path.relative_to(root).as_posix()
            _validate_relative_destination(relative)
            if entry.is_symlink():
                raise IsolationError(f"seed contains symbolic link: {relative}")
            if entry.is_dir(follow_symlinks=False):
                walk(path)
            elif entry.is_file(follow_symlinks=False):
                files.append(path)
            else:
                raise IsolationError(f"seed contains unsupported filesystem entry: {relative}")

    walk(root)
    return files


def _hash_map(value: object, *, field: str) -> dict[str, str]:
    if not isinstance(value, dict):
        raise IsolationError(f"manifest.{field} must be an object")
    result: dict[str, str] = {}
    for raw_path, raw_hash in value.items():
        path = _validate_relative_destination(str(raw_path))
        digest = str(raw_hash)
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise IsolationError(f"manifest.{field}[{path!r}] is not a SHA-256")
        result[path] = digest
    return result


def validate_seed(seed_root: Path) -> dict[str, Any]:
    """Recursively verify a materialized seed and its isolation manifest."""

    root = _require_plain_directory(Path(seed_root), label="seed root")
    manifest_path = root / MANIFEST_NAME
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise IsolationError(f"seed is missing {MANIFEST_NAME}")
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise IsolationError("invalid isolation manifest") from exc
    if not isinstance(manifest, dict):
        raise IsolationError("isolation manifest must be an object")
    _audit_structured(manifest, location="manifest")
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("protocol") != PROTOCOL:
        raise IsolationError("unsupported isolation manifest schema/protocol")
    if manifest.get("source_revision_disclosed") is not False or "source_commit" in manifest:
        raise IsolationError("manifest must not disclose a resolvable source revision")
    if manifest.get("isolation_claims") != {"filesystem": True, "network": False}:
        raise IsolationError("manifest isolation claims are not fail-closed")
    expected_workspace_policy = {
        "fresh_git_init": True,
        "history": False,
        "remotes": [],
        "solver_labels": ["GPT", "K3"],
    }
    if manifest.get("workspace_policy") != expected_workspace_policy:
        raise IsolationError("manifest workspace policy is invalid")

    engine = _hash_map(manifest.get("engine_files"), field="engine_files")
    lake = _hash_map(
        manifest.get("lake_skeleton_files"), field="lake_skeleton_files"
    )
    assets = _hash_map(manifest.get("assets"), field="assets")
    payload = _hash_map(manifest.get("payload_files"), field="payload_files")
    if engine:
        raise IsolationError("solver seed must not contain editable Archon engine files")
    required_lake = set(REQUIRED_LAKE_FILES).union(GENERATED_LAKE_FILES)
    if not required_lake.issubset(lake):
        raise IsolationError("manifest omits required Lake skeleton files")
    if not any(
        path.startswith(f"{IMAGE_DESTINATION_ROOT}/") for path in assets
    ) or not any(path.startswith(f"{PDF_DESTINATION_ROOT}/") for path in assets):
        raise IsolationError("manifest must include a problem image and problem PDF")
    if manifest.get("engine_files_sha256") != _hash_index(engine):
        raise IsolationError("engine file index hash mismatch")
    if manifest.get("lake_skeleton_sha256") != _hash_index(lake):
        raise IsolationError("Lake skeleton index hash mismatch")
    if manifest.get("assets_sha256") != _hash_index(assets):
        raise IsolationError("asset index hash mismatch")
    if manifest.get("payload_sha256") != _hash_index(payload):
        raise IsolationError("payload index hash mismatch")

    bundle = manifest.get("blind_bundle")
    if not isinstance(bundle, dict):
        raise IsolationError("manifest.blind_bundle must be an object")
    bundle_path = _validate_relative_destination(str(bundle.get("path", "")))
    bundle_hash = str(bundle.get("sha256", ""))
    if bundle_path != BUNDLE_DESTINATION:
        raise IsolationError("unexpected blind bundle destination")
    if manifest.get("blind_bundle_sha256") != bundle_hash:
        raise IsolationError("blind bundle hash fields disagree")

    combined = dict(engine)
    for hash_group in (lake, assets, {bundle_path: bundle_hash}):
        overlap = set(combined).intersection(hash_group)
        if overlap:
            raise IsolationError(f"manifest file groups overlap: {sorted(overlap)}")
        combined.update(hash_group)
    if combined != payload:
        raise IsolationError("manifest payload inventory does not match file groups")

    actual_files = _regular_files_below(root)
    actual_relative = {
        path.relative_to(root).as_posix() for path in actual_files if path != manifest_path
    }
    if actual_relative != set(payload):
        missing = sorted(set(payload) - actual_relative)
        extra = sorted(actual_relative - set(payload))
        raise IsolationError(f"seed inventory mismatch (missing={missing}, extra={extra})")

    for path in actual_files:
        if path == manifest_path:
            continue
        relative = path.relative_to(root).as_posix()
        data = path.read_bytes()
        if _sha256(data) != payload[relative]:
            raise IsolationError(f"seed file hash mismatch: {relative}")
        group = (
            "blind_bundle"
            if relative == bundle_path
            else "asset"
            if relative in assets
            else "lake_skeleton"
            if relative in lake
            else "engine"
        )
        item = PayloadFile(relative, data, 0o644, group)
        _audit_payload_file(item)
        if group == "lake_skeleton":
            _audit_lake_contract(item)
        if relative in GENERATED_LAKE_FILES and data != GENERATED_LAKE_FILES[relative]:
            raise IsolationError(f"trusted generated Lake entry point was modified: {relative}")

    bundle_file = root / Path(*PurePosixPath(bundle_path).parts)
    rows = _audit_json_bytes(
        bundle_file.read_bytes(), location=bundle_path, jsonl=True
    )
    contract = _blind_bundle_contract(bundle_file.read_bytes(), location=bundle_path)
    if bundle.get("row_count") != rows or bundle.get("size") != bundle_file.stat().st_size:
        raise IsolationError("blind bundle manifest metadata mismatch")
    if manifest.get("target_ids") != list(contract.target_ids):
        raise IsolationError("manifest target_ids do not match blind bundle")
    if manifest.get("target_ids_sha256") != _sha256(
        _canonical_json_bytes(list(contract.target_ids))
    ):
        raise IsolationError("manifest target_ids hash mismatch")
    expected_asset_destinations = {
        f"{PDF_DESTINATION_ROOT}/{contract.pdf_path}": contract.asset_hashes[
            contract.pdf_path
        ],
        **{
            f"{IMAGE_DESTINATION_ROOT}/{path}": contract.asset_hashes[path]
            for path in contract.image_paths
        },
    }
    if assets != dict(sorted(expected_asset_destinations.items())):
        raise IsolationError("manifest assets do not exactly match blind bundle declarations")
    return manifest


def _run_git(arguments: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    for name in (
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_COMMON_DIR",
        "GIT_CONFIG_COUNT",
        "GIT_DIR",
        "GIT_INDEX_FILE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_TEMPLATE_DIR",
        "GIT_WORK_TREE",
    ):
        environment.pop(name, None)
    for name in list(environment):
        if re.fullmatch(r"GIT_CONFIG_(?:KEY|VALUE)_\d+", name):
            environment.pop(name, None)
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    environment["GIT_CONFIG_GLOBAL"] = os.devnull
    return subprocess.run(
        ["git", *arguments],
        cwd=cwd,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )


def copy_seed_to_workspace(seed_root: Path, destination: Path, *, label: str) -> None:
    """Create one independent, history-free Git workspace from a valid seed."""

    seed = _require_plain_directory(Path(seed_root), label="seed root")
    validate_seed(seed)
    target = Path(destination)
    _ensure_new_destination(target, label=f"{label} workspace")
    parent = target.parent.resolve()
    staging = Path(tempfile.mkdtemp(prefix=f".{target.name}.staging-", dir=parent))
    # copytree requires a nonexistent destination, so use a child of the
    # controller-created staging directory.
    candidate = staging / "workspace"
    try:
        shutil.copytree(seed, candidate, symlinks=True)
        validate_seed(candidate)
        _run_git(["init", "--quiet", "--initial-branch=main", "--template="], cwd=candidate)
        if _run_git(["remote"], cwd=candidate).stdout.strip():
            raise IsolationError(f"{label} workspace unexpectedly has a Git remote")
        if _run_git(["rev-list", "--all"], cwd=candidate).stdout.strip():
            raise IsolationError(f"{label} workspace unexpectedly has Git history")
        os.replace(candidate, target)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    else:
        shutil.rmtree(staging, ignore_errors=True)


def copy_seed_for_gpt_and_k3(
    seed_root: Path, *, gpt_workspace: Path, k3_workspace: Path
) -> None:
    """Make independent GPT and K3 repositories from one validated seed."""

    if Path(gpt_workspace).resolve() == Path(k3_workspace).resolve():
        raise IsolationError("GPT and K3 workspace paths must be distinct")
    _ensure_new_destination(Path(gpt_workspace), label="GPT workspace")
    _ensure_new_destination(Path(k3_workspace), label="K3 workspace")
    copy_seed_to_workspace(seed_root, Path(gpt_workspace), label="GPT")
    copy_seed_to_workspace(seed_root, Path(k3_workspace), label="K3")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", "--source-tree", dest="source_root", type=Path)
    parser.add_argument("--lake-root", "--lake-skeleton", dest="lake_root", type=Path)
    parser.add_argument(
        "--questions-only", "--blind-bundle", dest="questions_only", type=Path
    )
    parser.add_argument("--problem-pdf", type=Path)
    parser.add_argument("--image-root", type=Path)
    parser.add_argument("--problem-image", action="append", default=[])
    parser.add_argument("--output", "--seed-output", dest="output_dir", type=Path)
    parser.add_argument("--gpt-workspace", "--gpt-output", dest="gpt_workspace", type=Path)
    parser.add_argument("--k3-workspace", "--k3-output", dest="k3_workspace", type=Path)
    parser.add_argument("--source-commit")
    parser.add_argument("--dry-run", "--validate-only", dest="dry_run", action="store_true")
    parser.add_argument("--validate-seed", type=Path)
    return parser


def _required_argument(parser: argparse.ArgumentParser, value: Any, flag: str) -> Any:
    if value is None:
        parser.error(f"{flag} is required in build mode")
    return value


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    if args.validate_seed is not None:
        manifest = validate_seed(args.validate_seed)
    else:
        source_root = _required_argument(parser, args.source_root, "--source-root")
        questions_only = _required_argument(
            parser, args.questions_only, "--questions-only"
        )
        problem_pdf = _required_argument(parser, args.problem_pdf, "--problem-pdf")
        image_root = _required_argument(parser, args.image_root, "--image-root")
        if not args.problem_image:
            parser.error("at least one --problem-image is required in build mode")
        if not args.dry_run and args.output_dir is None:
            parser.error("--output is required unless --dry-run is used")
        manifest = build_seed(
            source_root=source_root,
            lake_root=args.lake_root,
            questions_only=questions_only,
            problem_pdf=problem_pdf,
            image_root=image_root,
            problem_images=args.problem_image,
            output_dir=args.output_dir,
            source_commit=args.source_commit,
            dry_run=args.dry_run,
            gpt_workspace=args.gpt_workspace,
            k3_workspace=args.k3_workspace,
        )
    print(json.dumps(manifest, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
