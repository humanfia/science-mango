#!/usr/bin/env python3
"""Run a fresh, singleton GPT answer-blind campaign.

This controller deliberately composes the existing production entry points.  It
does not import or weaken their validation logic.  Every item receives a new
workspace containing the full 32-row questions-only bundle and exactly one
source report, then follows this irreversible sequence::

    source-first -> structured solver -> artifact-submit -> clean snapshot
    -> low-UID verifier -> artifact-finalize -> pilot seal -> freeze

The default mode executes all 32 items.  A sealed, terminal parent campaign
may authorize a fresh failed-subset retry, but there is still no resume mode:
the new campaign root and every per-item workspace/controller/snapshot must be
absent.  Failed trees are retained as evidence and never become retry inputs.
"""

from __future__ import annotations

import argparse
import asyncio
import contextlib
import dataclasses
import datetime as dt
import fcntl
import hashlib
import json
import os
import pwd
import re
import signal
import stat
import sys
import time
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, NoReturn, Sequence


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-gpt-campaign-v1"
BLIND_PROTOCOL = "icho-answer-blind-v1"
VARIANT = "gpt"
MODEL_FAMILY = "openai"
MODEL_ID = "gpt-5.6-sol"
EXPECTED_ITEM_COUNT = 32
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
SAFE_CAMPAIGN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
SOURCE_REPORT_FIELDS = (
    "id",
    "current_question",
    "shared_context",
    "previous_parts",
    "images",
    "problem_assets",
    "requested_outputs",
    "reporting_policy",
    "measurement_policy",
    "candidate_domain_policy",
)
SOURCE_REPORT_TOP_FIELDS = {
    "schema_version",
    "command",
    "domain",
    "proof_mode",
    "prover_mode",
    "path_base",
    "project_path",
    "source_report",
    "output_lean",
    "problem_id",
    "part_id",
    "previous_parts",
    "lean_search_packages",
    "status",
    "next_stage",
    "evaluation_mode",
    "official_answer_seen",
    "phase",
    "blind_record_sha256",
    "entry",
}
DEFAULT_VERIFIER_USERS = (
    "ichoblindgptv",
    "ichoblindgptv2",
    "ichoblindgptv3",
    "ichoblindgptv4",
)
DEFAULT_VERIFIER_SCRATCH_ROOTS = tuple(
    Path(f"/srv/icho-answer-blind-gpt-verifier-lane-{index}")
    for index in range(1, 5)
)
DEFAULT_SINGLETON_LOCK = Path("/run/icho-answer-blind-gpt-full32-campaign.lock")
RUNTIME_ORCHESTRATOR = PurePosixPath("libexec/run_answer_blind_gpt_campaign.py")
STAGES = (
    "source-first",
    "solver",
    "artifact-submit",
    "snapshot",
    "verifier",
    "artifact-finalize",
    "seal-pilot",
    "freeze",
)
FORBIDDEN_RUNTIME_CACHE_DIRS = {
    "__pycache__",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
}
FORBIDDEN_RUNTIME_CACHE_SUFFIXES = {".pyc", ".pyo"}
FORBIDDEN_SOLVER_KEY_FRAGMENTS = (
    "answer",
    "solution",
    "marking",
    "rubric",
    "explanation",
    "reasoning",
    "reusable_conclusion",
    "grader",
)
MAX_INVENTORY_FILES = 250_000
MAX_INVENTORY_TOTAL_BYTES = 32 * 1024 * 1024 * 1024
MAX_PARENT_INDEX_BYTES = 64 * 1024 * 1024


class CampaignError(RuntimeError):
    """A fail-closed campaign configuration or execution error."""


class StageError(CampaignError):
    def __init__(self, stage: str, message: str) -> None:
        super().__init__(message)
        self.stage = stage


def _fail(message: str) -> NoReturn:
    raise CampaignError(message)


def _utcnow() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _json_bytes(value: Any, *, pretty: bool = False) -> bytes:
    if pretty:
        rendered = json.dumps(
            value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False
        )
    else:
        rendered = json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    return (rendered + "\n").encode("utf-8")


def _sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _file_sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hash_index(index: Mapping[str, str]) -> str:
    return _sha(_json_bytes(dict(sorted(index.items()))))


def _safe_absolute(raw: Path, *, label: str) -> Path:
    if not raw.is_absolute():
        _fail(f"{label} must be an absolute path: {raw}")
    lexical = Path(os.path.abspath(raw))
    cursor = Path(lexical.anchor)
    for part in lexical.parts[1:]:
        cursor /= part
        if cursor.is_symlink():
            _fail(f"{label} may not traverse a symlink: {cursor}")
    return lexical.resolve(strict=False)


def _require_root_directory(
    path: Path,
    *,
    label: str,
    traversable: bool = False,
    empty: bool = False,
) -> Path:
    resolved = _safe_absolute(path, label=label)
    if resolved.is_symlink() or not resolved.is_dir():
        _fail(f"{label} must be a regular directory: {resolved}")
    metadata = resolved.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or metadata.st_mode & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable: {resolved}")
    if traversable and metadata.st_mode & 0o005 != 0o005:
        _fail(f"{label} must be group/other traversable: {resolved}")
    if empty and next(resolved.iterdir(), None) is not None:
        _fail(f"{label} must be empty before the campaign: {resolved}")
    return resolved


def _require_root_file(path: Path, *, label: str, executable: bool = False) -> Path:
    resolved = _safe_absolute(path, label=label)
    if resolved.is_symlink() or not resolved.is_file():
        _fail(f"{label} must be a regular file: {resolved}")
    metadata = resolved.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or metadata.st_mode & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable: {resolved}")
    if executable and metadata.st_mode & 0o111 == 0:
        _fail(f"{label} must be executable: {resolved}")
    return resolved


def _require_disjoint(paths: Mapping[str, Path]) -> None:
    values = list(paths.items())
    for index, (left_label, left) in enumerate(values):
        for right_label, right in values[index + 1 :]:
            if left == right or left.is_relative_to(right) or right.is_relative_to(left):
                _fail(
                    f"campaign roots must be disjoint: {left_label}={left}, "
                    f"{right_label}={right}"
                )


def _controller_inventory(
    root: Path, *, label: str, exclude_roots: Sequence[Path] = ()
) -> dict[str, str]:
    """Mirror the production root inventory, including safe in-tree links."""
    root = _require_root_directory(root, label=label)
    exclusions = tuple(path.resolve() for path in exclude_roots)
    inventory: dict[str, str] = {}
    total_bytes = 0

    def account(size: int) -> None:
        nonlocal total_bytes
        if len(inventory) >= MAX_INVENTORY_FILES:
            _fail(f"{label} exceeds the file-count safety limit")
        total_bytes += size
        if total_bytes > MAX_INVENTORY_TOTAL_BYTES:
            _fail(f"{label} exceeds the total-byte safety limit")

    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(root).as_posix()
            resolved = child.resolve(strict=True)
            if resolved in exclusions:
                continue
            if child.is_symlink():
                try:
                    resolved.relative_to(root)
                except ValueError:
                    _fail(f"{label} contains an escaping directory symlink: {relative}")
                if not resolved.is_dir() or child.lstat().st_uid != 0:
                    _fail(f"{label} contains an unsafe directory symlink: {relative}")
                target = os.readlink(child).encode("utf-8")
                account(len(target))
                inventory[relative] = _sha(b"symlink\0" + target)
                continue
            metadata = child.stat(follow_symlinks=False)
            if not child.is_dir() or metadata.st_uid != 0 or metadata.st_mode & 0o022:
                _fail(f"{label} contains an unsafe directory: {relative}")
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            child = base / name
            relative = child.relative_to(root).as_posix()
            if child.is_symlink():
                resolved = child.resolve(strict=True)
                try:
                    resolved.relative_to(root)
                except ValueError:
                    _fail(f"{label} contains an escaping file symlink: {relative}")
                if not resolved.is_file() or child.lstat().st_uid != 0:
                    _fail(f"{label} contains an unsafe file symlink: {relative}")
                target = os.readlink(child).encode("utf-8")
                account(len(target))
                inventory[relative] = _sha(b"symlink\0" + target)
                continue
            metadata = child.stat(follow_symlinks=False)
            if (
                not stat.S_ISREG(metadata.st_mode)
                or metadata.st_uid != 0
                or metadata.st_mode & 0o022
            ):
                _fail(f"{label} contains an unsafe file: {relative}")
            account(metadata.st_size)
            inventory[relative] = _file_sha(child)
    if not inventory:
        _fail(f"{label} contains no files")
    return dict(sorted(inventory.items()))


def _assert_runtime_cache_free(runtime: Path) -> None:
    """Reject generated Python/tool caches in the sealed runtime tree."""
    offenders: list[str] = []
    for directory, names, files in os.walk(runtime, topdown=True, followlinks=False):
        base = Path(directory)
        for name in names:
            child = base / name
            if name in FORBIDDEN_RUNTIME_CACHE_DIRS:
                offenders.append(child.relative_to(runtime).as_posix())
        for name in files:
            child = base / name
            if child.suffix in FORBIDDEN_RUNTIME_CACHE_SUFFIXES:
                offenders.append(child.relative_to(runtime).as_posix())
        if len(offenders) > 20:
            break
    if offenders:
        _fail(
            "sealed runtime contains generated cache entries: "
            + ", ".join(sorted(offenders)[:20])
        )


def _plain_seed_inventory(root: Path) -> dict[str, str]:
    """Inventory a copy seed while forbidding every symlink and special entry."""
    root = _require_root_directory(root, label="prepared full32 seed")
    inventory: dict[str, str] = {}
    total_bytes = 0
    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(root).as_posix()
            metadata = child.lstat()
            if (
                child.is_symlink()
                or not stat.S_ISDIR(metadata.st_mode)
                or metadata.st_uid != 0
                or metadata.st_mode & 0o022
            ):
                _fail(f"prepared full32 seed contains unsafe directory: {relative}")
        for name in sorted(files):
            child = base / name
            relative = child.relative_to(root).as_posix()
            metadata = child.lstat()
            if (
                child.is_symlink()
                or not stat.S_ISREG(metadata.st_mode)
                or metadata.st_uid != 0
                or metadata.st_mode & 0o022
            ):
                _fail(f"prepared full32 seed contains unsafe file: {relative}")
            if len(inventory) >= MAX_INVENTORY_FILES:
                _fail("prepared full32 seed exceeds the file-count safety limit")
            total_bytes += metadata.st_size
            if total_bytes > MAX_INVENTORY_TOTAL_BYTES:
                _fail("prepared full32 seed exceeds the total-byte safety limit")
            inventory[relative] = _file_sha(child)
    if not inventory:
        _fail("prepared full32 seed is empty")
    return dict(sorted(inventory.items()))


def _strict_json(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError(f"{label} is invalid JSON: {exc}") from exc
    if not isinstance(value, dict):
        _fail(f"{label} must contain one JSON object")
    return value


def _assert_solver_safe(value: Any, *, path: str) -> None:
    """Reject answer-key fields and solution-asset locators recursively."""
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key)
            lowered = key.lower()
            child_path = f"{path}.{key}"
            if lowered == "official_answer_seen":
                if child is not False:
                    _fail(f"answer-blind integrity flag must be false at {child_path}")
                continue
            if any(fragment in lowered for fragment in FORBIDDEN_SOLVER_KEY_FRAGMENTS):
                _fail(f"forbidden solver key at {child_path}")
            _assert_solver_safe(child, path=child_path)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _assert_solver_safe(child, path=f"{path}[{index}]")
    elif isinstance(value, str):
        normalized = value.lower().replace("\\", "/")
        if (
            "theory_solution" in normalized
            or "_answer_page-" in normalized
            or normalized.endswith("/solution.pdf")
        ):
            _fail(f"forbidden solution asset reference at {path}")


def _bundle_rows(bundle: Path) -> tuple[bytes, dict[str, dict[str, Any]]]:
    payload = bundle.read_bytes()
    rows: dict[str, dict[str, Any]] = {}
    nonempty_lines = [line for line in payload.decode("utf-8").splitlines() if line.strip()]
    if len(nonempty_lines) != EXPECTED_ITEM_COUNT:
        _fail(
            f"GPT full campaign requires exactly {EXPECTED_ITEM_COUNT} bundle rows; "
            f"found {len(nonempty_lines)}"
        )
    for line_number, line in enumerate(nonempty_lines, start=1):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise CampaignError(f"invalid bundle row {line_number}: {exc}") from exc
        if not isinstance(row, dict):
            _fail(f"bundle row {line_number} must be an object")
        record_id = row.get("id")
        if not isinstance(record_id, str) or SAFE_ID.fullmatch(record_id) is None:
            _fail(f"bundle row {line_number} has unsafe id")
        if record_id in rows:
            _fail(f"bundle contains duplicate id: {record_id}")
        if (
            row.get("evaluation_mode") != "answer_blind"
            or row.get("official_answer_seen") is not False
        ):
            _fail(f"bundle row {record_id} is not answer-blind")
        if (
            row.get("schema_version") != 1
            or row.get("protocol") != BLIND_PROTOCOL
            or row.get("phase") != "solve"
        ):
            _fail(f"bundle row {record_id} has stale answer-blind protocol metadata")
        _assert_solver_safe(row, path=f"bundle[{record_id}]")
        rows[record_id] = row
    return payload, rows


def _canonical_sha(value: Any) -> str:
    return _sha(_json_bytes(value))


def _source_reports(
    seed: Path, rows: Mapping[str, Mapping[str, Any]]
) -> dict[str, tuple[PurePosixPath, str]]:
    root = seed / "reports"
    if root.is_symlink() or not root.is_dir():
        _fail("prepared full32 seed has no plain reports directory")
    reports: dict[str, tuple[PurePosixPath, str]] = {}
    regular_files: set[Path] = set()
    for path in sorted(root.rglob("*")):
        if path.is_dir() and not path.is_symlink():
            continue
        if path.is_symlink() or not path.is_file():
            _fail(f"prepared reports tree contains unsafe entry: {path}")
        regular_files.add(path)
        if not path.name.endswith(".source.json"):
            _fail(f"prepared reports tree contains non-source-report file: {path}")
        payload = path.read_bytes()
        report = _strict_json(payload, label=f"source report {path}")
        if set(report) != SOURCE_REPORT_TOP_FIELDS:
            _fail(f"source report has non-canonical top-level schema: {path}")
        entry = report.get("entry")
        record_id = entry.get("id") if isinstance(entry, Mapping) else None
        if record_id not in rows:
            _fail(f"source report has unknown id: {record_id!r}")
        if record_id in reports:
            _fail(f"duplicate source report for {record_id}")
        row = rows[record_id]
        blind_hash = _canonical_sha(row)
        images = row.get("images")
        if not isinstance(images, list) or not images or any(
            not isinstance(image, str) or not image.strip() for image in images
        ):
            _fail(f"bundle row {record_id} has no canonical image inventory")
        image_paths: list[str] = []
        for image in images:
            locator = f"icho_2026_source/image/{image}"
            image_path = seed.joinpath(*PurePosixPath(locator).parts)
            if image_path.is_symlink() or not image_path.is_file():
                _fail(f"bundle row {record_id} image is absent or unsafe: {locator}")
            if locator not in image_paths:
                image_paths.append(locator)
        expected_entry = dict(row)
        expected_entry["blind_record_sha256"] = blind_hash
        # physics-formalize hashes the untouched bundle row, then applies its
        # ingestion normalization before persisting the source-report entry.
        # Replay both halves exactly: the trailing whitespace must not alter
        # the blind commitment, while the report projection uses stripped text.
        expected_entry["question"] = str(row.get("question") or "").strip()
        expected_entry["image"] = str(row.get("image") or images[0])
        expected_entry["image_paths"] = image_paths
        expected_entry["image_path"] = image_paths[0]
        if entry != expected_entry:
            _fail(f"source report {record_id} differs from canonical bundle projection")
        relative = PurePosixPath(path.relative_to(seed).as_posix())
        expected_target = f"IChO2026Problems/problem_{record_id}.lean"
        if (
            report.get("schema_version") != 3
            or report.get("evaluation_mode") != "answer_blind"
            or report.get("official_answer_seen") is not False
            or report.get("phase") != "solve"
            or report.get("blind_record_sha256") != blind_hash
            or report.get("previous_parts") != row.get("previous_parts")
            or report.get("output_lean") != expected_target
            or report.get("source_report") != relative.as_posix()
            or report.get("problem_id") != row.get("problem_id")
            or report.get("part_id") != row.get("part_id")
            or report.get("command") != "physics-formalize"
            or report.get("domain") != "chemistry"
            or report.get("proof_mode") != "chemistry"
            or report.get("prover_mode") != "chemistry-formalize"
            or report.get("path_base") != "project"
            or report.get("project_path") != "."
            or report.get("lean_search_packages")
            != ["Mathlib", "Physlib", "Chemistry"]
            or report.get("status") != "prepared"
            or report.get("next_stage") != "autoformalize"
        ):
            _fail(f"source report {record_id} metadata/provenance is non-canonical")
        reports[record_id] = (relative, _sha(payload))
    if set(reports) != set(rows) or len(regular_files) != EXPECTED_ITEM_COUNT:
        _fail("prepared source-report set differs from the 32-row bundle")
    return reports


def _uid_pids(uid: int) -> list[int]:
    result: list[int] = []
    for raw in os.listdir("/proc"):
        if not raw.isdigit():
            continue
        try:
            status = (Path("/proc") / raw / "status").read_text(
                encoding="utf-8", errors="replace"
            )
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        for line in status.splitlines():
            if line.startswith("Uid:"):
                fields = line.split()
                if len(fields) >= 2 and int(fields[1]) == uid:
                    result.append(int(raw))
                break
    return sorted(result)


@dataclasses.dataclass(frozen=True)
class Lane:
    number: int
    user: str
    uid: int
    gid: int
    scratch_root: Path


@dataclasses.dataclass(frozen=True)
class Config:
    campaign_id: str
    campaign_root: Path
    seed_workspace: Path
    runtime_root: Path
    dependency_root: Path
    codex_home: Path
    singleton_lock: Path
    verifier_users: tuple[str, ...]
    verifier_scratch_roots: tuple[Path, ...]
    concurrency: int
    max_attempts: int
    stage_timeout_s: int
    verifier_timeout_s: int
    parent_campaign_index: Path | None = None
    scope_ids: tuple[str, ...] = ()


@dataclasses.dataclass(frozen=True)
class ItemPaths:
    record_id: str
    ordinal: int
    run_id: str
    workspace: Path
    controller: Path
    snapshot: Path
    log_root: Path
    source_report_relative: PurePosixPath

    @property
    def bundle(self) -> Path:
        return self.workspace / "icho_2026_source/questions_only.jsonl"

    @property
    def assets(self) -> Path:
        return self.workspace / "icho_2026_source/image"


@dataclasses.dataclass(frozen=True)
class Binding:
    config: Config
    ids: tuple[str, ...]
    bundle_ids: tuple[str, ...]
    rows: Mapping[str, Mapping[str, Any]]
    orchestrator_sha256: str
    bundle_relative: PurePosixPath
    bundle_sha256: str
    seed_inventory: Mapping[str, str]
    seed_inventory_sha256: str
    runtime_inventory_sha256: str
    dependency_inventory_sha256: str
    source_reports: Mapping[str, tuple[PurePosixPath, str]]
    runtime_bins: Mapping[str, Path]
    lanes: tuple[Lane, ...]
    parent_campaign: ParentCampaign | None


@dataclasses.dataclass(frozen=True)
class ParentCampaign:
    index_path: Path
    index_sha256: str
    sidecar_path: Path
    sidecar_sha256: str
    campaign_id: str
    failed_ids: tuple[str, ...]
    lineage: tuple[CampaignReceipt, ...]


@dataclasses.dataclass(frozen=True)
class CampaignReceipt:
    index_path: Path
    index_sha256: str
    sidecar_path: Path
    sidecar_sha256: str
    campaign_id: str


def _resolve_lanes(config: Config) -> tuple[Lane, ...]:
    if len(config.verifier_users) != 4 or len(config.verifier_scratch_roots) != 4:
        _fail("exactly four verifier users and four paired scratch roots are required")
    if len(set(config.verifier_users)) != 4:
        _fail("verifier users must be distinct")
    lanes: list[Lane] = []
    seen_uids: set[int] = set()
    seen_gids: set[int] = set()
    for number, (user, raw_scratch) in enumerate(
        zip(config.verifier_users, config.verifier_scratch_roots, strict=True), start=1
    ):
        try:
            identity = pwd.getpwnam(user)
        except KeyError as exc:
            raise CampaignError(f"verifier user does not exist: {user}") from exc
        if (
            identity.pw_uid == 0
            or identity.pw_gid == 0
            or identity.pw_uid in seen_uids
            or identity.pw_gid in seen_gids
        ):
            _fail(f"verifier lane {number} must use a distinct non-root UID/GID")
        if _uid_pids(identity.pw_uid):
            _fail(f"verifier user is not quiescent before campaign: {user}")
        scratch = _require_root_directory(
            raw_scratch,
            label=f"verifier scratch root {number}",
            traversable=True,
            empty=True,
        )
        lanes.append(Lane(number, user, identity.pw_uid, identity.pw_gid, scratch))
        seen_uids.add(identity.pw_uid)
        seen_gids.add(identity.pw_gid)
    if len({lane.scratch_root for lane in lanes}) != 4:
        _fail("verifier scratch roots must be distinct")
    return tuple(lanes)


def _runtime_bins(runtime: Path) -> dict[str, Path]:
    paths = {
        "campaign": runtime / "bin/answer-blind-gpt-campaign",
        "review": runtime / "bin/answer-blind-independent-review",
        "solver": runtime / "bin/answer-blind-structured-solver",
        "verifier": runtime / "bin/answer-blind-verifier",
        "archon": runtime / "bin/archon",
        "codex": runtime / "bin/codex",
        "lake": runtime / "lean-v4.31.0/bin/lake",
    }
    return {
        name: _require_root_file(path, label=f"trusted runtime {name}", executable=True)
        for name, path in paths.items()
    }


def _orchestrator_runtime_binding(
    *, script_path: Path, runtime: Path, inventory: Mapping[str, str],
    executable: Path | None = None, startup_flags: Any | None = None,
) -> tuple[str, str]:
    """Bind this module, interpreter, and import policy to the sealed runtime."""
    expected = runtime.joinpath(*RUNTIME_ORCHESTRATOR.parts)
    if script_path != expected:
        _fail(
            "campaign controller must execute from the sealed runtime entry: "
            f"{expected}"
        )
    digest = _file_sha(script_path)
    if inventory.get(RUNTIME_ORCHESTRATOR.as_posix()) != digest:
        _fail("campaign controller is absent or stale in the runtime inventory")
    raw_executable = executable if executable is not None else Path(sys.executable)
    interpreter = raw_executable.resolve(strict=True)
    try:
        interpreter_relative = interpreter.relative_to(runtime).as_posix()
    except ValueError:
        _fail("campaign Python interpreter is outside the sealed runtime")
    interpreter_digest = _file_sha(interpreter)
    if inventory.get(interpreter_relative) != interpreter_digest:
        _fail("campaign Python interpreter is absent or stale in runtime inventory")
    flags = startup_flags if startup_flags is not None else sys.flags
    if not (
        flags.isolated
        and flags.ignore_environment
        and flags.safe_path
        and flags.no_user_site
        and flags.dont_write_bytecode
    ):
        _fail("campaign Python requires -I -B isolated startup flags")
    return digest, interpreter_digest


def _assert_singleton_available(path: Path) -> None:
    if not path.exists():
        return
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise CampaignError(
                f"another GPT full32 campaign holds singleton lock: {path}"
            ) from exc
        finally:
            with contextlib.suppress(OSError):
                fcntl.flock(descriptor, fcntl.LOCK_UN)
    finally:
        os.close(descriptor)


def _sealed_root_payload(path: Path, *, label: str, limit: int) -> tuple[Path, bytes]:
    """Read one immutable root receipt without following its final component."""
    resolved = _safe_absolute(path, label=label)
    try:
        descriptor = os.open(
            resolved, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC
        )
    except OSError as exc:
        raise CampaignError(f"cannot open {label}: {resolved}: {exc}") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != 0
            or stat.S_IMODE(metadata.st_mode) != 0o400
        ):
            _fail(f"{label} must be a root-owned mode-0400 regular file: {resolved}")
        if metadata.st_size > limit:
            _fail(f"{label} exceeds its size limit")
        chunks: list[bytes] = []
        remaining = limit + 1
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) > limit:
            _fail(f"{label} exceeds its size limit")
        checked = os.fstat(descriptor)
        if (
            checked.st_dev != metadata.st_dev
            or checked.st_ino != metadata.st_ino
            or checked.st_size != metadata.st_size
            or checked.st_mtime_ns != metadata.st_mtime_ns
        ):
            _fail(f"{label} changed while it was read")
        return resolved, payload
    finally:
        os.close(descriptor)


def _paths_overlap(left: Path, right: Path) -> bool:
    return (
        left == right
        or left.is_relative_to(right)
        or right.is_relative_to(left)
    )


def _execution_items(binding: Binding) -> tuple[tuple[int, str], ...]:
    positions = {
        record_id: ordinal
        for ordinal, record_id in enumerate(binding.bundle_ids, start=1)
    }
    return tuple((positions[record_id], record_id) for record_id in binding.ids)


def _parent_locator(parent: ParentCampaign | None) -> dict[str, Any] | None:
    if parent is None:
        return None
    return {
        "path": str(parent.index_path),
        "sha256": parent.index_sha256,
        "sidecar": {
            "path": str(parent.sidecar_path),
            "sha256": parent.sidecar_sha256,
        },
        "campaign_id": parent.campaign_id,
    }


def _valid_parent_locator(value: object) -> bool:
    if not isinstance(value, Mapping) or set(value) != {
        "path", "sha256", "sidecar", "campaign_id"
    }:
        return False
    raw_path = value.get("path")
    digest = value.get("sha256")
    campaign_id = value.get("campaign_id")
    sidecar = value.get("sidecar")
    if (
        not isinstance(raw_path, str)
        or not Path(raw_path).is_absolute()
        or Path(raw_path).name != "campaign-index.json"
        or not isinstance(digest, str)
        or SHA256.fullmatch(digest) is None
        or not isinstance(campaign_id, str)
        or SAFE_CAMPAIGN_ID.fullmatch(campaign_id) is None
        or not isinstance(sidecar, Mapping)
        or set(sidecar) != {"path", "sha256"}
    ):
        return False
    sidecar_path = sidecar.get("path")
    sidecar_digest = sidecar.get("sha256")
    return (
        isinstance(sidecar_path, str)
        and sidecar_path == raw_path + ".sha256"
        and isinstance(sidecar_digest, str)
        and SHA256.fullmatch(sidecar_digest) is not None
    )


def _execution_scope_document(binding: Binding) -> dict[str, Any]:
    return {
        "kind": (
            "failed_subset_retry"
            if binding.parent_campaign is not None
            else "full32"
        ),
        "ids": list(binding.ids),
    }


def _parent_execution_ids(
    value: Mapping[str, Any], *, bundle_ids: tuple[str, ...]
) -> tuple[str, ...]:
    scope = value.get("execution_scope")
    locator = value.get("parent_campaign_index")
    if scope is None and "parent_campaign_index" not in value:
        # Version-1 full32 indexes produced before subset retry support.
        return bundle_ids
    if not isinstance(scope, Mapping) or set(scope) != {"kind", "ids"}:
        _fail("parent campaign execution_scope is invalid")
    kind = scope.get("kind")
    raw_ids = scope.get("ids")
    if (
        not isinstance(raw_ids, list)
        or not raw_ids
        or any(not isinstance(item, str) for item in raw_ids)
        or len(raw_ids) != len(set(raw_ids))
    ):
        _fail("parent campaign execution scope IDs are invalid")
    ids = tuple(raw_ids)
    canonical = tuple(record_id for record_id in bundle_ids if record_id in set(ids))
    if ids != canonical:
        _fail("parent campaign execution scope is not in exact bundle order")
    if kind == "full32":
        if ids != bundle_ids or locator is not None:
            _fail("parent full32 execution scope has retry provenance")
    elif kind == "failed_subset_retry":
        if not _valid_parent_locator(locator):
            _fail("parent retry execution scope lacks parent provenance")
    else:
        _fail("parent campaign execution scope kind is invalid")
    return ids


def _load_parent_campaign(
    *, config: Config, bundle_ids: tuple[str, ...], bundle_sha256: str,
    campaign_root: Path,
    _lineage_paths: frozenset[Path] = frozenset(),
    _lineage_campaign_ids: frozenset[str] = frozenset(),
    _lineage_roots: frozenset[Path] = frozenset(),
) -> tuple[tuple[str, ...], ParentCampaign | None]:
    raw_parent = config.parent_campaign_index
    requested = config.scope_ids
    if raw_parent is None:
        if requested:
            _fail("--scope-id requires --parent-campaign-index")
        return bundle_ids, None
    if not requested:
        _fail("--parent-campaign-index requires at least one --scope-id")
    if (
        len(requested) != len(set(requested))
        or any(SAFE_ID.fullmatch(record_id) is None for record_id in requested)
    ):
        _fail("retry scope IDs must be unique safe IDs")
    requested_set = set(requested)
    canonical_requested = tuple(
        record_id for record_id in bundle_ids if record_id in requested_set
    )
    if requested != canonical_requested:
        _fail("retry scope must be an exact subset in canonical bundle order")

    parent_path, payload = _sealed_root_payload(
        raw_parent, label="parent campaign index", limit=MAX_PARENT_INDEX_BYTES
    )
    if parent_path.name != "campaign-index.json":
        _fail("parent campaign index must be named campaign-index.json")
    parent_root = _require_root_directory(
        parent_path.parent, label="parent campaign root"
    )
    if parent_path in _lineage_paths:
        _fail("parent campaign lineage contains an index cycle")
    descendant_roots = {*_lineage_roots, campaign_root}
    if any(_paths_overlap(root, parent_root) for root in descendant_roots):
        _fail("retry campaign root must be disjoint from the parent campaign root")
    index_sha = _sha(payload)
    sidecar_path, sidecar_payload = _sealed_root_payload(
        parent_path.with_suffix(parent_path.suffix + ".sha256"),
        label="parent campaign index sidecar",
        limit=512,
    )
    expected_sidecar = f"{index_sha}  {parent_path.name}\n".encode("ascii")
    if sidecar_payload != expected_sidecar:
        _fail("parent campaign index sidecar does not bind the sealed index")
    value = _strict_json(payload, label="parent campaign index")
    if (
        value.get("schema_version") != SCHEMA_VERSION
        or value.get("protocol") != PROTOCOL
        or value.get("phase") != "campaign"
        or value.get("integrity_error") is not None
        or value.get("status") not in {"succeeded", "failed"}
        or not isinstance(value.get("completed_at"), str)
        or not value.get("completed_at")
    ):
        _fail("parent campaign index is not a clean terminal campaign")
    campaign_id = value.get("campaign_id")
    if (
        not isinstance(campaign_id, str)
        or SAFE_CAMPAIGN_ID.fullmatch(campaign_id) is None
        or campaign_id == config.campaign_id
        or campaign_id in _lineage_campaign_ids
    ):
        _fail("parent campaign ID is invalid or reused")
    bundle = value.get("bundle")
    if (
        not isinstance(bundle, Mapping)
        or bundle.get("sha256") != bundle_sha256
        or bundle.get("row_count") != EXPECTED_ITEM_COUNT
        or bundle.get("ids") != list(bundle_ids)
    ):
        _fail("parent campaign does not bind the current full32 bundle")
    model = value.get("model")
    if (
        not isinstance(model, Mapping)
        or (model.get("variant"), model.get("family"), model.get("id"))
        != (VARIANT, MODEL_FAMILY, MODEL_ID)
    ):
        _fail("parent campaign model identity is stale")
    parent_ids = _parent_execution_ids(value, bundle_ids=bundle_ids)
    rows = value.get("items")
    if not isinstance(rows, list) or len(rows) != len(parent_ids):
        _fail("parent campaign item set differs from its execution scope")
    positions = {
        record_id: ordinal
        for ordinal, record_id in enumerate(bundle_ids, start=1)
    }
    actual_ids: list[str] = []
    counts = {"pending": 0, "running": 0, "succeeded": 0, "failed": 0}
    failed_ids: list[str] = []
    for row in rows:
        if not isinstance(row, Mapping):
            _fail("parent campaign item is not an object")
        record_id = row.get("id")
        if not isinstance(record_id, str):
            _fail("parent campaign item ID is invalid")
        actual_ids.append(record_id)
        status_value = row.get("status")
        if status_value not in {"succeeded", "failed"}:
            _fail("parent campaign contains pending or running item state")
        counts[status_value] += 1
        expected_ordinal = positions.get(record_id)
        if expected_ordinal is None:
            _fail(f"parent campaign item is outside the full32 bundle: {record_id}")
        expected_run_id = f"{campaign_id}-{expected_ordinal:02d}-{record_id}"
        if (
            row.get("ordinal") != expected_ordinal
            or row.get("run_id") != expected_run_id
            or row.get("current_stage") is not None
        ):
            _fail(f"parent campaign item binding is stale for {record_id}")
        for directory_name, field in (
            ("workspaces", "workspace"),
            ("controllers", "controller"),
            ("snapshots", "verifier_snapshot"),
        ):
            if row.get(field) != str(parent_path.parent / directory_name / record_id):
                _fail(f"parent campaign item path is stale for {record_id}")
        if status_value == "succeeded":
            if row.get("error") is not None:
                _fail(f"parent succeeded item retains an error for {record_id}")
            for field in ("controller_seal_sha256", "freeze_manifest_sha256"):
                digest = row.get(field)
                if not isinstance(digest, str) or SHA256.fullmatch(digest) is None:
                    _fail(f"parent succeeded item lacks {field} for {record_id}")
            stages = row.get("stages")
            if not isinstance(stages, Mapping) or set(stages) != set(STAGES):
                _fail(f"parent succeeded item lacks the full stage chain for {record_id}")
            if any(
                not isinstance(stages[stage], Mapping)
                or stages[stage].get("status") != "succeeded"
                for stage in STAGES
            ):
                _fail(f"parent succeeded item has a non-success stage for {record_id}")
            controller = parent_root / "controllers" / record_id
            for name, field in (
                ("gpt-freeze-authorization.json", "controller_seal_sha256"),
                ("gpt-frozen-manifest.json", "freeze_manifest_sha256"),
            ):
                _artifact_path, artifact_payload = _sealed_root_payload(
                    controller / name,
                    label=f"parent succeeded item {record_id} {name}",
                    limit=MAX_PARENT_INDEX_BYTES,
                )
                if _sha(artifact_payload) != row[field]:
                    _fail(
                        f"parent succeeded item {record_id} {name} hash drifted"
                    )
        else:
            error = row.get("error")
            stages = row.get("stages")
            if (
                not isinstance(error, Mapping)
                or set(error) != {"stage", "type", "message"}
                or error.get("stage") not in {*STAGES, "workspace-copy"}
                or any(
                    not isinstance(error.get(field), str) or not error.get(field)
                    for field in ("type", "message")
                )
            ):
                _fail(f"parent failed item lacks a structured error for {record_id}")
            error_stage = str(error["stage"])
            stage_count = len(stages) if isinstance(stages, Mapping) else -1
            expected_stage_set = (
                set(STAGES[:stage_count]) if stage_count >= 0 else set()
            )
            error_position = (
                STAGES.index(error_stage) if error_stage in STAGES else -1
            )
            if (
                not isinstance(stages, Mapping)
                or set(stages) != expected_stage_set
                or (
                    error_stage == "workspace-copy" and stage_count != 0
                )
                or (
                    error_position >= 0
                    and stage_count not in {error_position, error_position + 1}
                )
                or any(
                    not isinstance(stages.get(stage), Mapping)
                    or stages[stage].get("status") != "succeeded"
                    for stage in STAGES[: max(stage_count - 1, 0)]
                )
                or (
                    stage_count > 0
                    and (
                        not isinstance(stages.get(STAGES[stage_count - 1]), Mapping)
                        or stages[STAGES[stage_count - 1]].get("status")
                        not in {"succeeded", "failed"}
                    )
                )
            ):
                _fail(f"parent failed item stage state is stale for {record_id}")
            failed_ids.append(record_id)
    if tuple(actual_ids) != parent_ids:
        _fail("parent campaign item IDs/order differ from its execution scope")
    expected_summary = {
        "pending": 0,
        "running": 0,
        "succeeded": counts["succeeded"],
        "failed": counts["failed"],
    }
    if value.get("summary") != expected_summary:
        _fail("parent campaign terminal summary is stale")
    expected_status = "failed" if failed_ids else "succeeded"
    if value.get("status") != expected_status:
        _fail("parent campaign terminal status is stale")
    if not requested_set.issubset(set(failed_ids)):
        _fail("retry scope is not an exact subset of parent failed items")
    lineage: tuple[CampaignReceipt, ...] = (
        CampaignReceipt(
            index_path=parent_path,
            index_sha256=index_sha,
            sidecar_path=sidecar_path,
            sidecar_sha256=_sha(sidecar_payload),
            campaign_id=campaign_id,
        ),
    )
    scope = value.get("execution_scope")
    if isinstance(scope, Mapping) and scope.get("kind") == "failed_subset_retry":
        locator = value.get("parent_campaign_index")
        assert isinstance(locator, Mapping) and _valid_parent_locator(locator)
        ancestor_config = dataclasses.replace(
            config,
            campaign_id=campaign_id,
            parent_campaign_index=Path(str(locator["path"])),
            scope_ids=parent_ids,
        )
        _ancestor_ids, ancestor = _load_parent_campaign(
            config=ancestor_config,
            bundle_ids=bundle_ids,
            bundle_sha256=bundle_sha256,
            campaign_root=parent_root,
            _lineage_paths=frozenset((*_lineage_paths, parent_path)),
            _lineage_campaign_ids=frozenset(
                (*_lineage_campaign_ids, config.campaign_id, campaign_id)
            ),
            _lineage_roots=frozenset((*_lineage_roots, campaign_root, parent_root)),
        )
        assert ancestor is not None
        if _parent_locator(ancestor) != dict(locator):
            _fail("parent campaign lineage locator/hash does not match its ancestor")
        lineage += ancestor.lineage
    return requested, ParentCampaign(
        index_path=parent_path,
        index_sha256=index_sha,
        sidecar_path=sidecar_path,
        sidecar_sha256=_sha(sidecar_payload),
        campaign_id=campaign_id,
        failed_ids=tuple(failed_ids),
        lineage=lineage,
    )


def preflight(config: Config, *, lock_may_be_held: bool = False) -> Binding:
    if os.geteuid() != 0:
        _fail("GPT full campaign controller must run as root")
    script_path = Path(__file__).resolve()
    _require_root_file(script_path, label="campaign controller")
    if SAFE_CAMPAIGN_ID.fullmatch(config.campaign_id) is None:
        _fail("campaign id is unsafe")
    if not 1 <= config.concurrency <= EXPECTED_ITEM_COUNT:
        _fail(f"concurrency must be between 1 and {EXPECTED_ITEM_COUNT}")
    if not 1 <= config.max_attempts <= 16:
        _fail("max attempts must be between 1 and 16")
    if config.stage_timeout_s < 1 or config.verifier_timeout_s < 1:
        _fail("stage and verifier timeouts must be positive")

    campaign_root = _safe_absolute(config.campaign_root, label="campaign root")
    if campaign_root.exists() or campaign_root.is_symlink():
        _fail(
            "campaign root already exists; half-complete campaigns are never reused: "
            f"{campaign_root}"
        )
    campaign_parent = _require_root_directory(
        campaign_root.parent, label="campaign parent", traversable=True
    )
    singleton_lock = _safe_absolute(config.singleton_lock, label="singleton lock")
    _require_root_directory(singleton_lock.parent, label="singleton lock parent")
    if singleton_lock.exists() or singleton_lock.is_symlink():
        if singleton_lock.is_symlink() or not singleton_lock.is_file():
            _fail(f"singleton lock must be a regular file: {singleton_lock}")
        lock_metadata = singleton_lock.stat(follow_symlinks=False)
        if lock_metadata.st_uid != 0 or lock_metadata.st_mode & 0o022:
            _fail(f"singleton lock is not root-owned private state: {singleton_lock}")
        if not lock_may_be_held:
            _assert_singleton_available(singleton_lock)
    for ancestor in (campaign_parent, *campaign_parent.parents):
        if ancestor.stat(follow_symlinks=False).st_mode & 0o001 == 0:
            _fail(f"campaign snapshot path would not be world-traversable: {ancestor}")

    seed = _require_root_directory(config.seed_workspace, label="prepared full32 seed")
    runtime = _require_root_directory(
        config.runtime_root, label="answer-blind runtime", traversable=True
    )
    expected_orchestrator = runtime.joinpath(*RUNTIME_ORCHESTRATOR.parts)
    if script_path != expected_orchestrator:
        _fail(
            "campaign controller must be launched from its sealed runtime wrapper; "
            f"expected {expected_orchestrator}"
        )
    dependency = _require_root_directory(
        config.dependency_root, label="Lean dependency root", traversable=True
    )
    codex_home = _require_root_directory(config.codex_home, label="Codex login home")
    _require_disjoint(
        {
            "campaign": campaign_root,
            "seed": seed,
            "runtime": runtime,
            "dependency": dependency,
            "codex_home": codex_home,
            "singleton_lock": singleton_lock,
        }
    )

    bundle = seed / "icho_2026_source/questions_only.jsonl"
    _require_root_file(bundle, label="full32 questions-only bundle")
    bundle_payload, rows = _bundle_rows(bundle)
    bundle_ids = tuple(sorted(rows))
    ids, parent_campaign = _load_parent_campaign(
        config=config,
        bundle_ids=bundle_ids,
        bundle_sha256=_sha(bundle_payload),
        campaign_root=campaign_root,
    )
    positions = {
        record_id: ordinal
        for ordinal, record_id in enumerate(bundle_ids, start=1)
    }
    for record_id in ids:
        ordinal = positions[record_id]
        run_id = f"{config.campaign_id}-{ordinal:02d}-{record_id}"
        if SAFE_ID.fullmatch(run_id) is None:
            _fail(f"derived item run id is unsafe or too long: {run_id}")
    source_reports = _source_reports(seed, rows)
    seed_inventory = _plain_seed_inventory(seed)
    bundle_relative = PurePosixPath(bundle.relative_to(seed).as_posix())
    if seed_inventory.get(bundle_relative.as_posix()) != _sha(bundle_payload):
        _fail("prepared seed inventory does not bind the full32 bundle")

    runtime_bins = _runtime_bins(runtime)
    _assert_runtime_cache_free(runtime)
    dependency_exclusion = (
        (dependency,) if dependency.is_relative_to(runtime) else ()
    )
    runtime_inventory = _controller_inventory(
        runtime, label="answer-blind runtime", exclude_roots=dependency_exclusion
    )
    orchestrator_sha256, _interpreter_sha256 = _orchestrator_runtime_binding(
        script_path=script_path, runtime=runtime, inventory=runtime_inventory
    )
    dependency_inventory = _controller_inventory(
        dependency, label="Lean dependency tree"
    )
    lanes = _resolve_lanes(config)
    _require_disjoint(
        {
            "campaign": campaign_root,
            "seed": seed,
            "runtime": runtime,
            "dependency": dependency,
            "codex_home": codex_home,
            **(
                {
                    f"parent-{index}": receipt.index_path.parent
                    for index, receipt in enumerate(
                        parent_campaign.lineage, start=1
                    )
                }
                if parent_campaign is not None
                else {}
            ),
            **{f"scratch-{lane.number}": lane.scratch_root for lane in lanes},
        }
    )
    return Binding(
        config=dataclasses.replace(
            config,
            campaign_root=campaign_root,
            seed_workspace=seed,
            runtime_root=runtime,
            dependency_root=dependency,
            codex_home=codex_home,
            singleton_lock=singleton_lock,
            parent_campaign_index=(
                parent_campaign.index_path if parent_campaign is not None else None
            ),
            scope_ids=ids if parent_campaign is not None else (),
        ),
        ids=ids,
        bundle_ids=bundle_ids,
        rows=rows,
        orchestrator_sha256=orchestrator_sha256,
        bundle_relative=bundle_relative,
        bundle_sha256=_sha(bundle_payload),
        seed_inventory=seed_inventory,
        seed_inventory_sha256=_hash_index(seed_inventory),
        runtime_inventory_sha256=_hash_index(runtime_inventory),
        dependency_inventory_sha256=_hash_index(dependency_inventory),
        source_reports=source_reports,
        runtime_bins=runtime_bins,
        lanes=lanes,
        parent_campaign=parent_campaign,
    )


def _item_paths(binding: Binding, record_id: str, ordinal: int) -> ItemPaths:
    root = binding.config.campaign_root
    report_relative = binding.source_reports[record_id][0]
    run_id = f"{binding.config.campaign_id}-{ordinal:02d}-{record_id}"
    if SAFE_ID.fullmatch(run_id) is None:
        _fail(f"derived item run id is unsafe: {run_id}")
    return ItemPaths(
        record_id=record_id,
        ordinal=ordinal,
        run_id=run_id,
        workspace=root / "workspaces" / record_id,
        controller=root / "controllers" / record_id,
        snapshot=root / "snapshots" / record_id,
        log_root=root / "logs" / record_id,
        source_report_relative=report_relative,
    )


def _commands(binding: Binding, item: ItemPaths, lane: Lane) -> list[tuple[str, list[str]]]:
    config = binding.config
    binary = binding.runtime_bins
    precommit = item.controller / "gpt-source-first-precommit.json"
    solver = item.controller / "gpt-structured-solver-receipt.json"
    submission = item.controller / "gpt-artifact-review-submission.json"
    verifier = item.controller / "gpt-lean-verifier-invocation.json"
    review = item.controller / "gpt-structured-independent-review.json"
    seal = item.controller / "gpt-freeze-authorization.json"
    frozen = item.controller / "gpt-frozen-manifest.json"
    common_transport = [
        "--codex-binary",
        str(binary["codex"]),
        "--codex-home",
        str(config.codex_home),
    ]
    scope = ["--scope-id", item.record_id]
    return [
        (
            "source-first",
            [
                str(binary["review"]),
                "source-first",
                "--controller-dir",
                str(item.controller),
                "--bundle",
                str(item.bundle),
                "--asset-root",
                str(item.assets),
                "--variant",
                VARIANT,
                "--run-id",
                item.run_id,
                *scope,
                *common_transport,
            ],
        ),
        (
            "solver",
            [
                str(binary["solver"]),
                "--workspace",
                str(item.workspace),
                "--controller-dir",
                str(item.controller),
                "--bundle",
                str(item.bundle),
                "--asset-root",
                str(item.assets),
                "--variant",
                VARIANT,
                "--run-id",
                item.run_id,
                "--source-first-precommit",
                str(precommit),
                *scope,
                "--max-attempts",
                str(config.max_attempts),
                "--runtime-lake",
                str(binary["lake"]),
                "--dependency-root",
                str(config.dependency_root),
                "--verifier-user",
                lane.user,
                "--verifier-scratch",
                str(lane.scratch_root),
                *common_transport,
            ],
        ),
        (
            "artifact-submit",
            [
                str(binary["review"]),
                "artifact-submit",
                "--workspace",
                str(item.workspace),
                "--controller-dir",
                str(item.controller),
                "--bundle",
                str(item.bundle),
                "--source-first-precommit",
                str(precommit),
                "--solver-aggregate",
                str(solver),
                "--dependency-root",
                str(config.dependency_root),
                "--variant",
                VARIANT,
                "--run-id",
                item.run_id,
                *scope,
                *common_transport,
            ],
        ),
        (
            "snapshot",
            [
                str(binary["archon"]),
                "blind-create-verifier-snapshot",
                "--project",
                str(item.workspace),
                "--dependency-root",
                str(config.dependency_root),
                "--output",
                str(item.snapshot),
            ],
        ),
        (
            "verifier",
            [
                str(binary["verifier"]),
                "--snapshot-root",
                str(item.snapshot),
                "--controller-dir",
                str(item.controller),
                "--runtime-root",
                str(config.runtime_root),
                "--dependency-root",
                str(config.dependency_root),
                "--archon-executable",
                str(binary["archon"]),
                "--lake-executable",
                str(binary["lake"]),
                "--verifier-user",
                lane.user,
                "--scratch-root",
                str(lane.scratch_root),
                "--output",
                str(verifier),
                *scope,
                "--timeout-s",
                str(config.verifier_timeout_s),
            ],
        ),
        (
            "artifact-finalize",
            [
                str(binary["review"]),
                "artifact-finalize",
                "--workspace",
                str(item.workspace),
                "--controller-dir",
                str(item.controller),
                "--bundle",
                str(item.bundle),
                "--source-first-precommit",
                str(precommit),
                "--solver-aggregate",
                str(solver),
                "--artifact-submission",
                str(submission),
                "--verifier-invocation",
                str(verifier),
                "--verifier-snapshot",
                str(item.snapshot),
                "--dependency-root",
                str(config.dependency_root),
                "--snapshot-inventory-sha256",
                "{snapshot_inventory_sha256}",
                "--variant",
                VARIANT,
                "--run-id",
                item.run_id,
                *scope,
            ],
        ),
        (
            "seal-pilot",
            [
                str(binary["archon"]),
                "blind-create-seal",
                "--project",
                str(item.workspace),
                "--bundle",
                str(item.bundle),
                "--structured-solver-receipt",
                str(solver),
                "--source-first-precommit",
                str(precommit),
                "--independent-review-receipt",
                str(review),
                "--verifier-receipt",
                str(verifier),
                "--dependency-root",
                str(config.dependency_root),
                "--runtime-root",
                str(config.runtime_root),
                "--verifier-snapshot",
                str(item.snapshot),
                "--output",
                str(seal),
                "--scope-kind",
                "pilot",
                *scope,
            ],
        ),
        (
            "freeze",
            [
                str(binary["archon"]),
                "blind-freeze",
                "--project",
                str(item.workspace),
                "--candidate-dir",
                "blind_candidates",
                "--output",
                str(frozen),
                "--controller-seal",
                str(seal),
                "--expected-controller-seal-sha256",
                "{controller_seal_sha256}",
            ],
        ),
    ]


def _copy_file(source: Path, destination: Path) -> None:
    metadata = source.lstat()
    if source.is_symlink() or not stat.S_ISREG(metadata.st_mode):
        _fail(f"unsafe seed copy source: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor_in = os.open(source, os.O_RDONLY | os.O_NOFOLLOW)
    descriptor_out = -1
    try:
        checked = os.fstat(descriptor_in)
        if (
            not stat.S_ISREG(checked.st_mode)
            or checked.st_uid != 0
            or checked.st_mode & 0o022
        ):
            _fail(f"seed file changed during copy: {source}")
        mode = stat.S_IMODE(checked.st_mode)
        descriptor_out = os.open(
            destination,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            mode,
        )
        while True:
            chunk = os.read(descriptor_in, 1024 * 1024)
            if not chunk:
                break
            view = memoryview(chunk)
            while view:
                written = os.write(descriptor_out, view)
                if written <= 0:
                    _fail(f"short write while copying seed file: {destination}")
                view = view[written:]
        os.fchmod(descriptor_out, mode)
        os.fsync(descriptor_out)
    finally:
        os.close(descriptor_in)
        if descriptor_out >= 0:
            os.close(descriptor_out)


def _prepare_workspace(binding: Binding, item: ItemPaths) -> None:
    if any(
        path.exists() or path.is_symlink()
        for path in (item.workspace, item.controller, item.snapshot, item.log_root)
    ):
        _fail(f"refusing to reuse half-complete item paths for {item.record_id}")
    item.workspace.mkdir(mode=0o700)
    item.controller.mkdir(mode=0o700)
    item.log_root.mkdir(mode=0o700)
    seed = binding.config.seed_workspace
    for source in sorted(seed.rglob("*")):
        relative = source.relative_to(seed)
        if relative.parts and relative.parts[0] == "reports":
            continue
        destination = item.workspace / relative
        metadata = source.lstat()
        if source.is_symlink():
            _fail(f"prepared seed acquired a symlink during copy: {relative}")
        if stat.S_ISDIR(metadata.st_mode):
            destination.mkdir(mode=stat.S_IMODE(metadata.st_mode))
        elif stat.S_ISREG(metadata.st_mode):
            _copy_file(source, destination)
        else:
            _fail(f"prepared seed acquired a special entry during copy: {relative}")
    report_source = seed.joinpath(*item.source_report_relative.parts)
    report_destination = item.workspace.joinpath(*item.source_report_relative.parts)
    _copy_file(report_source, report_destination)

    expected = {
        relative: digest
        for relative, digest in binding.seed_inventory.items()
        if not relative.startswith("reports/")
    }
    expected[item.source_report_relative.as_posix()] = binding.source_reports[
        item.record_id
    ][1]
    actual = _plain_seed_inventory(item.workspace)
    if actual != dict(sorted(expected.items())):
        _fail(f"per-item workspace copy differs from prepared seed for {item.record_id}")
    if _file_sha(item.bundle) != binding.bundle_sha256:
        _fail(f"per-item workspace lost the full32 bundle for {item.record_id}")
    reports = list((item.workspace / "reports").rglob("*.source.json"))
    if reports != [report_destination]:
        _fail(f"per-item workspace does not contain exactly one source report: {item.record_id}")


def _mkdir_layout(binding: Binding) -> None:
    root = binding.config.campaign_root
    root.mkdir(mode=0o711)
    (root / "workspaces").mkdir(mode=0o700)
    (root / "controllers").mkdir(mode=0o700)
    (root / "snapshots").mkdir(mode=0o755)
    (root / "logs").mkdir(mode=0o700)


def _atomic_index(path: Path, value: Mapping[str, Any], *, final: bool = False) -> None:
    payload = _json_bytes(value, pretty=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    descriptor = os.open(
        temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600
    )
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail("short campaign index write")
            view = view[written:]
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o400 if final else 0o600)
    finally:
        os.close(descriptor)
    os.replace(temporary, path)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _initial_index(binding: Binding) -> dict[str, Any]:
    config = binding.config
    items: list[dict[str, Any]] = []
    for ordinal, record_id in _execution_items(binding):
        paths = _item_paths(binding, record_id, ordinal)
        items.append(
            {
                "id": record_id,
                "ordinal": ordinal,
                "run_id": paths.run_id,
                "status": "pending",
                "current_stage": None,
                "solver_lane": None,
                "verifier_lane": None,
                "workspace": str(paths.workspace),
                "controller": str(paths.controller),
                "verifier_snapshot": str(paths.snapshot),
                "source_report": {
                    "path": paths.source_report_relative.as_posix(),
                    "sha256": binding.source_reports[record_id][1],
                },
                "stages": {},
                "controller_seal_sha256": None,
                "freeze_manifest_sha256": None,
                "error": None,
            }
        )
    now = _utcnow()
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "campaign",
        "campaign_id": config.campaign_id,
        "status": "running",
        "created_at": now,
        "updated_at": now,
        "completed_at": None,
        "execution_scope": _execution_scope_document(binding),
        "parent_campaign_index": _parent_locator(binding.parent_campaign),
        "orchestrator": {
            "path": str(Path(__file__).resolve()),
            "sha256": binding.orchestrator_sha256,
        },
        "bundle": {
            "seed_root": str(config.seed_workspace),
            "path": binding.bundle_relative.as_posix(),
            "sha256": binding.bundle_sha256,
            "row_count": EXPECTED_ITEM_COUNT,
            "ids": list(binding.bundle_ids),
        },
        "seed_inventory_sha256": binding.seed_inventory_sha256,
        "runtime": {
            "root": str(config.runtime_root),
            "inventory_sha256": binding.runtime_inventory_sha256,
        },
        "dependency": {
            "root": str(config.dependency_root),
            "inventory_sha256": binding.dependency_inventory_sha256,
        },
        "model": {
            "variant": VARIANT,
            "family": MODEL_FAMILY,
            "id": MODEL_ID,
            "codex_binary": {
                "path": str(binding.runtime_bins["codex"]),
                "sha256": _file_sha(binding.runtime_bins["codex"]),
            },
            "codex_home": str(config.codex_home),
        },
        "execution": {
            "concurrency": config.concurrency,
            "pre_verifier_concurrency": config.concurrency,
            "final_verifier_concurrency": min(config.concurrency, len(binding.lanes)),
            "max_attempts": config.max_attempts,
            "stage_timeout_s": config.stage_timeout_s,
            "verifier_timeout_s": config.verifier_timeout_s,
            "resume_supported": False,
            "failure_reuses_partial_state": False,
            "singleton_lock": str(config.singleton_lock),
            "lanes": [
                {
                    "number": lane.number,
                    "user": lane.user,
                    "uid": lane.uid,
                    "gid": lane.gid,
                    "scratch_root": str(lane.scratch_root),
                }
                for lane in binding.lanes
            ],
        },
        "items": items,
        "summary": {
            "pending": len(binding.ids),
            "running": 0,
            "succeeded": 0,
            "failed": 0,
        },
        "integrity_error": None,
    }


class IndexWriter:
    def __init__(self, path: Path, value: dict[str, Any]) -> None:
        self.path = path
        self.value = value
        self.lock = asyncio.Lock()
        self.by_id = {row["id"]: row for row in value["items"]}

    def _recount(self) -> None:
        counts = {"pending": 0, "running": 0, "succeeded": 0, "failed": 0}
        for row in self.value["items"]:
            status_value = row["status"]
            if status_value in {"preparing", "running", "awaiting_verifier"}:
                counts["running"] += 1
            else:
                counts[status_value] += 1
        self.value["summary"] = counts

    async def update_item(self, record_id: str, **changes: Any) -> None:
        async with self.lock:
            self.by_id[record_id].update(changes)
            self.value["updated_at"] = _utcnow()
            self._recount()
            _atomic_index(self.path, self.value)

    async def stage(
        self, record_id: str, stage: str, stage_value: Mapping[str, Any]
    ) -> None:
        async with self.lock:
            self.by_id[record_id]["stages"][stage] = dict(stage_value)
            self.value["updated_at"] = _utcnow()
            self._recount()
            _atomic_index(self.path, self.value)

    def _success_integrity_error(self) -> str | None:
        bundle = self.value.get("bundle")
        bundle_ids = bundle.get("ids") if isinstance(bundle, Mapping) else None
        scope = self.value.get("execution_scope")
        parent = self.value.get("parent_campaign_index")
        rows = self.value.get("items")
        if (
            not isinstance(bundle_ids, list)
            or len(bundle_ids) != EXPECTED_ITEM_COUNT
            or any(not isinstance(record_id, str) for record_id in bundle_ids)
            or len(set(bundle_ids)) != EXPECTED_ITEM_COUNT
        ):
            return "campaign index does not bind exactly 32 unique bundle IDs"
        if not isinstance(scope, Mapping) or set(scope) != {"kind", "ids"}:
            return "campaign index has an invalid execution scope"
        expected_ids = scope.get("ids")
        if (
            not isinstance(expected_ids, list)
            or not expected_ids
            or any(not isinstance(record_id, str) for record_id in expected_ids)
            or len(expected_ids) != len(set(expected_ids))
            or expected_ids
            != [record_id for record_id in bundle_ids if record_id in set(expected_ids)]
            or not isinstance(rows, list)
            or len(rows) != len(expected_ids)
        ):
            return "campaign execution scope is not an exact ordered bundle subset"
        if scope.get("kind") == "full32":
            if expected_ids != bundle_ids or parent is not None:
                return "full32 campaign has retry-only scope provenance"
        elif scope.get("kind") == "failed_subset_retry":
            if not _valid_parent_locator(parent):
                return "retry campaign parent locator/hash is invalid"
        else:
            return "campaign execution scope kind is invalid"
        actual_ids = [row.get("id") for row in rows if isinstance(row, Mapping)]
        if actual_ids != expected_ids:
            return "campaign item IDs/order differ from the execution scope"
        campaign_id = self.value.get("campaign_id")
        if not isinstance(campaign_id, str) or SAFE_CAMPAIGN_ID.fullmatch(campaign_id) is None:
            return "campaign index has an invalid campaign ID"
        positions = {
            record_id: ordinal
            for ordinal, record_id in enumerate(bundle_ids, start=1)
        }
        for row in rows:
            assert isinstance(row, Mapping)
            record_id = str(row.get("id") or "")
            ordinal = positions.get(record_id)
            if ordinal is None:
                return f"campaign item {record_id} is outside the bundle"
            expected_run_id = f"{campaign_id}-{ordinal:02d}-{record_id}"
            if row.get("ordinal") != ordinal or row.get("run_id") != expected_run_id:
                return f"campaign item {record_id} has stale ordinal/run_id binding"
            if row.get("status") != "succeeded" or row.get("error") is not None:
                return f"campaign item is not terminal-success: {record_id}"
            for field in ("controller_seal_sha256", "freeze_manifest_sha256"):
                digest = row.get(field)
                if not isinstance(digest, str) or SHA256.fullmatch(digest) is None:
                    return f"campaign item {record_id} has no valid {field}"
            stages = row.get("stages")
            if not isinstance(stages, Mapping) or set(stages) != set(STAGES):
                return f"campaign item {record_id} does not bind every stage"
            for stage in STAGES:
                stage_value = stages.get(stage)
                if (
                    not isinstance(stage_value, Mapping)
                    or stage_value.get("status") != "succeeded"
                ):
                    return f"campaign item {record_id} stage {stage} is not succeeded"
                argv = stage_value.get("argv")
                if not isinstance(argv, list) or any(
                    isinstance(token, str) and token.startswith("{") and token.endswith("}")
                    for token in argv
                ):
                    return f"campaign item {record_id} stage {stage} retains a placeholder"
            controller_raw = row.get("controller")
            if not isinstance(controller_raw, str) or not Path(controller_raw).is_absolute():
                return f"campaign item {record_id} has an invalid controller path"
            controller = Path(controller_raw)
            for name, field in (
                ("gpt-freeze-authorization.json", "controller_seal_sha256"),
                ("gpt-frozen-manifest.json", "freeze_manifest_sha256"),
            ):
                path = controller / name
                if path.is_symlink() or not path.is_file():
                    return f"campaign item {record_id} lost finalized {name}"
                metadata = path.stat(follow_symlinks=False)
                if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o400:
                    return f"campaign item {record_id} finalized {name} is not sealed"
                if _file_sha(path) != row[field]:
                    return f"campaign item {record_id} finalized {name} hash drifted"
        return None

    async def finalize(self, *, integrity_error: str | None = None) -> None:
        async with self.lock:
            self._recount()
            summary = self.value["summary"]
            scope = self.value.get("execution_scope")
            scope_ids = scope.get("ids") if isinstance(scope, Mapping) else None
            expected_count = len(scope_ids) if isinstance(scope_ids, list) else -1
            final_error = integrity_error
            if final_error is None and (
                summary["pending"] != 0
                or summary["running"] != 0
                or summary["succeeded"] + summary["failed"] != expected_count
            ):
                final_error = "campaign finalized with nonterminal items"
            if final_error is None and summary["failed"] == 0:
                final_error = self._success_integrity_error()
            self.value["integrity_error"] = final_error
            self.value["status"] = (
                "succeeded"
                if final_error is None
                and summary == {
                    "pending": 0,
                    "running": 0,
                    "succeeded": expected_count,
                    "failed": 0,
                }
                else "failed"
            )
            self.value["updated_at"] = _utcnow()
            self.value["completed_at"] = self.value["updated_at"]
            _atomic_index(self.path, self.value, final=True)


def _command_environment(binding: Binding) -> dict[str, str]:
    runtime = binding.config.runtime_root
    return {
        "HOME": "/root",
        "PATH": f"{runtime / 'bin'}:{runtime / 'lean-v4.31.0/bin'}:/usr/bin:/bin",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TZ": "UTC",
        "PYTHONSAFEPATH": "1",
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }


async def _terminate_process_group(process: asyncio.subprocess.Process) -> None:
    with contextlib.suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGTERM)
    if process.returncode is None:
        with contextlib.suppress(asyncio.TimeoutError):
            await asyncio.wait_for(process.wait(), timeout=5)
    # The direct controller may have exited while a descendant retained the
    # process group.  A second signal is intentional on failure/timeout paths.
    with contextlib.suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    if process.returncode is None:
        with contextlib.suppress(asyncio.TimeoutError):
            await asyncio.wait_for(process.wait(), timeout=5)


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


async def _run_stage(
    *,
    binding: Binding,
    item: ItemPaths,
    index: IndexWriter,
    stage: str,
    argv: Sequence[str],
) -> None:
    if stage not in STAGES:
        _fail(f"unknown campaign stage: {stage}")
    log_path = item.log_root / f"{STAGES.index(stage) + 1:02d}-{stage}.log"
    started_at = _utcnow()
    started = time.monotonic()
    await index.stage(
        item.record_id,
        stage,
        {
            "status": "running",
            "started_at": started_at,
            "completed_at": None,
            "argv": list(argv),
            "argv_sha256": _sha(_json_bytes(list(argv))),
            "log": str(log_path),
            "log_sha256": None,
            "exit_code": None,
        },
    )
    timed_out = False
    process: asyncio.subprocess.Process | None = None
    execution_error: Exception | None = None
    try:
        descriptor = os.open(
            log_path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o600,
        )
        with os.fdopen(descriptor, "wb", closefd=True) as log:
            process = await asyncio.create_subprocess_exec(
                *argv,
                cwd=item.workspace,
                env=_command_environment(binding),
                stdin=asyncio.subprocess.DEVNULL,
                stdout=log,
                stderr=asyncio.subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                await asyncio.wait_for(
                    process.wait(), timeout=binding.config.stage_timeout_s
                )
            except asyncio.TimeoutError:
                timed_out = True
                await _terminate_process_group(process)
            log.flush()
            os.fsync(log.fileno())
    except asyncio.CancelledError:
        if process is not None:
            await _terminate_process_group(process)
        raise
    except Exception as exc:
        execution_error = exc
        if process is not None:
            await _terminate_process_group(process)
    finally:
        if log_path.is_file() and not log_path.is_symlink():
            os.chown(log_path, 0, 0)
            os.chmod(log_path, 0o400)
    exit_code = process.returncode if process is not None else None
    if (
        execution_error is None
        and not timed_out
        and exit_code == 0
        and process is not None
        and _process_group_exists(process.pid)
    ):
        await _terminate_process_group(process)
        execution_error = CampaignError(
            "successful controller left descendants in its process group"
        )
    elif process is not None and exit_code not in {None, 0} and not timed_out:
        await _terminate_process_group(process)
    completed_at = _utcnow()
    status_value = (
        "failed" if execution_error is not None or timed_out or exit_code != 0 else "succeeded"
    )
    stage_value = {
        "status": status_value,
        "started_at": started_at,
        "completed_at": completed_at,
        "duration_seconds": round(time.monotonic() - started, 6),
        "argv": list(argv),
        "argv_sha256": _sha(_json_bytes(list(argv))),
        "log": str(log_path),
        "log_sha256": _file_sha(log_path) if log_path.is_file() else None,
        "exit_code": exit_code,
        "timed_out": timed_out,
        "controller_error": (
            None
            if execution_error is None
            else {"type": type(execution_error).__name__, "message": str(execution_error)}
        ),
    }
    await index.stage(item.record_id, stage, stage_value)
    if execution_error is not None:
        raise StageError(
            stage,
            f"{stage} controller failed for {item.record_id}: {execution_error}",
        ) from execution_error
    if timed_out:
        raise StageError(stage, f"{stage} timed out for {item.record_id}")
    if exit_code != 0:
        raise StageError(
            stage, f"{stage} exited {exit_code} for {item.record_id}; inspect {log_path}"
        )


def _load_receipt(path: Path, *, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} was not produced: {path}")
    metadata = path.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o400:
        _fail(f"{label} is not finalized root-owned mode 0400: {path}")
    return _strict_json(path.read_bytes(), label=label)


def _replace_placeholder(argv: Sequence[str], placeholder: str, value: str) -> list[str]:
    if list(argv).count(placeholder) != 1:
        _fail(f"internal command placeholder drift: {placeholder}")
    return [value if token == placeholder else token for token in argv]


def _lane_document(lane: Lane) -> dict[str, Any]:
    return {
        "number": lane.number,
        "user": lane.user,
        "uid": lane.uid,
        "scratch_root": str(lane.scratch_root),
    }


async def _record_item_failure(
    *, index: IndexWriter, item: ItemPaths, exc: Exception, default_stage: str
) -> None:
    stage = exc.stage if isinstance(exc, StageError) else default_stage
    await index.update_item(
        item.record_id,
        status="failed",
        current_stage=None,
        error={"stage": stage, "type": type(exc).__name__, "message": str(exc)},
    )


async def _run_pre_verifier_item(
    *, binding: Binding, item: ItemPaths, solver_lane: Lane,
    solver_lane_lock: asyncio.Lock, index: IndexWriter,
) -> bool:
    """Run the model-bearing half of one item before the UID barrier."""
    await index.update_item(
        item.record_id,
        status="preparing",
        current_stage="workspace-copy",
        solver_lane=_lane_document(solver_lane),
    )
    current_stage = "workspace-copy"
    try:
        await asyncio.to_thread(_prepare_workspace, binding, item)
        await index.update_item(
            item.record_id, status="running", current_stage="source-first"
        )
        for stage, argv in _commands(binding, item, solver_lane):
            if stage == "verifier":
                break
            current_stage = stage
            await index.update_item(item.record_id, current_stage=stage)
            if stage == "solver":
                async with solver_lane_lock:
                    await _run_stage(
                        binding=binding,
                        item=item,
                        index=index,
                        stage=stage,
                        argv=list(argv),
                    )
            else:
                await _run_stage(
                    binding=binding,
                    item=item,
                    index=index,
                    stage=stage,
                    argv=list(argv),
                )
        await index.update_item(
            item.record_id,
            status="awaiting_verifier",
            current_stage=None,
            error=None,
        )
        return True
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        await _record_item_failure(
            index=index, item=item, exc=exc, default_stage=current_stage
        )
        return False


async def _run_post_verifier_item(
    *, binding: Binding, item: ItemPaths, verifier_lane: Lane, index: IndexWriter
) -> None:
    """Run final verification and the model-free irreversible close."""
    await index.update_item(
        item.record_id,
        status="running",
        current_stage="verifier",
        verifier_lane=_lane_document(verifier_lane),
    )
    current_stage = "verifier"
    try:
        for stage, raw_argv in _commands(binding, item, verifier_lane):
            if STAGES.index(stage) < STAGES.index("verifier"):
                continue
            current_stage = stage
            argv = list(raw_argv)
            if stage == "artifact-finalize":
                verifier_path = item.controller / "gpt-lean-verifier-invocation.json"
                verifier = _load_receipt(verifier_path, label="Lean verifier invocation")
                snapshot_sha = verifier.get("snapshot_inventory_sha256")
                if not isinstance(snapshot_sha, str) or SHA256.fullmatch(snapshot_sha) is None:
                    raise StageError(stage, "verifier receipt has invalid snapshot digest")
                argv = _replace_placeholder(
                    argv, "{snapshot_inventory_sha256}", snapshot_sha
                )
            elif stage == "freeze":
                seal_path = item.controller / "gpt-freeze-authorization.json"
                _load_receipt(seal_path, label="pilot controller seal")
                seal_sha = _file_sha(seal_path)
                argv = _replace_placeholder(argv, "{controller_seal_sha256}", seal_sha)
            elif stage == "seal-pilot":
                await asyncio.to_thread(
                    _assert_runtime_cache_free, binding.config.runtime_root
                )
            await index.update_item(item.record_id, current_stage=stage)
            await _run_stage(
                binding=binding, item=item, index=index, stage=stage, argv=argv
            )

        seal_path = item.controller / "gpt-freeze-authorization.json"
        frozen_path = item.controller / "gpt-frozen-manifest.json"
        seal = _load_receipt(seal_path, label="pilot controller seal")
        frozen = _load_receipt(frozen_path, label="freeze manifest")
        solver_binding = seal.get("solver")
        frozen_solver_binding = frozen.get("solver")
        expected_solver_binding = {
            "model_family": MODEL_FAMILY,
            "model_id": MODEL_ID,
            "run_id": item.run_id,
        }
        bundle_binding = seal.get("blind_bundle")
        runtime_binding = seal.get("runtime_inventory")
        dependency_binding = seal.get("dependency_inventory")
        if (
            seal.get("phase") != "freeze_authorization"
            or seal.get("freeze_scope")
            != {"kind": "pilot", "ids": [item.record_id]}
            or not isinstance(solver_binding, Mapping)
            or dict(solver_binding) != expected_solver_binding
            or not isinstance(bundle_binding, Mapping)
            or bundle_binding.get("sha256") != binding.bundle_sha256
            or bundle_binding.get("row_count") != EXPECTED_ITEM_COUNT
            or bundle_binding.get("ids") != list(binding.bundle_ids)
            or not isinstance(runtime_binding, Mapping)
            or runtime_binding.get("files_sha256")
            != binding.runtime_inventory_sha256
            or not isinstance(dependency_binding, Mapping)
            or dependency_binding.get("files_sha256")
            != binding.dependency_inventory_sha256
        ):
            raise StageError("freeze", "pilot seal scope/model binding is stale")
        controller_binding = frozen.get("controller_binding")
        records = frozen.get("records")
        seal_sha = _file_sha(seal_path)
        if (
            frozen.get("phase") != "freeze"
            or frozen.get("evaluation_mode") != "answer_blind"
            or frozen.get("official_answer_seen") is not False
            or not isinstance(frozen_solver_binding, Mapping)
            or dict(frozen_solver_binding) != expected_solver_binding
            or frozen.get("record_count") != 1
            or not isinstance(records, list)
            or len(records) != 1
            or not isinstance(records[0], Mapping)
            or records[0].get("id") != item.record_id
            or records[0].get("blind_record_sha256")
            != _canonical_sha(binding.rows[item.record_id])
            or not isinstance(controller_binding, Mapping)
            or controller_binding.get("scope_kind") != "pilot"
            or controller_binding.get("scope_ids") != [item.record_id]
            or controller_binding.get("controller_seal_sha256") != seal_sha
            or controller_binding.get("bundle_sha256") != binding.bundle_sha256
            or controller_binding.get("bundle_row_count") != EXPECTED_ITEM_COUNT
            or controller_binding.get("runtime_inventory_sha256")
            != binding.runtime_inventory_sha256
            or controller_binding.get("dependency_inventory_sha256")
            != binding.dependency_inventory_sha256
        ):
            raise StageError("freeze", "freeze manifest scope binding is stale")
        await index.update_item(
            item.record_id,
            status="succeeded",
            current_stage=None,
            controller_seal_sha256=seal_sha,
            freeze_manifest_sha256=_file_sha(frozen_path),
            error=None,
        )
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        await _record_item_failure(
            index=index, item=item, exc=exc, default_stage=current_stage
        )


async def _execute(binding: Binding, index: IndexWriter) -> None:
    """Run selected model lanes, then cross a barrier before final UID lanes.

    Structured-solver validation uses isolated ``mkdtemp`` trees and can share
    the configured UIDs.  The final verifier proves UID quiescence and may kill
    stragglers, so no final verifier starts until every solver has stopped.
    """
    semaphore = asyncio.Semaphore(binding.config.concurrency)
    solver_lane_locks = tuple(asyncio.Lock() for _lane in binding.lanes)

    async def scheduled_pre(record_id: str, ordinal: int) -> tuple[int, str, bool]:
        async with semaphore:
            lane_index = (ordinal - 1) % len(binding.lanes)
            solver_lane = binding.lanes[lane_index]
            ready = await _run_pre_verifier_item(
                binding=binding,
                item=_item_paths(binding, record_id, ordinal),
                solver_lane=solver_lane,
                solver_lane_lock=solver_lane_locks[lane_index],
                index=index,
            )
            return ordinal, record_id, ready

    pre_results = await asyncio.gather(
        *(
            scheduled_pre(record_id, ordinal)
            for ordinal, record_id in _execution_items(binding)
        )
    )

    lanes: asyncio.Queue[Lane] = asyncio.Queue()
    for lane in binding.lanes:
        lanes.put_nowait(lane)
    final_semaphore = asyncio.Semaphore(
        min(binding.config.concurrency, len(binding.lanes))
    )

    async def scheduled_post(ordinal: int, record_id: str) -> None:
        async with final_semaphore:
            lane = await lanes.get()
            try:
                await _run_post_verifier_item(
                    binding=binding,
                    item=_item_paths(binding, record_id, ordinal),
                    verifier_lane=lane,
                    index=index,
                )
            finally:
                lanes.put_nowait(lane)

    await asyncio.gather(
        *(
            scheduled_post(ordinal, record_id)
            for ordinal, record_id, ready in pre_results
            if ready
        )
    )


def _binding_drift(binding: Binding) -> str | None:
    try:
        if _file_sha(Path(__file__).resolve()) != binding.orchestrator_sha256:
            return "campaign orchestrator changed during campaign"
        bundle = binding.config.seed_workspace.joinpath(*binding.bundle_relative.parts)
        if _file_sha(bundle) != binding.bundle_sha256:
            return "full32 bundle changed during campaign"
        if (
            _hash_index(_plain_seed_inventory(binding.config.seed_workspace))
            != binding.seed_inventory_sha256
        ):
            return "prepared seed changed during campaign"
        dependency = _controller_inventory(
            binding.config.dependency_root, label="Lean dependency tree"
        )
        if _hash_index(dependency) != binding.dependency_inventory_sha256:
            return "Lean dependency tree changed during campaign"
        exclusions = (
            (binding.config.dependency_root,)
            if binding.config.dependency_root.is_relative_to(binding.config.runtime_root)
            else ()
        )
        runtime = _controller_inventory(
            binding.config.runtime_root,
            label="answer-blind runtime",
            exclude_roots=exclusions,
        )
        _assert_runtime_cache_free(binding.config.runtime_root)
        if _hash_index(runtime) != binding.runtime_inventory_sha256:
            return "answer-blind runtime changed during campaign"
        parent = binding.parent_campaign
        if parent is not None:
            retry_ids, current_parent = _load_parent_campaign(
                config=binding.config,
                bundle_ids=binding.bundle_ids,
                bundle_sha256=binding.bundle_sha256,
                campaign_root=binding.config.campaign_root,
            )
            if retry_ids != binding.ids or current_parent != parent:
                return "sealed parent campaign lineage changed during retry"
    except BaseException as exc:
        return f"campaign binding recheck failed: {exc}"
    return None


@contextlib.contextmanager
def _campaign_lock(path: Path) -> Iterable[None]:
    path = _safe_absolute(path, label="singleton lock")
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != 0
            or metadata.st_mode & 0o022
        ):
            _fail(f"campaign lock is unsafe: {path}")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise CampaignError(f"another campaign controller holds {path}") from exc
        os.ftruncate(descriptor, 0)
        os.write(descriptor, f"pid={os.getpid()} started={_utcnow()}\n".encode("ascii"))
        os.fsync(descriptor)
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _dry_run_document(binding: Binding) -> dict[str, Any]:
    items: list[dict[str, Any]] = []
    for ordinal, record_id in _execution_items(binding):
        item = _item_paths(binding, record_id, ordinal)
        lane = binding.lanes[(ordinal - 1) % len(binding.lanes)]
        items.append(
            {
                "id": record_id,
                "run_id": item.run_id,
                "workspace": str(item.workspace),
                "source_report": item.source_report_relative.as_posix(),
                "planned_solver_lane": lane.number,
                "final_verifier_lane_pool": [
                    candidate.number for candidate in binding.lanes
                ],
                "commands": [
                    {"stage": stage, "argv": argv}
                    for stage, argv in _commands(binding, item, lane)
                ],
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "mode": "dry-run",
        "would_invoke_models": False,
        "campaign_id": binding.config.campaign_id,
        "campaign_root": str(binding.config.campaign_root),
        "execution_scope": _execution_scope_document(binding),
        "parent_campaign_index": _parent_locator(binding.parent_campaign),
        "bundle_sha256": binding.bundle_sha256,
        "bundle_ids": list(binding.bundle_ids),
        "runtime_inventory_sha256": binding.runtime_inventory_sha256,
        "dependency_inventory_sha256": binding.dependency_inventory_sha256,
        "model": {"variant": VARIANT, "family": MODEL_FAMILY, "id": MODEL_ID},
        "execution": {
            "concurrency": binding.config.concurrency,
            "final_verifier_concurrency": min(
                binding.config.concurrency, len(binding.lanes)
            ),
            "singleton_lock": str(binding.config.singleton_lock),
            "lanes": [
                {
                    "number": lane.number,
                    "user": lane.user,
                    "scratch_root": str(lane.scratch_root),
                }
                for lane in binding.lanes
            ],
        },
        "item_count": len(binding.ids),
        "items": items,
    }


async def _execute_and_finalize(binding: Binding, writer: IndexWriter) -> None:
    try:
        await _execute(binding, writer)
        integrity_error = await asyncio.to_thread(_binding_drift, binding)
    except BaseException as exc:
        await writer.finalize(integrity_error=f"orchestrator failure: {exc}")
        raise
    await writer.finalize(integrity_error=integrity_error)


def _publish_index_sidecar(index_path: Path) -> Path:
    payload = index_path.read_bytes()
    sidecar = index_path.with_suffix(index_path.suffix + ".sha256")
    if sidecar.exists() or sidecar.is_symlink():
        _fail(f"campaign index sidecar already exists: {sidecar}")
    temporary = sidecar.with_name(f".{sidecar.name}.{os.getpid()}.tmp")
    descriptor = os.open(
        temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400
    )
    try:
        view = memoryview(f"{_sha(payload)}  {index_path.name}\n".encode("ascii"))
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail("short campaign index sidecar write")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    try:
        os.replace(temporary, sidecar)
        directory = os.open(sidecar.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
    return sidecar


def run_campaign(config: Config) -> int:
    binding = preflight(config)
    with _campaign_lock(binding.config.singleton_lock):
        # Recheck all absence/authority facts after acquiring the singleton lock.
        binding = preflight(config, lock_may_be_held=True)
        _mkdir_layout(binding)
        index_path = binding.config.campaign_root / "campaign-index.json"
        index_value = _initial_index(binding)
        _atomic_index(index_path, index_value)
        writer = IndexWriter(index_path, index_value)
        try:
            asyncio.run(_execute_and_finalize(binding, writer))
        except BaseException as exc:
            try:
                _publish_index_sidecar(index_path)
            except BaseException as sidecar_exc:
                exc.add_note(f"campaign index sidecar publication also failed: {sidecar_exc}")
            raise
        _publish_index_sidecar(index_path)
        return 0 if writer.value["status"] == "succeeded" else 1


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-id", required=True)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument(
        "--seed-workspace",
        type=Path,
        default=Path("/srv/icho-answer-blind-full32-v1-gpt"),
    )
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument(
        "--dependency-root",
        type=Path,
        default=Path("/opt/icho-answer-blind-runtime/lake/packages"),
    )
    parser.add_argument("--codex-home", type=Path, default=Path("/root/.codex"))
    parser.add_argument(
        "--singleton-lock", type=Path, default=DEFAULT_SINGLETON_LOCK,
        help="global lock preventing overlapping GPT full32 campaigns",
    )
    parser.add_argument(
        "--parent-campaign-index",
        type=Path,
        help=(
            "sealed terminal campaign-index.json authorizing a fresh failed-subset "
            "retry"
        ),
    )
    parser.add_argument(
        "--scope-id",
        action="append",
        help=(
            "retry one failed parent item; repeat in canonical full32 bundle order "
            "and use only with --parent-campaign-index"
        ),
    )
    parser.add_argument(
        "--verifier-user",
        action="append",
        help="repeat exactly four times; defaults to the four GPT verifier accounts",
    )
    parser.add_argument(
        "--verifier-scratch-root",
        action="append",
        type=Path,
        help="repeat exactly four times in verifier-user order",
    )
    parser.add_argument("--concurrency", type=int, default=EXPECTED_ITEM_COUNT)
    parser.add_argument("--max-attempts", type=int, default=4)
    parser.add_argument("--stage-timeout-s", type=int, default=21600)
    parser.add_argument("--verifier-timeout-s", type=int, default=3600)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--preflight", action="store_true", help="validate only; create nothing"
    )
    mode.add_argument(
        "--dry-run", action="store_true", help="print the complete plan; create nothing"
    )
    return parser


def _config(args: argparse.Namespace) -> Config:
    users = tuple(args.verifier_user or DEFAULT_VERIFIER_USERS)
    scratches = tuple(args.verifier_scratch_root or DEFAULT_VERIFIER_SCRATCH_ROOTS)
    return Config(
        campaign_id=args.campaign_id,
        campaign_root=args.campaign_root,
        seed_workspace=args.seed_workspace,
        runtime_root=args.runtime_root,
        dependency_root=args.dependency_root,
        codex_home=args.codex_home,
        singleton_lock=args.singleton_lock,
        verifier_users=users,
        verifier_scratch_roots=scratches,
        concurrency=args.concurrency,
        max_attempts=args.max_attempts,
        stage_timeout_s=args.stage_timeout_s,
        verifier_timeout_s=args.verifier_timeout_s,
        parent_campaign_index=args.parent_campaign_index,
        scope_ids=tuple(args.scope_id or ()),
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        config = _config(args)
        if args.preflight or args.dry_run:
            binding = preflight(config)
            if args.dry_run:
                output = _dry_run_document(binding)
            else:
                output = {
                    "schema_version": SCHEMA_VERSION,
                    "protocol": PROTOCOL,
                    "mode": "preflight",
                    "status": "passed",
                    "would_invoke_models": False,
                    "campaign_id": config.campaign_id,
                    "campaign_root": str(binding.config.campaign_root),
                    "execution_scope": _execution_scope_document(binding),
                    "parent_campaign_index": _parent_locator(
                        binding.parent_campaign
                    ),
                    "item_count": len(binding.ids),
                    "ids": list(binding.ids),
                    "bundle_ids": list(binding.bundle_ids),
                    "bundle_sha256": binding.bundle_sha256,
                    "seed_inventory_sha256": binding.seed_inventory_sha256,
                    "runtime_inventory_sha256": binding.runtime_inventory_sha256,
                    "dependency_inventory_sha256": binding.dependency_inventory_sha256,
                    "model": {
                        "variant": VARIANT,
                        "family": MODEL_FAMILY,
                        "id": MODEL_ID,
                    },
                    "execution": {
                        "concurrency": binding.config.concurrency,
                        "final_verifier_concurrency": min(
                            binding.config.concurrency, len(binding.lanes)
                        ),
                        "singleton_lock": str(binding.config.singleton_lock),
                        "runtime_cache_entries": 0,
                        "lanes": [
                            {
                                "number": lane.number,
                                "user": lane.user,
                                "uid": lane.uid,
                                "scratch_root": str(lane.scratch_root),
                            }
                            for lane in binding.lanes
                        ],
                    },
                }
            sys.stdout.buffer.write(_json_bytes(output, pretty=True))
            return 0
        return run_campaign(config)
    except CampaignError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
