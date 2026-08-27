#!/usr/bin/env python3
"""Atomic, fail-closed handoff from the stopped width-10 batch.

This module deliberately separates durable evidence from launch authority.
Every JSON document emitted here has ``launch_authorized == false``.  The only
object that may authorize a launch is an in-memory :class:`AtomicSwitchLease`.
The lease owns all legacy coordination locks until four new workers have been
started, fenced, and recorded in one batch-wide handoff commit.

The legacy coordinator and child runner are executed from the exact source
bytes named by the old batch manifest.  The loader compiles those bytes
directly and never asks Python to execute a ``.pyc``.  It also does not spawn a
Python worker, so a project-local ``sitecustomize.py`` cannot run between lock
acquisition and replay.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import importlib
import importlib.abc
import importlib.util
import json
import math
import os
import stat
import sys
import threading
import types
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 2
LANE_COUNT = 4
SWITCH_KIND = "paper400-dic5-adaptive-switch-evidence-v2"
SWITCH_GATE = "paper400-dic5-adaptive-switch-evidence-v2"
LANE_KIND = "paper400-dic5-adaptive-switch-lane-v2"
STRUCTURAL_KIND = "paper400-dic5-adaptive-switch-structural-check-v2"
HANDOFF_KIND = "paper400-dic5-adaptive-batch-handoff-v2"
HANDOFF_VERIFY_KIND = "paper400-dic5-adaptive-batch-handoff-check-v2"
HANDOFF_COMMIT = Path("adaptive-handoff-v2.json")

COORDINATOR_RELATIVE = Path(
    "scripts/run_paper400_dic5_nested_width10_four_lane_v1.py"
)
CHILD_RUNNER_RELATIVE = Path(
    "scripts/run_paper400_dic5_nested_width10_child_resume_proof_v1.py"
)
OVERLAY_RELATIVE = Path(
    "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
)
BATCH_RELATIVE = Path("batch.json")
STATIC_COMMIT_RELATIVE = Path("state/00-resume-static.json")
SESSION_RELATIVE = Path("state/11-session.json")
BATCH_LOCK = Path(".batch.lock")
LANE_LOCK = Path(".hierarchical-resume.lock")
CONTROLLER_LOCK = Path("runtime/dmtcp/.controller.lock")
OLD_TERMINAL_CLAIM = Path("state/20-proof-harvest.claim")
OLD_FINAL_COMMIT = Path("COMMIT.json")

MAX_JSON_BYTES = 256 << 20
MAX_SOURCE_BYTES = 16 << 20
HASH_CHUNK_BYTES = 1 << 20

SWITCH_FIELDS = frozenset({
    "schema_version", "kind", "gate", "authority", "test_only",
    "production_eligible", "authenticated", "launch_authorized",
    "scientific_claim", "root", "root_identity",
    "batch_manifest_sha256", "width10_campaign_sha256",
    "width6_campaign_sha256", "parent_manifest_sha256",
    "observation_policy", "action_history", "lanes", "source_binding",
    "claim_scope", "record_sha256",
})

LANE_FIELDS = frozenset({
    "schema_version", "kind", "lane_index", "cpu", "global_leaf_index",
    "global_leaf_id", "leaf_sha256", "child_cnf_sha256",
    "child_dimacs_sha256", "combined_unit_clauses_sha256", "child_root",
    "child_root_identity", "resume_static_sha256", "session_sha256",
    "checkpoint_stop_lane_outcome_sha256", "transport_chain",
    "transport_chain_sha256", "controller_inspection",
    "latest_checkpoint_sha256", "checkpoint_proof_prefix",
    "checkpoint_proof_physical", "hard_evidence", "hard_evidence_sha256",
    "solver_stopped", "terminal_claimed", "terminal_committed",
    "hardness_only", "solver_terminal_claim", "lane_record_sha256",
})

HANDOFF_FIELDS = frozenset({
    "schema_version", "kind", "gate", "test_only", "production_eligible",
    "authenticated", "launch_authorized", "scientific_claim",
    "historical_atomic_handoff_observed", "batch_root", "batch_root_identity",
    "batch_manifest_sha256", "switch_evidence_sha256", "source_binding",
    "retired_locks", "root_bindings", "fence_sha256s", "root_link_policy",
    "claim_scope", "record_sha256",
})


class AdaptiveSwitchEvidenceV2Error(RuntimeError):
    """A source, lock, replay, target, fence, or handoff invariant failed."""


def _strict_json(value: Any, *, label: str = "value") -> None:
    kind = type(value)
    if value is None or kind in (str, bool, int):
        return
    if kind is float:
        if not math.isfinite(value):
            raise AdaptiveSwitchEvidenceV2Error(f"{label} is non-finite")
        return
    if kind is list:
        for index, item in enumerate(value):
            _strict_json(item, label=f"{label}[{index}]")
        return
    if kind is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise AdaptiveSwitchEvidenceV2Error(
                    f"{label} contains a non-string key"
                )
            _strict_json(item, label=f"{label}.{key}")
        return
    raise AdaptiveSwitchEvidenceV2Error(
        f"{label} contains non-JSON type {kind.__name__}"
    )


def canonical_bytes(value: Any) -> bytes:
    _strict_json(value)
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise AdaptiveSwitchEvidenceV2Error("canonical JSON encoding failed") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise AdaptiveSwitchEvidenceV2Error("seal requires a plain unsealed object")
    result = dict(value)
    result[field] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def _require_sha256(value: Any, *, label: str) -> str:
    if not _is_sha256(value):
        raise AdaptiveSwitchEvidenceV2Error(f"{label} is not a SHA-256")
    return value


def selfhash_valid(value: Any, field: str = "record_sha256") -> bool:
    if type(value) is not dict or not _is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    expected = unsigned.pop(field)
    try:
        return expected == canonical_sha256(unsigned)
    except AdaptiveSwitchEvidenceV2Error:
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            json_type_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(a, b)
            for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def _stat_identity(info: os.stat_result) -> dict[str, int]:
    return {
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": int(stat.S_IMODE(info.st_mode)), "uid": int(info.st_uid),
        "gid": int(info.st_gid), "links": int(info.st_nlink),
        "bytes": int(info.st_size), "mtime_ns": int(info.st_mtime_ns),
        "ctime_ns": int(info.st_ctime_ns),
    }


def _root_identity(root: Path) -> dict[str, Any]:
    target = Path(root)
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise AdaptiveSwitchEvidenceV2Error("cannot resolve owned root") from exc
    if (
        not target.is_absolute() or str(target) != os.path.abspath(str(target))
        or resolved != target or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode) or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV2Error(
            "root must be canonical, owned, plain, and mode-0700"
        )
    return {
        "path": str(target), "device": int(lexical.st_dev),
        "inode": int(lexical.st_ino), "uid": int(lexical.st_uid),
        "mode": int(stat.S_IMODE(lexical.st_mode)),
    }


def _stable_bytes(
    path: Path, *, cap: int, require_owned: bool = True,
) -> tuple[bytes, dict[str, int]]:
    candidate = Path(path)
    try:
        lexical = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise AdaptiveSwitchEvidenceV2Error(f"cannot resolve {candidate}") from exc
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_nlink != 1
        or (require_owned and lexical.st_uid != os.geteuid())
        or lexical.st_size > cap
    ):
        raise AdaptiveSwitchEvidenceV2Error(f"unsafe or oversized file: {candidate}")
    fd = os.open(resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    observed = 0
    try:
        before = os.fstat(fd)
        if _stat_identity(before) != _stat_identity(lexical):
            raise AdaptiveSwitchEvidenceV2Error("file changed before open")
        while True:
            chunk = os.read(fd, min(HASH_CHUNK_BYTES, cap + 1 - observed))
            if not chunk:
                break
            chunks.append(chunk)
            observed += len(chunk)
            if observed > cap:
                raise AdaptiveSwitchEvidenceV2Error("file exceeded cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if _stat_identity(before) != _stat_identity(after) or observed != before.st_size:
        raise AdaptiveSwitchEvidenceV2Error("file changed while reading")
    return b"".join(chunks), _stat_identity(before)


def _read_json(path: Path, *, cap: int = MAX_JSON_BYTES) -> dict[str, Any]:
    payload, _ = _stable_bytes(path, cap=cap)
    try:
        value = json.loads(payload)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise AdaptiveSwitchEvidenceV2Error(f"invalid JSON: {path}") from exc
    if type(value) is not dict:
        raise AdaptiveSwitchEvidenceV2Error("JSON record is not a plain object")
    _strict_json(value)
    if payload not in {canonical_bytes(value), canonical_bytes(value) + b"\n"}:
        raise AdaptiveSwitchEvidenceV2Error("JSON bytes are not canonical")
    return value


def _safe_relative(project: Path, relative: str) -> Path:
    if type(relative) is not str:
        raise AdaptiveSwitchEvidenceV2Error("source path is not a string")
    pure = PurePosixPath(relative)
    if pure.is_absolute() or not pure.parts or any(
        part in {"", ".", ".."} for part in pure.parts
    ):
        raise AdaptiveSwitchEvidenceV2Error("source path is not canonical relative")
    path = project.joinpath(*pure.parts)
    try:
        resolved = path.resolve(strict=True)
        base = project.resolve(strict=True)
        resolved.relative_to(base)
    except (FileNotFoundError, OSError, RuntimeError, ValueError) as exc:
        raise AdaptiveSwitchEvidenceV2Error("source escapes project") from exc
    if resolved != path or path.is_symlink():
        raise AdaptiveSwitchEvidenceV2Error("source path is aliased")
    return path


def _record_by_role(batch: Mapping[str, Any], role: str) -> dict[str, Any]:
    binding = batch.get("source_binding")
    sources = binding.get("sources") if type(binding) is dict else None
    matches = [
        item for item in sources or []
        if type(item) is dict and item.get("role") == role
    ]
    if len(matches) != 1:
        raise AdaptiveSwitchEvidenceV2Error(f"missing/duplicate source role {role}")
    record = matches[0]
    if set(record) != {"role", "relative_path", "sha256"}:
        raise AdaptiveSwitchEvidenceV2Error("legacy source record field mismatch")
    _require_sha256(record.get("sha256"), label=f"{role} source")
    return dict(record)


def _module_name(relative: str) -> str:
    pure = PurePosixPath(relative)
    if pure.suffix != ".py":
        raise AdaptiveSwitchEvidenceV2Error("bound Python source lacks .py suffix")
    return ".".join(pure.with_suffix("").parts)


def _discover_sources(
    root: Path, *, expected_batch_manifest_sha256: str | None,
) -> dict[str, Any]:
    target = Path(root)
    root_id = _root_identity(target)
    batch = _read_json(target / BATCH_RELATIVE)
    if not selfhash_valid(batch):
        raise AdaptiveSwitchEvidenceV2Error("batch self-hash mismatch")
    if expected_batch_manifest_sha256 is not None:
        pin = _require_sha256(
            expected_batch_manifest_sha256, label="batch manifest pin"
        )
        if batch.get("record_sha256") != pin:
            raise AdaptiveSwitchEvidenceV2Error("batch misses external pin")
    if (
        batch.get("root") != str(target)
        or not json_type_equal(batch.get("root_identity"), root_id)
    ):
        raise AdaptiveSwitchEvidenceV2Error("batch binds another root")
    lanes = batch.get("lanes")
    if type(lanes) is not list or len(lanes) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("batch must contain four lanes")
    coordinator_record = _record_by_role(batch, "four_lane_coordinator_source")
    child_record = _record_by_role(batch, "nested_width10_child_runner_source")
    coordinator_paths: set[str] = set()
    child_hashes: set[str] = set()
    for index, lane in enumerate(lanes):
        lane_root = target / "lanes" / f"lane-{index}"
        if (
            type(lane) is not dict or lane.get("lane_index") != index
            or lane.get("child_root") != str(lane_root)
        ):
            raise AdaptiveSwitchEvidenceV2Error("batch lane table was substituted")
        static_record = _read_json(lane_root / STATIC_COMMIT_RELATIVE)
        session = _read_json(lane_root / SESSION_RELATIVE)
        tool = static_record.get("toolchain_binding", {}).get("tools", {}).get(
            "four_lane_coordinator_source"
        )
        execution = session.get("execution_source_binding")
        if (
            type(tool) is not dict or type(tool.get("path")) is not str
            or not _is_sha256(tool.get("sha256"))
            or type(execution) is not dict
            or not _is_sha256(execution.get("runner_source_sha256"))
        ):
            raise AdaptiveSwitchEvidenceV2Error("lane source binding is malformed")
        coordinator_paths.add(tool["path"])
        child_hashes.add(execution["runner_source_sha256"])
    if len(coordinator_paths) != 1 or len(child_hashes) != 1:
        raise AdaptiveSwitchEvidenceV2Error("lanes disagree on source identity")
    coordinator_path = Path(next(iter(coordinator_paths)))
    if not coordinator_path.is_absolute() or coordinator_path.name != COORDINATOR_RELATIVE.name:
        raise AdaptiveSwitchEvidenceV2Error("legacy coordinator path malformed")
    legacy_project = coordinator_path.parent.parent
    if legacy_project.resolve(strict=True) != legacy_project or legacy_project.is_symlink():
        raise AdaptiveSwitchEvidenceV2Error("legacy project is aliased")
    if coordinator_path != _safe_relative(
        legacy_project, coordinator_record["relative_path"]
    ):
        raise AdaptiveSwitchEvidenceV2Error("coordinator path/batch mismatch")
    if child_record["sha256"] != next(iter(child_hashes)):
        raise AdaptiveSwitchEvidenceV2Error("child source/session mismatch")
    if _safe_relative(legacy_project, child_record["relative_path"]) != (
        legacy_project / CHILD_RUNNER_RELATIVE
    ):
        raise AdaptiveSwitchEvidenceV2Error("child source path mismatch")
    binding = batch.get("source_binding")
    if type(binding) is not dict or not selfhash_valid(binding):
        raise AdaptiveSwitchEvidenceV2Error("batch source binding self-hash mismatch")
    sources = binding.get("sources")
    if type(sources) is not list:
        raise AdaptiveSwitchEvidenceV2Error("batch source list malformed")
    payloads: dict[str, tuple[Path, bytes, str]] = {}
    records: list[dict[str, Any]] = []
    roles: set[str] = set()
    modules: set[str] = set()
    for item in sources:
        if type(item) is not dict or set(item) != {"role", "relative_path", "sha256"}:
            raise AdaptiveSwitchEvidenceV2Error("legacy source entry malformed")
        role = item.get("role")
        digest = _require_sha256(item.get("sha256"), label="legacy source hash")
        if type(role) is not str or role in roles:
            raise AdaptiveSwitchEvidenceV2Error("legacy source roles are invalid")
        path = _safe_relative(legacy_project, item["relative_path"])
        payload, _ = _stable_bytes(path, cap=MAX_SOURCE_BYTES, require_owned=False)
        if hashlib.sha256(payload).hexdigest() != digest:
            raise AdaptiveSwitchEvidenceV2Error(f"legacy source changed: {role}")
        module = _module_name(item["relative_path"])
        if module in modules:
            raise AdaptiveSwitchEvidenceV2Error("duplicate legacy module binding")
        payloads[module] = (path, payload, digest)
        roles.add(role)
        modules.add(module)
        records.append(dict(item))
    return {
        "root_identity": root_id, "batch": batch,
        "legacy_project": legacy_project, "legacy_sources": records,
        "source_payloads": payloads,
        "coordinator_module": _module_name(coordinator_record["relative_path"]),
        "child_module": _module_name(child_record["relative_path"]),
    }


_SOURCE_LOAD_GUARD = threading.RLock()


class _SourceBytesLoader(importlib.abc.Loader):
    def __init__(
        self, fullname: str, path: Path, payload: bytes,
        observed: dict[str, dict[str, Any]], *, externally_bound: bool,
    ) -> None:
        self.fullname = fullname
        self.path = path
        self.payload = payload
        self.observed = observed
        self.externally_bound = externally_bound

    def create_module(self, spec: Any) -> types.ModuleType | None:
        return None

    def exec_module(self, module: types.ModuleType) -> None:
        spec = getattr(module, "__spec__", None)
        expected_path = str(self.path)
        expected_package = self.fullname.rpartition(".")[0]
        if (
            spec is None or getattr(spec, "name", None) != self.fullname
            or getattr(spec, "loader", None) is not self
            or getattr(spec, "origin", None) != expected_path
            or getattr(module, "__name__", None) != self.fullname
            or getattr(module, "__loader__", None) is not self
            or getattr(module, "__package__", None) != expected_package
        ):
            raise AdaptiveSwitchEvidenceV2Error(
                "exact source module specification mismatch"
            )
        # ``spec_from_loader`` cannot infer a location from this byte-only
        # loader.  Bind the externally discovered source path before the
        # module executes so legacy code may safely derive PROJECT from
        # ``__file__``.  No bytecode is loaded or written by this loader.
        module.__file__ = expected_path
        module.__cached__ = None
        digest = hashlib.sha256(self.payload).hexdigest()
        self.observed[self.fullname] = {
            "module": self.fullname, "path": str(self.path),
            "sha256": digest, "bytes": len(self.payload),
            "externally_bound": self.externally_bound,
            "execution": "compile-exact-source-bytes-v2",
        }
        code = compile(self.payload, str(self.path), "exec", dont_inherit=True)
        exec(code, module.__dict__)
        if (
            module.__dict__.get("__file__") != expected_path
            or module.__dict__.get("__cached__", object()) is not None
        ):
            raise AdaptiveSwitchEvidenceV2Error(
                "exact source module location binding changed during execution"
            )


class _SourceOnlyFinder(importlib.abc.MetaPathFinder):
    def __init__(
        self, project: Path, bound: Mapping[str, tuple[Path, bytes, str]],
    ) -> None:
        self.project = project
        self.bound = dict(bound)
        self.observed: dict[str, dict[str, Any]] = {}

    def find_spec(
        self, fullname: str, path: Sequence[str] | None = None,
        target: types.ModuleType | None = None,
    ) -> Any:
        del path, target
        if fullname in {"sitecustomize", "usercustomize"}:
            raise AdaptiveSwitchEvidenceV2Error(
                "custom Python startup modules are forbidden"
            )
        record = self.bound.get(fullname)
        if record is not None:
            source_path, payload, digest = record
            if hashlib.sha256(payload).hexdigest() != digest:
                raise AdaptiveSwitchEvidenceV2Error("bound source payload drift")
            loader = _SourceBytesLoader(
                fullname, source_path, payload, self.observed,
                externally_bound=True,
            )
            return importlib.util.spec_from_loader(fullname, loader, origin=str(source_path))
        parts = fullname.split(".")
        if not parts or parts[0] not in {"scripts", "investigations", "evaluation"}:
            return None
        source_path = self.project.joinpath(*parts).with_suffix(".py")
        try:
            source_path.resolve(strict=True).relative_to(self.project)
        except (FileNotFoundError, OSError, RuntimeError, ValueError):
            return None
        payload, _ = _stable_bytes(
            source_path, cap=MAX_SOURCE_BYTES, require_owned=False
        )
        loader = _SourceBytesLoader(
            fullname, source_path, payload, self.observed,
            externally_bound=False,
        )
        return importlib.util.spec_from_loader(fullname, loader, origin=str(source_path))


def _load_exact_modules(discovery: Mapping[str, Any]) -> tuple[Any, Any, list[dict[str, Any]]]:
    project = discovery["legacy_project"]
    finder = _SourceOnlyFinder(project, discovery["source_payloads"])
    coordinator_name = discovery["coordinator_module"]
    child_name = discovery["child_module"]
    with _SOURCE_LOAD_GUARD:
        before_modules = dict(sys.modules)
        before_meta = list(sys.meta_path)
        try:
            for name, module in list(sys.modules.items()):
                if name == __name__:
                    continue
                filename = getattr(module, "__file__", None)
                if type(filename) is not str:
                    continue
                try:
                    Path(filename).resolve(strict=True).relative_to(project)
                except (FileNotFoundError, OSError, RuntimeError, ValueError):
                    continue
                sys.modules.pop(name, None)
            sys.meta_path.insert(0, finder)
            coordinator = importlib.import_module(coordinator_name)
            child = sys.modules.get(child_name)
            if child is None or getattr(coordinator, "child_runner", None) is not child:
                raise AdaptiveSwitchEvidenceV2Error("coordinator did not use exact child")
            for required in (coordinator_name, child_name):
                observed = finder.observed.get(required)
                bound = discovery["source_payloads"].get(required)
                if observed is None or bound is None or observed["sha256"] != bound[2]:
                    raise AdaptiveSwitchEvidenceV2Error(
                        f"exact source was not executed: {required}"
                    )
            loaded = [finder.observed[key] for key in sorted(finder.observed)]
            return coordinator, child, loaded
        finally:
            sys.meta_path[:] = before_meta
            for name in list(sys.modules):
                if name not in before_modules:
                    module = sys.modules.get(name)
                    filename = getattr(module, "__file__", None)
                    if type(filename) is str:
                        with contextlib.suppress(Exception):
                            Path(filename).resolve(strict=True).relative_to(project)
                            sys.modules.pop(name, None)
            for name, module in before_modules.items():
                sys.modules[name] = module


def _load_overlay_exact() -> tuple[Any, dict[str, Any], list[dict[str, Any]]]:
    path = (PROJECT / OVERLAY_RELATIVE).resolve(strict=True)
    payload, _ = _stable_bytes(path, cap=MAX_SOURCE_BYTES, require_owned=False)
    digest = hashlib.sha256(payload).hexdigest()
    discovery = {
        "legacy_project": PROJECT,
        "source_payloads": {
            _module_name(OVERLAY_RELATIVE.as_posix()): (path, payload, digest),
        },
        "coordinator_module": _module_name(OVERLAY_RELATIVE.as_posix()),
        "child_module": _module_name(OVERLAY_RELATIVE.as_posix()),
    }
    finder = _SourceOnlyFinder(PROJECT, discovery["source_payloads"])
    name = discovery["coordinator_module"]
    with _SOURCE_LOAD_GUARD:
        before_modules = dict(sys.modules)
        before_meta = list(sys.meta_path)
        try:
            for module_name, module in list(sys.modules.items()):
                if module_name == __name__:
                    continue
                filename = getattr(module, "__file__", None)
                if type(filename) is not str:
                    continue
                try:
                    Path(filename).resolve(strict=True).relative_to(PROJECT)
                except (FileNotFoundError, OSError, RuntimeError, ValueError):
                    continue
                if module_name.startswith(("investigations.", "scripts.", "evaluation.")):
                    sys.modules.pop(module_name, None)
            sys.meta_path.insert(0, finder)
            overlay = importlib.import_module(name)
            observed = finder.observed.get(name)
            if observed is None or observed["sha256"] != digest:
                raise AdaptiveSwitchEvidenceV2Error("overlay source bytes were not executed")
            return overlay, {
                "role": "adaptive_leaf_overlay_v2_source",
                "relative_path": OVERLAY_RELATIVE.as_posix(),
                "sha256": digest,
            }, [finder.observed[key] for key in sorted(finder.observed)]
        finally:
            sys.meta_path[:] = before_meta
            for module_name in list(sys.modules):
                if module_name not in before_modules:
                    module = sys.modules.get(module_name)
                    filename = getattr(module, "__file__", None)
                    if type(filename) is str:
                        with contextlib.suppress(Exception):
                            Path(filename).resolve(strict=True).relative_to(PROJECT)
                            sys.modules.pop(module_name, None)
            for module_name, module in before_modules.items():
                sys.modules[module_name] = module


class _HeldLock:
    __slots__ = ("fd", "role", "original_path", "current_path", "identity", "operation")

    def __init__(self, path: Path, role: str, operation: int) -> None:
        self.role = role
        self.original_path = Path(path)
        self.current_path = Path(path)
        self.operation = operation
        try:
            lexical = self.original_path.lstat()
        except OSError as exc:
            raise AdaptiveSwitchEvidenceV2Error(f"missing lock: {role}") from exc
        if (
            stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
            or lexical.st_uid != os.geteuid() or stat.S_IMODE(lexical.st_mode) != 0o600
            or lexical.st_nlink != 1 or lexical.st_size != 0
        ):
            raise AdaptiveSwitchEvidenceV2Error(f"unsafe lock file: {role}")
        self.fd = os.open(
            self.original_path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW
        )
        observed = os.fstat(self.fd)
        if _stat_identity(observed) != _stat_identity(lexical):
            os.close(self.fd)
            raise AdaptiveSwitchEvidenceV2Error(f"lock changed before open: {role}")
        self.identity = _stat_identity(observed)
        try:
            fcntl.flock(self.fd, operation | fcntl.LOCK_NB)
        except BaseException:
            os.close(self.fd)
            raise

    def retire(self, suffix: str) -> dict[str, Any]:
        if self.current_path != self.original_path:
            raise AdaptiveSwitchEvidenceV2Error("lock was already retired")
        current = self.original_path.lstat()
        if _stat_identity(current) != self.identity or _stat_identity(os.fstat(self.fd)) != self.identity:
            raise AdaptiveSwitchEvidenceV2Error("held lock identity changed")
        retired = self.original_path.with_name(
            self.original_path.name + f".retired-v2-{suffix}"
        )
        if retired.exists() or retired.is_symlink():
            raise AdaptiveSwitchEvidenceV2Error("retired lock target exists")
        os.rename(self.original_path, retired)
        directory = os.open(
            retired.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
        )
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
        self.current_path = retired
        # rename(2) may update ctime; bind the post-rename inode state.
        self.identity = _stat_identity(os.fstat(self.fd))
        return {
            "role": self.role, "original_path": str(self.original_path),
            "retired_path": str(retired), "identity": dict(self.identity),
        }

    def restore(self) -> None:
        if self.current_path == self.original_path:
            return
        if self.original_path.exists() or self.original_path.is_symlink():
            raise AdaptiveSwitchEvidenceV2Error("cannot restore occupied lock path")
        os.rename(self.current_path, self.original_path)
        directory = os.open(
            self.original_path.parent,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
        self.current_path = self.original_path

    def close(self) -> None:
        if self.fd < 0:
            return
        with contextlib.suppress(OSError):
            fcntl.flock(self.fd, fcntl.LOCK_UN)
        os.close(self.fd)
        self.fd = -1


def _acquire_all_locks(root: Path) -> tuple[list[_HeldLock], dict[str, Any]]:
    locks: list[_HeldLock] = []
    try:
        locks.append(_HeldLock(root / BATCH_LOCK, "batch", fcntl.LOCK_EX))
        discovery = _discover_sources(root, expected_batch_manifest_sha256=None)
        for index in range(LANE_COUNT):
            lane_root = root / "lanes" / f"lane-{index}"
            locks.append(_HeldLock(
                lane_root / LANE_LOCK, f"lane-{index}", fcntl.LOCK_EX
            ))
        for index in range(LANE_COUNT):
            lane_root = root / "lanes" / f"lane-{index}"
            # A shared controller lock blocks start/checkpoint/resume (exclusive)
            # while remaining compatible with controller.inspect(verify_hashes=True).
            locks.append(_HeldLock(
                lane_root / CONTROLLER_LOCK, f"controller-{index}", fcntl.LOCK_SH
            ))
        return locks, discovery
    except BaseException:
        for held in reversed(locks):
            held.close()
        raise


def _manifest_hash(value: Any, field: str, *, label: str) -> str:
    if type(value) is not dict:
        raise AdaptiveSwitchEvidenceV2Error(f"{label} is not an object")
    return _require_sha256(value.get(field), label=f"{label} hash")


def _strict_bool(value: Any, expected: bool, *, label: str) -> None:
    if type(value) is not bool or value is not expected:
        raise AdaptiveSwitchEvidenceV2Error(f"{label} mismatch")


def _snapshot_locked(root: Path, coordinator: Any, child: Any) -> dict[str, Any]:
    loaded = coordinator._load_batch(root, instance=None, strict_base=True)
    manifest = loaded.get("manifest")
    if type(manifest) is not dict:
        raise AdaptiveSwitchEvidenceV2Error("legacy replay returned no batch")
    completed, incomplete = coordinator._action_directories(root, manifest)
    if incomplete is not None or type(completed) is not list or not completed:
        raise AdaptiveSwitchEvidenceV2Error("legacy action history is incomplete/empty")
    previous: str | None = None
    actions: list[dict[str, Any]] = []
    latest_claim: dict[str, Any] | None = None
    latest_outcomes: list[dict[str, Any]] | None = None
    latest_result: dict[str, Any] | None = None
    for sequence, action_dir in enumerate(completed):
        claim = coordinator._read_action_claim(
            action_dir / "claim.json", root=root, manifest=manifest,
            sequence=sequence, previous_sha=previous,
        )
        outcomes = [
            coordinator._read_lane_outcome(
                action_dir / f"lane-{lane['lane_index']}.json",
                lane=lane, action=claim["action"], sequence=sequence,
                claim_sha256=claim["record_sha256"],
            )
            for lane in manifest["lanes"]
        ]
        result = coordinator._read_action_result(
            action_dir / "result.json", root=root, manifest=manifest,
            claim=claim, outcomes=outcomes,
        )
        actions.append({
            "sequence": sequence, "action": claim["action"],
            "claim_sha256": claim["record_sha256"],
            "result_sha256": result["record_sha256"],
            "lane_outcome_sha256s": [item["record_sha256"] for item in outcomes],
        })
        previous = result["record_sha256"]
        latest_claim, latest_outcomes, latest_result = claim, outcomes, result
    assert latest_claim is not None and latest_outcomes is not None and latest_result is not None
    if latest_claim.get("action") != "checkpoint-stop":
        raise AdaptiveSwitchEvidenceV2Error("latest action is not checkpoint-stop")
    _strict_bool(latest_result.get("all_lanes_succeeded"), True, label="batch success")
    _strict_bool(
        latest_result.get("all_lanes_goal_satisfied"), True, label="batch goal"
    )
    if latest_result.get("goal_satisfied_lane_count") != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("not all checkpoint goals were satisfied")
    runtime_lanes: list[dict[str, Any]] = []
    for index, lane in enumerate(manifest["lanes"]):
        outcome = latest_outcomes[index]
        if (
            type(lane) is not dict or lane.get("lane_index") != index
            or type(outcome) is not dict or outcome.get("lane_index") != index
            or outcome.get("action") != "checkpoint-stop"
            or outcome.get("transport_state_after") != "CHECKPOINTED"
            or outcome.get("child_result_state") != "CHECKPOINTED"
        ):
            raise AdaptiveSwitchEvidenceV2Error("checkpoint lane outcome mismatch")
        _strict_bool(outcome.get("success"), True, label=f"lane {index} success")
        _strict_bool(outcome.get("goal_satisfied"), True, label=f"lane {index} goal")
        _strict_bool(
            outcome.get("terminal_claimed_after"), False,
            label=f"lane {index} terminal claim",
        )
        _strict_bool(
            outcome.get("terminal_committed_after"), False,
            label=f"lane {index} terminal commit",
        )
        lane_root = root / "lanes" / f"lane-{index}"
        if lane.get("child_root") != str(lane_root):
            raise AdaptiveSwitchEvidenceV2Error("lane root mismatch")
        checked = child._action_static_kwargs(lane_root, loaded["static_kwargs"])
        child_loaded, session = child._load_session(lane_root, **checked)
        caps = child_loaded["record"]["resource_policy"]
        chain = child.validate_transport_chain(
            lane_root, session, caps,
            requirement=child.CHAIN_REQUIRE_CHECKPOINTED,
        )
        repeat = child.validate_transport_chain(
            lane_root, session, caps,
            requirement=child.CHAIN_REQUIRE_CHECKPOINTED,
        )
        if not json_type_equal(chain, repeat):
            raise AdaptiveSwitchEvidenceV2Error("transport changed during replay")
        with child._fixed_environment():
            inspection = child.controller.inspect(
                lane_root / child.RUNTIME_ROOT, verify_hashes=True
            )
        generations = chain.get("generations")
        inspect_generations = inspection.get("generations")
        if (
            chain.get("state") != "CHECKPOINTED"
            or type(generations) is not list or not generations
            or generations[-1].get("pid_identity_alive") is not False
            or chain.get("writable_holders") != []
            or not _is_sha256(chain.get("latest_checkpoint_sha256"))
            or type(chain.get("latest_proof_prefix")) is not dict
            or type(chain.get("latest_proof_physical")) is not dict
            or inspection.get("state") != "CHECKPOINTED"
            or inspection.get("hash_verification_requested") is not True
            or type(inspect_generations) is not list or not inspect_generations
            or inspect_generations[-1].get("pid_identity_alive") is not False
            or inspect_generations[-1].get("checkpoint_hashes_valid") is not True
        ):
            raise AdaptiveSwitchEvidenceV2Error("lane is not a verified stopped checkpoint")
        bound_chain = outcome.get("child_result")
        if type(bound_chain) is dict and type(bound_chain.get("chain")) is dict:
            bound_chain = bound_chain["chain"]
        if type(bound_chain) is not dict or not json_type_equal(bound_chain, chain):
            raise AdaptiveSwitchEvidenceV2Error("action result misses fresh chain")
        if (lane_root / OLD_TERMINAL_CLAIM).exists() or (lane_root / OLD_FINAL_COMMIT).exists():
            raise AdaptiveSwitchEvidenceV2Error("old lane entered terminal proof stage")
        static_record = child_loaded.get("record")
        if (
            type(static_record) is not dict
            or static_record.get("record_sha256") != lane.get("resume_static_sha256")
            or session.get("resume_static_sha256") != lane.get("resume_static_sha256")
            or session.get("root") != str(lane_root)
        ):
            raise AdaptiveSwitchEvidenceV2Error("lane static/session mismatch")
        runtime_lanes.append({
            "lane": dict(lane), "root_identity": child._root_identity(lane_root),
            "static": static_record, "session": session, "chain": chain,
            "inspection": inspection, "outcome": outcome,
        })
    return {
        "manifest": manifest, "parent": loaded["parent"],
        "width6_campaign": loaded["width6_campaign"],
        "width10_campaign": loaded["campaign"], "actions": actions,
        "checkpoint_claim": latest_claim, "checkpoint_result": latest_result,
        "lanes": runtime_lanes,
    }


def _observation_policy(
    timeout_seconds: float, elapsed_seconds_by_lane: Sequence[float],
) -> dict[str, Any]:
    if type(timeout_seconds) is not float or not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise AdaptiveSwitchEvidenceV2Error("timeout annotation must be positive float")
    if (
        type(elapsed_seconds_by_lane) is not list
        or len(elapsed_seconds_by_lane) != LANE_COUNT
        or any(
            type(item) is not float or not math.isfinite(item) or item < 0
            for item in elapsed_seconds_by_lane
        )
    ):
        raise AdaptiveSwitchEvidenceV2Error("elapsed annotation must be four floats")
    return {
        "status": "UNKNOWN", "timeout_seconds": timeout_seconds,
        "elapsed_seconds_by_lane": list(elapsed_seconds_by_lane),
        "annotation_source": "operator-annotation-not-solver-result-v2",
        "timed_out": False, "hardness_only": True,
    }


def _source_binding(
    discovery: Mapping[str, Any], legacy_executed: Sequence[Mapping[str, Any]],
    overlay_record: Mapping[str, Any], overlay_executed: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    switch_path = Path(__file__).resolve(strict=True)
    payload, _ = _stable_bytes(switch_path, cap=MAX_SOURCE_BYTES, require_owned=False)
    current = [
        {
            "role": "adaptive_switch_evidence_v2_source",
            "relative_path": switch_path.relative_to(PROJECT).as_posix(),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        dict(overlay_record),
    ]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "manifest-pinned-source-bytes-compile-exec-no-pyc-v2",
        "legacy_project": str(discovery["legacy_project"]),
        "legacy_sources": list(discovery["legacy_sources"]),
        "legacy_executed_source_closure": [dict(item) for item in legacy_executed],
        "current_sources": current,
        "overlay_executed_source_closure": [dict(item) for item in overlay_executed],
        "sitecustomize_imported_by_loader": False,
        "pyc_executed_by_loader": False,
    }, "source_binding_sha256")


def _build_record(
    root: Path, snapshot: Mapping[str, Any], discovery: Mapping[str, Any],
    overlay: Any, legacy_executed: Sequence[Mapping[str, Any]],
    overlay_record: Mapping[str, Any], overlay_executed: Sequence[Mapping[str, Any]],
    *, timeout_seconds: float, elapsed_seconds_by_lane: Sequence[float],
) -> dict[str, Any]:
    manifest = snapshot["manifest"]
    width10 = snapshot["width10_campaign"]
    width6 = snapshot["width6_campaign"]
    parent = snapshot["parent"]
    policy = _observation_policy(timeout_seconds, elapsed_seconds_by_lane)
    width10_sha = _manifest_hash(width10, "manifest_sha256", label="width10")
    width6_sha = _manifest_hash(width6, "manifest_sha256", label="width6")
    parent_sha = _manifest_hash(parent, "manifest_sha256", label="parent")
    leaves = width10.get("leaves")
    if type(leaves) is not list:
        raise AdaptiveSwitchEvidenceV2Error("width10 leaf table malformed")
    lane_records: list[dict[str, Any]] = []
    for index, runtime in enumerate(snapshot["lanes"]):
        lane = runtime["lane"]
        outcome = runtime["outcome"]
        session = runtime["session"]
        chain = runtime["chain"]
        global_index = lane.get("global_leaf_index")
        if type(global_index) is not int or not 0 <= global_index < len(leaves):
            raise AdaptiveSwitchEvidenceV2Error("global leaf index malformed")
        leaf = leaves[global_index]
        if any(lane.get(field) != leaf.get(field) for field in (
            "leaf_sha256", "child_dimacs_sha256",
        )):
            raise AdaptiveSwitchEvidenceV2Error("lane/leaf identity mismatch")
        hard = overlay.build_hard_evidence_record(
            width10, global_leaf_index=global_index, status="UNKNOWN",
            runner_record_sha256=session.get("record_sha256"),
            result_record_sha256=outcome.get("record_sha256"),
            timeout_seconds=policy["timeout_seconds"],
            elapsed_seconds=policy["elapsed_seconds_by_lane"][index],
            timed_out=False,
        )
        prefix = chain["latest_proof_prefix"]
        physical = chain["latest_proof_physical"]
        if (
            prefix.get("sha256") != physical.get("file_sha256")
            or prefix.get("bytes") != physical.get("bytes")
        ):
            raise AdaptiveSwitchEvidenceV2Error("proof prefix/physical mismatch")
        lane_records.append(seal({
            "schema_version": SCHEMA_VERSION, "kind": LANE_KIND,
            "lane_index": index, "cpu": lane.get("cpu"),
            "global_leaf_index": global_index,
            "global_leaf_id": leaf.get("global_leaf_id"),
            "leaf_sha256": leaf.get("leaf_sha256"),
            "child_cnf_sha256": leaf.get("child_cnf_sha256"),
            "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
            "combined_unit_clauses_sha256": leaf.get("combined_unit_clauses_sha256"),
            "child_root": lane.get("child_root"),
            "child_root_identity": runtime["root_identity"],
            "resume_static_sha256": runtime["static"].get("record_sha256"),
            "session_sha256": session.get("record_sha256"),
            "checkpoint_stop_lane_outcome_sha256": outcome.get("record_sha256"),
            "transport_chain": chain,
            "transport_chain_sha256": chain.get("record_sha256"),
            "controller_inspection": runtime["inspection"],
            "latest_checkpoint_sha256": chain.get("latest_checkpoint_sha256"),
            "checkpoint_proof_prefix": prefix,
            "checkpoint_proof_physical": physical,
            "hard_evidence": hard,
            "hard_evidence_sha256": hard.get("evidence_sha256"),
            "solver_stopped": True, "terminal_claimed": False,
            "terminal_committed": False, "hardness_only": True,
            "solver_terminal_claim": False,
        }, "lane_record_sha256"))
    if len({item["global_leaf_index"] for item in lane_records}) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("switch lanes duplicate a leaf")
    history = seal({
        "actions": list(snapshot["actions"]),
        "completed_action_count": len(snapshot["actions"]),
        "latest_action": "checkpoint-stop",
        "checkpoint_stop_claim_sha256": snapshot["checkpoint_claim"].get("record_sha256"),
        "checkpoint_stop_result_sha256": snapshot["checkpoint_result"].get("record_sha256"),
        "complete": True,
    }, "action_history_sha256")
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": SWITCH_KIND,
        "gate": SWITCH_GATE, "authority": "EVIDENCE_ONLY_ATOMIC_LEASE_REQUIRED",
        "test_only": True, "production_eligible": False,
        "authenticated": False, "launch_authorized": False,
        "scientific_claim": False, "root": str(root),
        "root_identity": _root_identity(root),
        "batch_manifest_sha256": manifest.get("record_sha256"),
        "width10_campaign_sha256": width10_sha,
        "width6_campaign_sha256": width6_sha,
        "parent_manifest_sha256": parent_sha,
        "observation_policy": policy, "action_history": history,
        "lanes": lane_records,
        "source_binding": _source_binding(
            discovery, legacy_executed, overlay_record, overlay_executed
        ),
        "claim_scope": {
            "candidate_evidence_only": True,
            "serialized_record_is_launch_authority": False,
            "unknown_is_hardness_only": True,
            "checkpoint_proves_unsat": False,
            "atomic_in_memory_lease_required": True,
            "four_lane_batch_handoff_required": True,
        },
    })


def validate_switch_record_structure(record: Mapping[str, Any]) -> dict[str, Any]:
    """Validate bytes/schema only; deliberately authenticate nothing."""

    if type(record) is not dict:
        raise AdaptiveSwitchEvidenceV2Error("switch record must be a plain object")
    _strict_json(record)
    if set(record) != SWITCH_FIELDS or not selfhash_valid(record):
        raise AdaptiveSwitchEvidenceV2Error("switch field set/self-hash mismatch")
    if (
        record.get("schema_version") != SCHEMA_VERSION
        or type(record.get("schema_version")) is not int
        or record.get("kind") != SWITCH_KIND or record.get("gate") != SWITCH_GATE
        or record.get("test_only") is not True
        or record.get("production_eligible") is not False
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or record.get("scientific_claim") is not False
    ):
        raise AdaptiveSwitchEvidenceV2Error("switch authority/schema mismatch")
    for field in (
        "batch_manifest_sha256", "width10_campaign_sha256",
        "width6_campaign_sha256", "parent_manifest_sha256", "record_sha256",
    ):
        _require_sha256(record.get(field), label=field)
    lanes = record.get("lanes")
    if type(lanes) is not list or len(lanes) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("switch must have four lanes")
    indices: set[int] = set()
    leaves: set[int] = set()
    for expected, lane in enumerate(lanes):
        if (
            type(lane) is not dict or set(lane) != LANE_FIELDS
            or not selfhash_valid(lane, "lane_record_sha256")
            or lane.get("schema_version") != SCHEMA_VERSION
            or type(lane.get("schema_version")) is not int
            or lane.get("kind") != LANE_KIND or lane.get("lane_index") != expected
            or type(lane.get("lane_index")) is not int
            or type(lane.get("global_leaf_index")) is not int
            or lane.get("solver_stopped") is not True
            or lane.get("terminal_claimed") is not False
            or lane.get("terminal_committed") is not False
            or lane.get("hardness_only") is not True
            or lane.get("solver_terminal_claim") is not False
        ):
            raise AdaptiveSwitchEvidenceV2Error("switch lane schema mismatch")
        for field in (
            "leaf_sha256", "child_cnf_sha256", "child_dimacs_sha256",
            "combined_unit_clauses_sha256", "resume_static_sha256",
            "session_sha256", "checkpoint_stop_lane_outcome_sha256",
            "transport_chain_sha256", "latest_checkpoint_sha256",
            "hard_evidence_sha256", "lane_record_sha256",
        ):
            _require_sha256(lane.get(field), label=f"lane {expected} {field}")
        chain = lane.get("transport_chain")
        if (
            type(chain) is not dict or not selfhash_valid(chain)
            or chain.get("record_sha256") != lane["transport_chain_sha256"]
            or chain.get("state") != "CHECKPOINTED"
            or chain.get("writable_holders") != []
        ):
            raise AdaptiveSwitchEvidenceV2Error("transport chain malformed")
        hard = lane.get("hard_evidence")
        if (
            type(hard) is not dict or not selfhash_valid(hard, "evidence_sha256")
            or hard.get("evidence_sha256") != lane["hard_evidence_sha256"]
            or hard.get("status") != "UNKNOWN"
            or hard.get("hardness_only") is not True
            or hard.get("solver_terminal_claim") is not False
        ):
            raise AdaptiveSwitchEvidenceV2Error("hard evidence malformed")
        indices.add(lane["lane_index"])
        leaves.add(lane["global_leaf_index"])
    if indices != set(range(LANE_COUNT)) or len(leaves) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("lane coverage is not exact")
    source = record.get("source_binding")
    history = record.get("action_history")
    if (
        type(source) is not dict
        or not selfhash_valid(source, "source_binding_sha256")
        or source.get("sitecustomize_imported_by_loader") is not False
        or source.get("pyc_executed_by_loader") is not False
        or type(history) is not dict
        or not selfhash_valid(history, "action_history_sha256")
        or history.get("latest_action") != "checkpoint-stop"
        or history.get("complete") is not True
    ):
        raise AdaptiveSwitchEvidenceV2Error("source/action binding malformed")
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": STRUCTURAL_KIND,
        "valid": True, "authenticated": False, "launch_authorized": False,
        "production_eligible": False, "scientific_claim": False,
        "switch_evidence_sha256": record["record_sha256"],
        "structural_only": True,
        "caller_expected_record_is_never_a_trust_root": True,
    })


class LaunchPermit:
    __slots__ = (
        "_lease", "_lease_nonce", "_permit_nonce", "lane_index",
        "global_leaf_index", "descendant_index", "descendant_sha256",
        "overlay_manifest_sha256", "hard_evidence_sha256", "_used",
        "permit_binding_sha256",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", *, lane_index: int,
        global_leaf_index: int, descendant_index: int,
        descendant_sha256: str, overlay_manifest_sha256: str,
        hard_evidence_sha256: str,
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self._permit_nonce = uuid.uuid4().hex
        self.lane_index = lane_index
        self.global_leaf_index = global_leaf_index
        self.descendant_index = descendant_index
        self.descendant_sha256 = descendant_sha256
        self.overlay_manifest_sha256 = overlay_manifest_sha256
        self.hard_evidence_sha256 = hard_evidence_sha256
        self._used = False
        self.permit_binding_sha256 = canonical_sha256({
            "lease_nonce": self._lease_nonce, "permit_nonce": self._permit_nonce,
            "lane_index": lane_index, "global_leaf_index": global_leaf_index,
            "descendant_index": descendant_index,
            "descendant_sha256": descendant_sha256,
            "overlay_manifest_sha256": overlay_manifest_sha256,
            "hard_evidence_sha256": hard_evidence_sha256,
        })

    def __reduce__(self) -> Any:
        raise TypeError("LaunchPermit is process-local and cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("LaunchPermit cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("LaunchPermit cannot be copied")


class PostStartFence:
    __slots__ = (
        "_lease", "_lease_nonce", "lane_index", "global_leaf_index",
        "descendant_index", "descendant_sha256", "new_root_identity",
        "new_session_sha256", "new_start_commit_sha256", "new_pid",
        "new_proc_start_ticks", "permit_binding_sha256", "fence_sha256",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", permit: LaunchPermit, *,
        new_root_identity: Mapping[str, Any], new_session_sha256: str,
        new_start_commit_sha256: str, new_pid: int, new_proc_start_ticks: int,
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self.lane_index = permit.lane_index
        self.global_leaf_index = permit.global_leaf_index
        self.descendant_index = permit.descendant_index
        self.descendant_sha256 = permit.descendant_sha256
        self.new_root_identity = dict(new_root_identity)
        self.new_session_sha256 = new_session_sha256
        self.new_start_commit_sha256 = new_start_commit_sha256
        self.new_pid = new_pid
        self.new_proc_start_ticks = new_proc_start_ticks
        self.permit_binding_sha256 = permit.permit_binding_sha256
        self.fence_sha256 = canonical_sha256(self.audit_binding())

    def audit_binding(self) -> dict[str, Any]:
        return {
            "lane_index": self.lane_index,
            "global_leaf_index": self.global_leaf_index,
            "descendant_index": self.descendant_index,
            "descendant_sha256": self.descendant_sha256,
            "new_root_identity": dict(self.new_root_identity),
            "new_session_sha256": self.new_session_sha256,
            "new_start_commit_sha256": self.new_start_commit_sha256,
            "new_pid": self.new_pid,
            "new_proc_start_ticks": self.new_proc_start_ticks,
            "permit_binding_sha256": self.permit_binding_sha256,
        }

    def __reduce__(self) -> Any:
        raise TypeError("PostStartFence is process-local and cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("PostStartFence cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("PostStartFence cannot be copied")


def _proc_start_ticks(pid: int) -> int:
    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except (FileNotFoundError, ProcessLookupError, OSError) as exc:
        raise AdaptiveSwitchEvidenceV2Error("process is not alive") from exc
    closing = payload.rfind(")")
    fields = payload[closing + 2:].split() if closing >= 0 else []
    if len(fields) <= 19 or fields[0] == "Z":
        raise AdaptiveSwitchEvidenceV2Error("process identity is malformed/dead")
    try:
        return int(fields[19])
    except ValueError as exc:
        raise AdaptiveSwitchEvidenceV2Error("process start ticks malformed") from exc


class AtomicSwitchLease:
    __slots__ = (
        "_owner_pid", "_owner_thread", "_nonce", "_active", "_committed",
        "_poisoned", "_candidate_only", "_root", "_locks", "_discovery",
        "_coordinator", "_child", "_overlay", "_legacy_executed",
        "_overlay_record", "_overlay_executed", "_snapshot", "_record",
        "_timeout", "_elapsed", "_permits", "_fences",
    )

    def __init__(
        self, root: Path, locks: list[_HeldLock], discovery: Mapping[str, Any],
        coordinator: Any, child: Any, overlay: Any,
        legacy_executed: Sequence[Mapping[str, Any]],
        overlay_record: Mapping[str, Any],
        overlay_executed: Sequence[Mapping[str, Any]],
        snapshot: Mapping[str, Any], record: Mapping[str, Any], *,
        timeout_seconds: float, elapsed_seconds_by_lane: Sequence[float],
        candidate_only: bool,
    ) -> None:
        self._owner_pid = os.getpid()
        self._owner_thread = threading.get_ident()
        self._nonce = uuid.uuid4().hex
        self._active = True
        self._committed = False
        self._poisoned = False
        self._candidate_only = candidate_only
        self._root = root
        self._locks = locks
        self._discovery = discovery
        self._coordinator = coordinator
        self._child = child
        self._overlay = overlay
        self._legacy_executed = list(legacy_executed)
        self._overlay_record = dict(overlay_record)
        self._overlay_executed = list(overlay_executed)
        self._snapshot = snapshot
        self._record = dict(record)
        self._timeout = timeout_seconds
        self._elapsed = list(elapsed_seconds_by_lane)
        self._permits: dict[int, LaunchPermit] = {}
        self._fences: dict[int, PostStartFence] = {}

    def __reduce__(self) -> Any:
        raise TypeError("AtomicSwitchLease cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("AtomicSwitchLease cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("AtomicSwitchLease cannot be copied")

    @property
    def switch_record(self) -> dict[str, Any]:
        self._assert_active()
        return json.loads(canonical_bytes(self._record))

    def _assert_active(self) -> None:
        if (
            not self._active or self._poisoned or os.getpid() != self._owner_pid
            or threading.get_ident() != self._owner_thread
        ):
            raise AdaptiveSwitchEvidenceV2Error("lease is inactive/foreign/poisoned")

    def _fresh_record(self) -> dict[str, Any]:
        snapshot = _snapshot_locked(self._root, self._coordinator, self._child)
        record = _build_record(
            self._root, snapshot, self._discovery, self._overlay,
            self._legacy_executed, self._overlay_record,
            self._overlay_executed, timeout_seconds=self._timeout,
            elapsed_seconds_by_lane=self._elapsed,
        )
        if not json_type_equal(record, self._record):
            self._poisoned = True
            raise AdaptiveSwitchEvidenceV2Error("old stopped state changed under lease")
        return record

    def verify_target(
        self, overlay_manifest: Mapping[str, Any], *,
        expected_overlay_sha256: str, global_leaf_index: int,
        expected_hard_evidence_sha256: str,
        candidate_variables: list[int], descendant_index: int,
        expected_descendant_sha256: str,
    ) -> LaunchPermit:
        self._assert_active()
        if self._candidate_only:
            raise AdaptiveSwitchEvidenceV2Error("candidate lease cannot issue permits")
        if type(global_leaf_index) is not int or type(descendant_index) is not int:
            raise AdaptiveSwitchEvidenceV2Error("target indices must be strict integers")
        if descendant_index not in {0, 1}:
            raise AdaptiveSwitchEvidenceV2Error("descendant index must be 0 or 1")
        if (
            type(candidate_variables) is not list or not candidate_variables
            or any(type(item) is not int or not 1 <= item <= 400 for item in candidate_variables)
            or len(candidate_variables) != len(set(candidate_variables))
        ):
            raise AdaptiveSwitchEvidenceV2Error("candidate variables are malformed")
        overlay_pin = _require_sha256(expected_overlay_sha256, label="overlay pin")
        hard_pin = _require_sha256(
            expected_hard_evidence_sha256, label="hard-evidence pin"
        )
        descendant_pin = _require_sha256(
            expected_descendant_sha256, label="descendant pin"
        )
        if (
            type(overlay_manifest) is not dict
            or overlay_manifest.get("manifest_sha256") != overlay_pin
            or not selfhash_valid(overlay_manifest, "manifest_sha256")
        ):
            raise AdaptiveSwitchEvidenceV2Error("overlay misses external pin")
        matches = [
            lane for lane in self._record["lanes"]
            if lane["global_leaf_index"] == global_leaf_index
        ]
        if len(matches) != 1:
            raise AdaptiveSwitchEvidenceV2Error("target is not one old batch lane")
        lane = matches[0]
        lane_index = lane["lane_index"]
        if lane_index in self._permits or lane["hard_evidence_sha256"] != hard_pin:
            raise AdaptiveSwitchEvidenceV2Error("lane already issued/misses hard pin")
        instance = self._overlay.optimized.build_optimized_instance()
        try:
            checked = self._overlay.verify_overlay_manifest(
                overlay_manifest, self._snapshot["width10_campaign"],
                self._snapshot["width6_campaign"], self._snapshot["parent"],
                instance, global_leaf_index=global_leaf_index,
                hard_evidence=lane["hard_evidence"],
                expected_hard_evidence_sha256=hard_pin,
                candidate_variables=list(candidate_variables),
                expected_overlay_sha256=overlay_pin, strict_base=True,
            )
        except Exception as exc:
            raise AdaptiveSwitchEvidenceV2Error("overlay target replay failed") from exc
        if (
            type(checked) is not dict or checked.get("valid") is not True
            or checked.get("current_source_exact_replay") is not True
            or checked.get("launch_authorized") is not False
            or checked.get("production_eligible") is not False
        ):
            raise AdaptiveSwitchEvidenceV2Error("overlay authority mismatch")
        descendants = overlay_manifest.get("descendants")
        if type(descendants) is not list or len(descendants) != 2:
            raise AdaptiveSwitchEvidenceV2Error("overlay must have two descendants")
        descendant = descendants[descendant_index]
        if (
            type(descendant) is not dict
            or descendant.get("descendant_index") != descendant_index
            or descendant.get("descendant_sha256") != descendant_pin
            or descendant.get("pending") is not True
            or descendant.get("status_source") != "generated-frontier-v1"
            or descendant.get("solver_terminal_authenticated") is not False
            or descendant.get("parent_leaf_sha256") != lane["leaf_sha256"]
        ):
            raise AdaptiveSwitchEvidenceV2Error("exact pending descendant mismatch")
        permit = LaunchPermit(
            self, lane_index=lane_index, global_leaf_index=global_leaf_index,
            descendant_index=descendant_index, descendant_sha256=descendant_pin,
            overlay_manifest_sha256=overlay_pin, hard_evidence_sha256=hard_pin,
        )
        self._permits[lane_index] = permit
        return permit

    def post_start_fence(
        self, *, permit: LaunchPermit, new_root_identity: Mapping[str, Any],
        new_session_sha256: str, new_start_commit_sha256: str,
        new_pid: int, new_proc_start_ticks: int,
    ) -> PostStartFence:
        self._assert_active()
        if (
            type(permit) is not LaunchPermit or permit._lease is not self
            or permit._lease_nonce != self._nonce or permit._used
            or self._permits.get(permit.lane_index) is not permit
            or permit.lane_index in self._fences
        ):
            raise AdaptiveSwitchEvidenceV2Error("permit is foreign, stale, or reused")
        session_sha = _require_sha256(new_session_sha256, label="new session")
        start_sha = _require_sha256(new_start_commit_sha256, label="new start commit")
        if type(new_pid) is not int or type(new_proc_start_ticks) is not int:
            raise AdaptiveSwitchEvidenceV2Error("new process identity must be strict ints")
        if _proc_start_ticks(new_pid) != new_proc_start_ticks:
            raise AdaptiveSwitchEvidenceV2Error("new process identity is not alive")
        if type(new_root_identity) is not dict or type(new_root_identity.get("path")) is not str:
            raise AdaptiveSwitchEvidenceV2Error("new root identity malformed")
        observed_root = _root_identity(Path(new_root_identity["path"]))
        if not json_type_equal(observed_root, new_root_identity):
            raise AdaptiveSwitchEvidenceV2Error("new root identity changed")
        try:
            self._fresh_record()
            fence = PostStartFence(
                self, permit, new_root_identity=observed_root,
                new_session_sha256=session_sha,
                new_start_commit_sha256=start_sha, new_pid=new_pid,
                new_proc_start_ticks=new_proc_start_ticks,
            )
        except BaseException:
            self._poisoned = True
            permit._used = True
            raise
        permit._used = True
        self._fences[permit.lane_index] = fence
        return fence

    def commit_handoff(
        self, *, fences: list[PostStartFence], batch_commit_path: Path,
    ) -> dict[str, Any]:
        self._assert_active()
        if self._candidate_only or self._committed:
            raise AdaptiveSwitchEvidenceV2Error("lease cannot commit")
        if type(fences) is not list or len(fences) != LANE_COUNT:
            raise AdaptiveSwitchEvidenceV2Error("exactly four fences are required")
        by_lane: dict[int, PostStartFence] = {}
        for fence in fences:
            if (
                type(fence) is not PostStartFence or fence._lease is not self
                or fence._lease_nonce != self._nonce
                or self._fences.get(fence.lane_index) is not fence
                or fence.lane_index in by_lane
            ):
                raise AdaptiveSwitchEvidenceV2Error("fence set is foreign/duplicated")
            by_lane[fence.lane_index] = fence
        if set(by_lane) != set(range(LANE_COUNT)):
            raise AdaptiveSwitchEvidenceV2Error("fences do not cover all old lanes")
        roots = [item.new_root_identity["path"] for item in by_lane.values()]
        pids = [item.new_pid for item in by_lane.values()]
        if len(set(roots)) != LANE_COUNT or len(set(pids)) != LANE_COUNT:
            raise AdaptiveSwitchEvidenceV2Error("new roots/processes are duplicated")
        for item in by_lane.values():
            if _proc_start_ticks(item.new_pid) != item.new_proc_start_ticks:
                raise AdaptiveSwitchEvidenceV2Error("new process died before commit")
        self._fresh_record()
        target = Path(batch_commit_path)
        expected_target = self._root / HANDOFF_COMMIT
        if target != expected_target:
            raise AdaptiveSwitchEvidenceV2Error(
                f"batch commit path must be {expected_target}"
            )
        suffix = self._record["record_sha256"][:16]
        retired: list[dict[str, Any]] = []
        retired_locks: list[_HeldLock] = []
        try:
            # Retire direct controller entry points first, then lane entry points,
            # and finally the batch coordinator.  Held fds keep every transition
            # excluded throughout the rename sequence.
            for held in [*self._locks[5:], *self._locks[1:5], self._locks[0]]:
                retired.append(held.retire(suffix))
                retired_locks.append(held)
            root_bindings = [
                {
                    **by_lane[index].audit_binding(),
                    "fence_sha256": by_lane[index].fence_sha256,
                }
                for index in range(LANE_COUNT)
            ]
            record = seal({
                "schema_version": SCHEMA_VERSION, "kind": HANDOFF_KIND,
                "gate": SWITCH_GATE, "test_only": True,
                "production_eligible": False, "authenticated": False,
                "launch_authorized": False, "scientific_claim": False,
                "historical_atomic_handoff_observed": True,
                "batch_root": str(self._root),
                "batch_root_identity": _root_identity(self._root),
                "batch_manifest_sha256": self._record["batch_manifest_sha256"],
                "switch_evidence_sha256": self._record["record_sha256"],
                "source_binding": self._record["source_binding"],
                "retired_locks": retired, "root_bindings": root_bindings,
                "fence_sha256s": [item["fence_sha256"] for item in root_bindings],
                "root_link_policy": {
                    "relative_path": "state/15-batch-handoff.json",
                    "publish": "o-excl-canonical-json-fsync-v1",
                    "repair_only_from_externally_pinned_batch_commit": True,
                },
                "claim_scope": {
                    "old_transport_durably_retired": True,
                    "four_new_processes_observed_alive_under_old_locks": True,
                    "serialized_record_can_authorize_launch": False,
                    "serialized_record_can_authenticate_unsat": False,
                    "root_links_may_be_repaired_from_this_commit": True,
                },
            })
            _publish_new_json(target, record)
        except BaseException:
            failures: list[BaseException] = []
            for held in reversed(retired_locks):
                try:
                    held.restore()
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                self._poisoned = True
                raise AdaptiveSwitchEvidenceV2Error(
                    "handoff failed and lock retirement rollback was incomplete"
                ) from failures[0]
            raise
        self._committed = True
        return json.loads(canonical_bytes(record))

    def _close(self) -> None:
        if not self._active:
            return
        self._active = False
        for held in reversed(self._locks):
            held.close()


def _publish_new_json(path: Path, value: Mapping[str, Any]) -> None:
    payload = canonical_bytes(value) + b"\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    fd = os.open(path, flags, 0o600)
    try:
        offset = 0
        while offset < len(payload):
            written = os.write(fd, payload[offset:])
            if written <= 0:
                raise AdaptiveSwitchEvidenceV2Error("short JSON publication")
            offset += written
        os.fsync(fd)
    finally:
        os.close(fd)
    directory = os.open(
        path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
    )
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _enter_lease(
    batch_root: Path, *, expected_batch_manifest_sha256: str | None,
    expected_switch_evidence_sha256: str | None,
    expected_hard_evidence_sha256s: list[str] | None,
    timeout_seconds: float, elapsed_seconds_by_lane: list[float],
    strict_base: bool, candidate_only: bool,
) -> AtomicSwitchLease:
    if type(strict_base) is not bool or strict_base is not True:
        raise AdaptiveSwitchEvidenceV2Error("only strict real replay is accepted")
    root = Path(batch_root)
    locks, discovery = _acquire_all_locks(root)
    try:
        fresh_discovery = _discover_sources(
            root, expected_batch_manifest_sha256=expected_batch_manifest_sha256
        )
        if not json_type_equal(
            {key: discovery[key] for key in ("root_identity", "batch", "legacy_sources")},
            {key: fresh_discovery[key] for key in ("root_identity", "batch", "legacy_sources")},
        ):
            raise AdaptiveSwitchEvidenceV2Error("batch/source changed during locking")
        discovery = fresh_discovery
        coordinator, child, legacy_executed = _load_exact_modules(discovery)
        overlay, overlay_record, overlay_executed = _load_overlay_exact()
        snapshot = _snapshot_locked(root, coordinator, child)
        record = _build_record(
            root, snapshot, discovery, overlay, legacy_executed,
            overlay_record, overlay_executed,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        )
        validate_switch_record_structure(record)
        if not candidate_only:
            switch_pin = _require_sha256(
                expected_switch_evidence_sha256, label="switch evidence pin"
            )
            batch_pin = _require_sha256(
                expected_batch_manifest_sha256, label="batch manifest pin"
            )
            if record["record_sha256"] != switch_pin or record["batch_manifest_sha256"] != batch_pin:
                raise AdaptiveSwitchEvidenceV2Error("fresh replay misses external pins")
            if type(expected_hard_evidence_sha256s) is not list or len(expected_hard_evidence_sha256s) != LANE_COUNT:
                raise AdaptiveSwitchEvidenceV2Error("four hard-evidence pins required")
            hard_pins = [
                _require_sha256(item, label="hard-evidence pin")
                for item in expected_hard_evidence_sha256s
            ]
            if [lane["hard_evidence_sha256"] for lane in record["lanes"]] != hard_pins:
                raise AdaptiveSwitchEvidenceV2Error("hard evidence misses external pins")
        return AtomicSwitchLease(
            root, locks, discovery, coordinator, child, overlay,
            legacy_executed, overlay_record, overlay_executed, snapshot, record,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
            candidate_only=candidate_only,
        )
    except BaseException:
        for held in reversed(locks):
            held.close()
        raise


@contextlib.contextmanager
def acquire_atomic_switch_lease(
    batch_root: Path, *, expected_batch_manifest_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_hard_evidence_sha256s: list[str], timeout_seconds: float,
    elapsed_seconds_by_lane: list[float], strict_base: bool = True,
) -> Iterator[AtomicSwitchLease]:
    """Disabled: v2 has a known pre-retirement crash window."""

    del (
        batch_root, expected_batch_manifest_sha256,
        expected_switch_evidence_sha256, expected_hard_evidence_sha256s,
        timeout_seconds, elapsed_seconds_by_lane, strict_base,
    )
    raise AdaptiveSwitchEvidenceV2Error("SUPERSEDED_BY_V3")
    yield  # pragma: no cover - preserves the contextmanager protocol


def build_switch_evidence_record(
    batch_root: Path, *, timeout_seconds: float,
    elapsed_seconds_by_lane: list[float], strict_base: bool = True,
) -> dict[str, Any]:
    """Build a pin candidate.  The returned record authenticates no launch."""

    lease = _enter_lease(
        batch_root, expected_batch_manifest_sha256=None,
        expected_switch_evidence_sha256=None,
        expected_hard_evidence_sha256s=None,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        strict_base=strict_base, candidate_only=True,
    )
    try:
        return lease.switch_record
    finally:
        lease._close()


def _validate_handoff_record(record: Mapping[str, Any]) -> dict[str, Any]:
    if type(record) is not dict or set(record) != HANDOFF_FIELDS or not selfhash_valid(record):
        raise AdaptiveSwitchEvidenceV2Error("handoff field set/self-hash mismatch")
    _strict_json(record)
    if (
        record.get("schema_version") != SCHEMA_VERSION
        or type(record.get("schema_version")) is not int
        or record.get("kind") != HANDOFF_KIND or record.get("gate") != SWITCH_GATE
        or record.get("test_only") is not True
        or record.get("production_eligible") is not False
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or record.get("scientific_claim") is not False
        or record.get("historical_atomic_handoff_observed") is not True
    ):
        raise AdaptiveSwitchEvidenceV2Error("handoff authority/schema mismatch")
    bindings = record.get("root_bindings")
    fences = record.get("fence_sha256s")
    retired = record.get("retired_locks")
    if (
        type(bindings) is not list or len(bindings) != LANE_COUNT
        or type(fences) is not list or len(fences) != LANE_COUNT
        or type(retired) is not list or len(retired) != 1 + 2 * LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV2Error("handoff cardinality mismatch")
    expected_binding_fields = {
        "lane_index", "global_leaf_index", "descendant_index",
        "descendant_sha256", "new_root_identity", "new_session_sha256",
        "new_start_commit_sha256", "new_pid", "new_proc_start_ticks",
        "permit_binding_sha256", "fence_sha256",
    }
    roots: set[str] = set()
    pids: set[int] = set()
    for index, binding in enumerate(bindings):
        if type(binding) is not dict or set(binding) != expected_binding_fields:
            raise AdaptiveSwitchEvidenceV2Error("root binding schema mismatch")
        unsigned = dict(binding)
        fence_sha = unsigned.pop("fence_sha256")
        if (
            binding.get("lane_index") != index
            or type(binding.get("lane_index")) is not int
            or type(binding.get("global_leaf_index")) is not int
            or type(binding.get("descendant_index")) is not int
            or binding.get("descendant_index") not in {0, 1}
            or type(binding.get("new_pid")) is not int
            or type(binding.get("new_proc_start_ticks")) is not int
            or canonical_sha256(unsigned) != fence_sha or fences[index] != fence_sha
        ):
            raise AdaptiveSwitchEvidenceV2Error("root/fence binding mismatch")
        for field in (
            "descendant_sha256", "new_session_sha256", "new_start_commit_sha256",
            "permit_binding_sha256", "fence_sha256",
        ):
            _require_sha256(binding.get(field), label=f"binding {field}")
        identity = binding.get("new_root_identity")
        if type(identity) is not dict or type(identity.get("path")) is not str:
            raise AdaptiveSwitchEvidenceV2Error("new root identity malformed")
        roots.add(identity["path"])
        pids.add(binding["new_pid"])
    if len(roots) != LANE_COUNT or len(pids) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV2Error("handoff roots/PIDs are duplicated")
    roles = {item.get("role") for item in retired if type(item) is dict}
    if roles != {"batch", *{f"lane-{i}" for i in range(4)}, *{f"controller-{i}" for i in range(4)}}:
        raise AdaptiveSwitchEvidenceV2Error("retired lock roles mismatch")
    return dict(record)


def verify_committed_handoff(
    batch_commit_path: Path, *, expected_batch_commit_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str,
) -> dict[str, Any]:
    """Verify a durable historical handoff; never authorize another launch."""

    commit_pin = _require_sha256(
        expected_batch_commit_sha256, label="batch handoff commit pin"
    )
    switch_pin = _require_sha256(
        expected_switch_evidence_sha256, label="switch evidence pin"
    )
    batch_pin = _require_sha256(
        expected_batch_manifest_sha256, label="batch manifest pin"
    )
    path = Path(batch_commit_path)
    record = _validate_handoff_record(_read_json(path))
    root = Path(record.get("batch_root", ""))
    if (
        path != root / HANDOFF_COMMIT or record["record_sha256"] != commit_pin
        or record["switch_evidence_sha256"] != switch_pin
        or record["batch_manifest_sha256"] != batch_pin
        or not json_type_equal(record.get("batch_root_identity"), _root_identity(root))
    ):
        raise AdaptiveSwitchEvidenceV2Error("handoff misses path/external pins")
    verified_retirement: list[dict[str, Any]] = []
    for item in record["retired_locks"]:
        if type(item) is not dict or set(item) != {
            "role", "original_path", "retired_path", "identity"
        }:
            raise AdaptiveSwitchEvidenceV2Error("retired lock schema mismatch")
        original = Path(item["original_path"])
        retired = Path(item["retired_path"])
        if original.exists() or original.is_symlink():
            raise AdaptiveSwitchEvidenceV2Error("legacy lock entry point was restored")
        try:
            observed = retired.lstat()
        except OSError as exc:
            raise AdaptiveSwitchEvidenceV2Error("retired lock is missing") from exc
        if (
            stat.S_ISLNK(observed.st_mode) or not stat.S_ISREG(observed.st_mode)
            or not json_type_equal(_stat_identity(observed), item["identity"])
        ):
            raise AdaptiveSwitchEvidenceV2Error("retired lock identity mismatch")
        verified_retirement.append(dict(item))
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": HANDOFF_VERIFY_KIND,
        "valid": True, "authenticated": False, "launch_authorized": False,
        "production_eligible": False, "scientific_claim": False,
        "historical_handoff_only": True,
        "batch_commit_sha256": record["record_sha256"],
        "switch_evidence_sha256": record["switch_evidence_sha256"],
        "batch_manifest_sha256": record["batch_manifest_sha256"],
        "old_transport_retirement_verified": True,
        "retired_locks": verified_retirement,
        "root_bindings": list(record["root_bindings"]),
        "fence_sha256s": list(record["fence_sha256s"]),
        "root_link_policy": dict(record["root_link_policy"]),
    })


__all__ = [
    "AdaptiveSwitchEvidenceV2Error", "AtomicSwitchLease", "LaunchPermit",
    "PostStartFence", "HANDOFF_COMMIT",
    "build_switch_evidence_record", "validate_switch_record_structure",
    "verify_committed_handoff", "canonical_bytes", "canonical_sha256",
    "seal", "selfhash_valid", "json_type_equal",
]
