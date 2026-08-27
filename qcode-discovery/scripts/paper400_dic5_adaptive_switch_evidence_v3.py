#!/usr/bin/env python3
"""Crash-safe atomic handoff from four old lanes to eight descendants.

Version 3 closes the remaining crash window in v2: the nine legacy entry
points (batch, four lane, and four DMTCP controller lock names) are durably
retired *before* a launch-capable lease is returned.  A process crash can
therefore strand a PREPARED handoff, but it cannot make an old runner
reachable while a new proof writer is alive.

All JSON records remain evidence-only.  Launch authority exists only in the
non-serializable, owner-process/thread-bound ``AtomicSwitchLease``.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import importlib
import importlib.abc
import importlib.util
import json
import os
import stat
import sys
import threading
import types
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
BASE_RELATIVE = Path("scripts/paper400_dic5_adaptive_switch_evidence_v2.py")
OVERLAY_RELATIVE = Path(
    "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
)
MAX_SOURCE_BYTES = 16 << 20
MAX_PROOF_BYTES = 1 << 40
SCHEMA_VERSION = 3
LANE_COUNT = 4
DESCENDANT_COUNT = 2
TARGET_COUNT = LANE_COUNT * DESCENDANT_COUNT
MAX_LIVE_WORKERS = 4
TARGET_KEYS = tuple(
    (lane, descendant)
    for descendant in range(DESCENDANT_COUNT)
    for lane in range(LANE_COUNT)
)
GATE = "paper400-dic5-adaptive-switch-evidence-v3"
PREPARED_KIND = "paper400-dic5-adaptive-retirement-prepared-v3"
HANDOFF_KIND = "paper400-dic5-adaptive-batch-handoff-v3"
HANDOFF_VERIFY_KIND = "paper400-dic5-adaptive-batch-handoff-check-v3"
ROLLBACK_KIND = "paper400-dic5-adaptive-handoff-rollback-v3"
QUIESCENCE_KIND = "paper400-adaptive-new-root-quiescence-v3"
RETIREMENT_INTENT = Path("adaptive-handoff-v3.retirement-intent.json")
PREPARED_COMMIT = Path("adaptive-handoff-v3.prepared.json")
HANDOFF_COMMIT = Path("adaptive-handoff-v3.json")
ROLLBACK_COMMIT = Path("adaptive-handoff-v3.rollback.json")
TARGET_DIRECTORY = Path("adaptive-handoff-v3.targets")
STARTED_DIRECTORY = Path("adaptive-handoff-v3.started")
QUIESCENCE_DIRECTORY = Path("adaptive-handoff-v3.quiescence")


class AdaptiveSwitchEvidenceV3Error(RuntimeError):
    """A source, retirement, target, process, or rollback invariant failed."""


def _read_source_bytes(path: Path) -> bytes:
    candidate = Path(path)
    lexical = candidate.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_nlink != 1 or lexical.st_size > MAX_SOURCE_BYTES
    ):
        raise AdaptiveSwitchEvidenceV3Error("unsafe source file")
    fd = os.open(candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    try:
        before = os.fstat(fd)
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            chunks.append(chunk)
            if sum(map(len, chunks)) > MAX_SOURCE_BYTES:
                raise AdaptiveSwitchEvidenceV3Error("source exceeds cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_gid,
        item.st_nlink, item.st_size, item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(b"".join(chunks)) != before.st_size:
        raise AdaptiveSwitchEvidenceV3Error("source changed while reading")
    return b"".join(chunks)


_V3_SOURCE_PATH = Path(__file__).resolve(strict=True)
_V3_SOURCE_PAYLOAD = _read_source_bytes(_V3_SOURCE_PATH)
_V3_SOURCE_RECORD = {
    "role": "adaptive_switch_evidence_v3_source",
    "relative_path": _V3_SOURCE_PATH.relative_to(PROJECT).as_posix(),
    "sha256": hashlib.sha256(_V3_SOURCE_PAYLOAD).hexdigest(),
    "bytes": len(_V3_SOURCE_PAYLOAD),
    "execution": "module-load-captured-exact-source-bytes-v3",
}


def _load_base_from_exact_source() -> tuple[Any, dict[str, Any]]:
    path = (PROJECT / BASE_RELATIVE).resolve(strict=True)
    payload = _read_source_bytes(path)
    module = types.ModuleType("_paper400_adaptive_switch_v2_exact_bytes")
    module.__file__ = str(path)
    module.__package__ = "scripts"
    module.__loader__ = None
    exec(compile(payload, str(path), "exec", dont_inherit=True), module.__dict__)
    return module, {
        "role": "adaptive_switch_evidence_v2_primitives_source",
        "relative_path": BASE_RELATIVE.as_posix(),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "execution": "compile-exact-source-bytes-v3",
    }


base, _BASE_SOURCE_RECORD = _load_base_from_exact_source()

canonical_bytes = base.canonical_bytes
canonical_sha256 = base.canonical_sha256
seal = base.seal
selfhash_valid = base.selfhash_valid
json_type_equal = base.json_type_equal
validate_switch_record_structure = base.validate_switch_record_structure


_LOAD_GUARD = threading.RLock()
_PROJECT_PREFIXES = (
    "scripts", "scripts.", "investigations", "investigations.",
    "evaluation", "evaluation.",
)


class _ExactSourceLoader(importlib.abc.Loader):
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
        module.__file__ = str(self.path)
        module.__package__ = (
            self.fullname if self.path.name == "__init__.py"
            else self.fullname.rpartition(".")[0]
        )
        if self.path.name == "__init__.py":
            module.__path__ = [str(self.path.parent)]
        digest = hashlib.sha256(self.payload).hexdigest()
        self.observed[self.fullname] = {
            "module": self.fullname, "path": str(self.path),
            "sha256": digest, "bytes": len(self.payload),
            "externally_bound": self.externally_bound,
            "execution": "compile-exact-source-bytes-v3",
        }
        exec(
            compile(self.payload, str(self.path), "exec", dont_inherit=True),
            module.__dict__,
        )


class _ExactSourceFinder(importlib.abc.MetaPathFinder):
    def __init__(
        self, project: Path, bound: Mapping[str, tuple[Path, bytes, str]],
    ) -> None:
        self.project = project.resolve(strict=True)
        self.bound = dict(bound)
        self.observed: dict[str, dict[str, Any]] = {}

    def _spec(
        self, fullname: str, path: Path, payload: bytes, *,
        externally_bound: bool, is_package: bool,
    ) -> Any:
        loader = _ExactSourceLoader(
            fullname, path, payload, self.observed,
            externally_bound=externally_bound,
        )
        return importlib.util.spec_from_loader(
            fullname, loader, origin=str(path), is_package=is_package,
        )

    def find_spec(
        self, fullname: str, path: Sequence[str] | None = None,
        target: types.ModuleType | None = None,
    ) -> Any:
        del path, target
        if fullname in {"sitecustomize", "usercustomize"}:
            raise AdaptiveSwitchEvidenceV3Error(
                "Python startup customization is forbidden"
            )
        bound = self.bound.get(fullname)
        if bound is not None:
            source, payload, expected = bound
            if hashlib.sha256(payload).hexdigest() != expected:
                raise AdaptiveSwitchEvidenceV3Error("bound source payload drift")
            return self._spec(
                fullname, source, payload, externally_bound=True,
                is_package=source.name == "__init__.py",
            )
        if not fullname.startswith(_PROJECT_PREFIXES):
            return None
        parts = fullname.split(".")
        package = self.project.joinpath(*parts) / "__init__.py"
        source = self.project.joinpath(*parts).with_suffix(".py")
        selected: Path | None = None
        is_package = False
        if package.is_file() and not package.is_symlink():
            selected, is_package = package, True
        elif source.is_file() and not source.is_symlink():
            selected = source
        if selected is None:
            return None
        try:
            selected.resolve(strict=True).relative_to(self.project)
        except (FileNotFoundError, OSError, RuntimeError, ValueError) as exc:
            raise AdaptiveSwitchEvidenceV3Error("source escapes exact project") from exc
        payload = _read_source_bytes(selected)
        return self._spec(
            fullname, selected, payload, externally_bound=False,
            is_package=is_package,
        )


def _purge_project_modules() -> dict[str, types.ModuleType]:
    removed: dict[str, types.ModuleType] = {}
    for name, module in list(sys.modules.items()):
        if name == __name__:
            continue
        if name in {"scripts", "investigations", "evaluation"} or name.startswith(
            ("scripts.", "investigations.", "evaluation.")
        ):
            removed[name] = module
            sys.modules.pop(name, None)
    return removed


def _restore_project_modules(
    before_names: set[str], removed: Mapping[str, types.ModuleType],
) -> None:
    for name in list(sys.modules):
        if name not in before_names and (
            name in {"scripts", "investigations", "evaluation"}
            or name.startswith(("scripts.", "investigations.", "evaluation."))
        ):
            sys.modules.pop(name, None)
    for name, module in removed.items():
        sys.modules[name] = module


def _load_legacy_exact(
    discovery: Mapping[str, Any],
) -> tuple[Any, Any, list[dict[str, Any]]]:
    project = discovery["legacy_project"]
    finder = _ExactSourceFinder(project, discovery["source_payloads"])
    coordinator_name = discovery["coordinator_module"]
    child_name = discovery["child_module"]
    with _LOAD_GUARD:
        before_names = set(sys.modules)
        before_meta = list(sys.meta_path)
        removed = _purge_project_modules()
        try:
            sys.meta_path.insert(0, finder)
            coordinator = importlib.import_module(coordinator_name)
            child = sys.modules.get(child_name)
            if child is None or getattr(coordinator, "child_runner", None) is not child:
                raise AdaptiveSwitchEvidenceV3Error("coordinator exact-child mismatch")
            required = set(discovery["source_payloads"])
            missing = required - set(finder.observed)
            if missing:
                raise AdaptiveSwitchEvidenceV3Error(
                    f"manifest-bound sources not executed from bytes: {sorted(missing)}"
                )
            for name in required:
                if (
                    finder.observed[name]["sha256"]
                    != discovery["source_payloads"][name][2]
                    or finder.observed[name]["externally_bound"] is not True
                ):
                    raise AdaptiveSwitchEvidenceV3Error("bound source execution mismatch")
            return coordinator, child, [
                finder.observed[name] for name in sorted(finder.observed)
            ]
        finally:
            sys.meta_path[:] = before_meta
            _restore_project_modules(before_names, removed)


def _load_overlay_exact() -> tuple[Any, dict[str, Any], list[dict[str, Any]]]:
    path = (PROJECT / OVERLAY_RELATIVE).resolve(strict=True)
    payload = _read_source_bytes(path)
    digest = hashlib.sha256(payload).hexdigest()
    name = ".".join(OVERLAY_RELATIVE.with_suffix("").parts)
    finder = _ExactSourceFinder(PROJECT, {name: (path, payload, digest)})
    with _LOAD_GUARD:
        before_names = set(sys.modules)
        before_meta = list(sys.meta_path)
        removed = _purge_project_modules()
        try:
            sys.meta_path.insert(0, finder)
            overlay = importlib.import_module(name)
            if (
                name not in finder.observed
                or finder.observed[name]["sha256"] != digest
                or finder.observed[name]["externally_bound"] is not True
            ):
                raise AdaptiveSwitchEvidenceV3Error("overlay exact-byte load failed")
            return overlay, {
                "role": "adaptive_leaf_overlay_v2_source",
                "relative_path": OVERLAY_RELATIVE.as_posix(),
                "sha256": digest,
                "bytes": len(payload),
                "execution": "compile-exact-source-bytes-v3",
            }, [finder.observed[item] for item in sorted(finder.observed)]
        finally:
            sys.meta_path[:] = before_meta
            _restore_project_modules(before_names, removed)


def _v3_source_binding() -> dict[str, Any]:
    if _read_source_bytes(_V3_SOURCE_PATH) != _V3_SOURCE_PAYLOAD:
        raise AdaptiveSwitchEvidenceV3Error(
            "v3 source changed since exact module load"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "exact-source-bytes-no-pyc-no-sitecustomize-v3",
        "sources": [
            dict(_V3_SOURCE_RECORD),
            dict(_BASE_SOURCE_RECORD),
        ],
        "sitecustomize_executed_by_loader": False,
        "pyc_executed_by_loader": False,
    }, "source_binding_sha256")


def _publish(path: Path, record: Mapping[str, Any]) -> None:
    base._publish_new_json(path, record)


def _make_journal_directory(root: Path, relative: Path) -> Path:
    target = root / relative
    try:
        os.mkdir(target, 0o700)
    except FileExistsError as exc:
        raise AdaptiveSwitchEvidenceV3Error(
            f"stale handoff journal exists: {relative}"
        ) from exc
    lexical = target.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISDIR(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV3Error("unsafe handoff journal directory")
    _fsync_directory(root)
    return target


def _fsync_directory(path: Path) -> None:
    fd = os.open(
        path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
    )
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _identity_without_ctime(identity: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(identity)
    result.pop("ctime_ns", None)
    return result


def _retire_lock_v3(held: Any, retired_path: Path) -> dict[str, Any]:
    original = Path(held.original_path)
    retired = Path(retired_path)
    if (
        Path(held.current_path) != original
        or retired.parent != original.parent
        or retired.name == original.name
        or retired.exists() or retired.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV3Error("unsafe v3 retirement target")
    lexical = original.lstat()
    pre = base._stat_identity(os.fstat(held.fd))
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or not json_type_equal(base._stat_identity(lexical), pre)
        or not json_type_equal(pre, held.identity)
        or pre["uid"] != os.geteuid() or pre["mode"] != 0o600
        or pre["links"] != 1 or pre["bytes"] != 0
    ):
        raise AdaptiveSwitchEvidenceV3Error("held legacy lock changed")
    os.rename(original, retired)
    # Record the new pathname immediately so any later fsync/validation fault
    # can be compensated before a launch-capable lease is returned.
    held.current_path = retired
    held.identity = base._stat_identity(os.fstat(held.fd))
    _fsync_directory(retired.parent)
    post_path = base._stat_identity(retired.lstat())
    post_fd = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(post_path, post_fd)
        or not json_type_equal(
            _identity_without_ctime(pre), _identity_without_ctime(post_fd)
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error("retired legacy lock identity changed")
    held.current_path = retired
    held.identity = post_fd
    return {
        "role": held.role, "original_path": str(original),
        "retired_path": str(retired), "pre_rename_identity": pre,
        "identity": post_fd,
    }


def _restore_lock_v3(held: Any, record: Mapping[str, Any]) -> dict[str, Any]:
    original = Path(record["original_path"])
    retired = Path(record["retired_path"])
    if (
        Path(held.original_path) != original or Path(held.current_path) != retired
        or original.exists() or original.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV3Error("unsafe v3 restore target")
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(path_identity, record["identity"])
        or not json_type_equal(fd_identity, record["identity"])
    ):
        raise AdaptiveSwitchEvidenceV3Error("retired lock changed before restore")
    os.rename(retired, original)
    _fsync_directory(original.parent)
    restored_path = base._stat_identity(original.lstat())
    restored_fd = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(restored_path, restored_fd)
        or not json_type_equal(
            _identity_without_ctime(fd_identity),
            _identity_without_ctime(restored_fd),
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error("restored lock identity changed")
    held.current_path = original
    held.identity = restored_fd
    return {
        "role": held.role, "original_path": str(original),
        "retired_path": str(retired), "identity": restored_fd,
    }


def _restore_current_lock_v3(
    held: Any, *, original_path: Path, retired_path: Path,
) -> dict[str, Any] | None:
    original = Path(original_path)
    retired = Path(retired_path)
    if Path(held.current_path) == original:
        return None
    if Path(held.current_path) != retired:
        raise AdaptiveSwitchEvidenceV3Error(
            "held lock has an unknown compensation path"
        )
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if not json_type_equal(path_identity, fd_identity):
        raise AdaptiveSwitchEvidenceV3Error(
            "retired inode changed before compensation"
        )
    held.identity = fd_identity
    return _restore_lock_v3(held, {
        "original_path": str(original),
        "retired_path": str(retired),
        "identity": fd_identity,
    })


def _stream_hash_size_identity(
    path: Path, *, cap: int = MAX_PROOF_BYTES,
) -> tuple[str, int, dict[str, int]]:
    candidate = Path(path)
    lexical = candidate.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid() or lexical.st_nlink != 1
        or lexical.st_size < 0 or lexical.st_size > cap
    ):
        raise AdaptiveSwitchEvidenceV3Error("unsafe proof prefix")
    fd = os.open(candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    digest = hashlib.sha256()
    total = 0
    try:
        before = os.fstat(fd)
        if not json_type_equal(
            base._stat_identity(before), base._stat_identity(lexical)
        ):
            raise AdaptiveSwitchEvidenceV3Error("proof changed before streaming")
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise AdaptiveSwitchEvidenceV3Error("proof exceeds streaming cap")
            digest.update(chunk)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if (
        not json_type_equal(
            base._stat_identity(before), base._stat_identity(after)
        )
        or total != before.st_size
    ):
        raise AdaptiveSwitchEvidenceV3Error("proof changed while streaming")
    return digest.hexdigest(), total, base._stat_identity(after)


def _stream_hash_size(
    path: Path, *, cap: int = MAX_PROOF_BYTES,
) -> tuple[str, int]:
    digest, total, _ = _stream_hash_size_identity(path, cap=cap)
    return digest, total


def _validate_quiescence_record(record: Any) -> dict[str, Any]:
    expected_fields = {
        "schema_version", "kind", "lane_index", "descendant_index",
        "new_root_identity", "new_pid", "new_proc_start_ticks",
        "state", "pid_identity_alive", "checkpoint_commit_sha256",
        "proof_sha256", "proof_bytes", "writable_holders", "record_sha256",
    }
    if (
        type(record) is not dict or set(record) != expected_fields
        or not selfhash_valid(record)
        or type(record.get("schema_version")) is not int
        or record.get("schema_version") != SCHEMA_VERSION
        or record.get("kind") != QUIESCENCE_KIND
        or type(record.get("lane_index")) is not int
        or record["lane_index"] not in range(LANE_COUNT)
        or type(record.get("descendant_index")) is not int
        or record["descendant_index"] not in range(DESCENDANT_COUNT)
        or type(record.get("new_pid")) is not int or record["new_pid"] <= 0
        or type(record.get("new_proc_start_ticks")) is not int
        or record["new_proc_start_ticks"] <= 0
        or type(record.get("new_root_identity")) is not dict
        or type(record["new_root_identity"].get("path")) is not str
        or record.get("state") not in {
            "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
        }
        or record.get("pid_identity_alive") is not False
        or (
            record.get("state") == "CHECKPOINTED"
            and not base._is_sha256(
                record.get("checkpoint_commit_sha256")
            )
        )
        or (
            record.get("state") == "INACTIVE_UNCHECKPOINTED"
            and record.get("checkpoint_commit_sha256") is not None
        )
        or record.get("writable_holders") != []
        or not base._is_sha256(record.get("proof_sha256"))
        or type(record.get("proof_bytes")) is not int
        or record["proof_bytes"] < 0 or record["proof_bytes"] > MAX_PROOF_BYTES
    ):
        raise AdaptiveSwitchEvidenceV3Error("quiescence record invalid")
    return dict(record)


def _read_handoff_journal(
    path: Path, *, expected_fields: set[str], expected_kind: str,
) -> dict[str, Any]:
    value = base._read_json(path)
    lexical = path.lstat()
    if (
        set(value) != expected_fields
        or not selfhash_valid(value)
        or value.get("schema_version") != SCHEMA_VERSION
        or type(value.get("schema_version")) is not int
        or value.get("kind") != expected_kind
        or value.get("authenticated") is not False
        or value.get("launch_authorized") is not False
        or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o600
        or lexical.st_nlink != 1
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff journal schema/ownership mismatch"
        )
    return value


def _verify_committed_journals(
    root: Path, record: Mapping[str, Any],
) -> list[dict[str, Any]]:
    target_fields = {
        "schema_version", "kind", "authenticated", "launch_authorized",
        "lane_index", "global_leaf_index", "descendant_index",
        "descendant_sha256", "overlay_manifest_sha256",
        "hard_evidence_sha256", "permit_binding_sha256",
        "new_root_identity", "switch_evidence_sha256",
        "prepared_retirement_sha256", "record_sha256",
    }
    started_fields = {
        "schema_version", "kind", "authenticated", "launch_authorized",
        "lane_index", "descendant_index", "prepared_target_sha256",
        "permit_binding_sha256", "new_root_identity", "new_pid",
        "new_proc_start_ticks", "switch_evidence_sha256",
        "prepared_retirement_sha256", "record_sha256",
    }
    bindings = record.get("root_bindings")
    if type(bindings) is not list or len(bindings) != TARGET_COUNT:
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff journal binding cardinality mismatch"
        )
    verified: list[dict[str, Any]] = []
    for key, binding in zip(TARGET_KEYS, bindings, strict=True):
        if (
            type(binding) is not dict
            or (
                binding.get("lane_index"),
                binding.get("descendant_index"),
            ) != key
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "handoff journal target order mismatch"
            )
        target_path = (
            root / TARGET_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        started_path = (
            root / STARTED_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        target = _read_handoff_journal(
            target_path, expected_fields=target_fields,
            expected_kind="paper400-adaptive-prepared-target-v3",
        )
        started = _read_handoff_journal(
            started_path, expected_fields=started_fields,
            expected_kind="paper400-adaptive-started-worker-v3",
        )
        root_identity = binding.get("new_root_identity")
        if (
            type(target.get("lane_index")) is not int
            or type(target.get("global_leaf_index")) is not int
            or type(target.get("descendant_index")) is not int
            or (target["lane_index"], target["descendant_index"]) != key
            or target["global_leaf_index"]
                != binding.get("global_leaf_index")
            or target.get("descendant_sha256")
                != binding.get("descendant_sha256")
            or target.get("permit_binding_sha256")
                != binding.get("permit_binding_sha256")
            or target.get("record_sha256")
                != binding.get("prepared_target_sha256")
            or target.get("switch_evidence_sha256")
                != record.get("switch_evidence_sha256")
            or target.get("prepared_retirement_sha256")
                != record.get("prepared_retirement_sha256")
            or any(
                not base._is_sha256(target.get(field))
                for field in (
                    "descendant_sha256", "overlay_manifest_sha256",
                    "hard_evidence_sha256", "permit_binding_sha256",
                    "record_sha256",
                )
            )
            or type(root_identity) is not dict
            or not json_type_equal(
                target.get("new_root_identity"), root_identity
            )
            or not json_type_equal(
                base._root_identity(Path(root_identity.get("path", ""))),
                root_identity,
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "prepared-target journal misses commit"
            )
        if (
            type(started.get("lane_index")) is not int
            or type(started.get("descendant_index")) is not int
            or (started["lane_index"], started["descendant_index"]) != key
            or started.get("prepared_target_sha256")
                != target["record_sha256"]
            or started.get("permit_binding_sha256")
                != binding.get("permit_binding_sha256")
            or started.get("record_sha256")
                != binding.get("started_worker_journal_sha256")
            or started.get("switch_evidence_sha256")
                != record.get("switch_evidence_sha256")
            or started.get("prepared_retirement_sha256")
                != record.get("prepared_retirement_sha256")
            or not json_type_equal(
                started.get("new_root_identity"), root_identity
            )
            or started.get("new_pid") != binding.get("new_pid")
            or started.get("new_proc_start_ticks")
                != binding.get("new_proc_start_ticks")
            or type(started.get("new_pid")) is not int
            or type(started.get("new_proc_start_ticks")) is not int
            or started["new_pid"] <= 0
            or started["new_proc_start_ticks"] <= 0
            or any(
                not base._is_sha256(started.get(field))
                for field in (
                    "prepared_target_sha256", "permit_binding_sha256",
                    "record_sha256",
                )
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "started-worker journal misses commit"
            )
        quiescence_path = (
            root / QUIESCENCE_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        if key[1] == 0:
            quiescence = _validate_quiescence_record(
                base._read_json(quiescence_path)
            )
            lexical = quiescence_path.lstat()
            if (
                stat.S_ISLNK(lexical.st_mode)
                or not stat.S_ISREG(lexical.st_mode)
                or lexical.st_uid != os.geteuid()
                or stat.S_IMODE(lexical.st_mode) != 0o600
                or lexical.st_nlink != 1
                or quiescence["state"] != "CHECKPOINTED"
                or (
                    quiescence["lane_index"],
                    quiescence["descendant_index"],
                ) != key
                or quiescence["record_sha256"]
                    != binding.get("cohort_quiescence_sha256")
                or quiescence["new_pid"] != binding.get("new_pid")
                or quiescence["new_proc_start_ticks"]
                    != binding.get("new_proc_start_ticks")
                or not json_type_equal(
                    quiescence["new_root_identity"], root_identity
                )
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "cohort quiescence journal misses commit"
                )
        elif (
            binding.get("cohort_quiescence_sha256") is not None
            or quiescence_path.exists() or quiescence_path.is_symlink()
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "running cohort has a quiescence journal"
            )
        verified.append({
            "lane_index": key[0], "descendant_index": key[1],
            "prepared_target_sha256": target["record_sha256"],
            "started_worker_journal_sha256":
                started["record_sha256"],
            "cohort_quiescence_sha256":
                binding.get("cohort_quiescence_sha256"),
        })
    return verified


def _acquire_new_root_fences(
    root_identities: Sequence[Mapping[str, Any]], *,
    controller_root_identities:
        Sequence[Mapping[str, Any]] | None = None,
    already_held: Sequence[Any] = (),
) -> list[Any]:
    identities = [dict(item) for item in root_identities]
    by_root = {
        Path(item.get("path", "")): item for item in identities
    }
    if (
        len(by_root) != len(identities)
        or any(
            not json_type_equal(base._root_identity(path), identity)
            for path, identity in by_root.items()
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error("new root fence identities malformed")
    if controller_root_identities is None:
        controller_by_root = dict(by_root)
    else:
        controller_identities = [
            dict(item) for item in controller_root_identities
        ]
        controller_by_root = {
            Path(item.get("path", "")): item
            for item in controller_identities
        }
        if (
            len(controller_by_root) != len(controller_identities)
            or not set(controller_by_root) <= set(by_root)
            or any(
                not json_type_equal(base._root_identity(path), identity)
                for path, identity in controller_by_root.items()
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "controller root fence identities malformed"
            )
    plan: list[tuple[Path, str, int]] = []
    for path in by_root:
        plan.append((
            path / ".adaptive-child.lock",
            f"new-root:{path}", fcntl.LOCK_EX,
        ))
    for path in controller_by_root:
        plan.append((
            path / "runtime/dmtcp/.controller.lock",
            f"new-controller:{path}", fcntl.LOCK_SH,
        ))
    plan.sort(key=lambda item: str(item[0]))
    retained = {Path(item.current_path): item for item in already_held}
    if (
        len(retained) != len(already_held)
        or not set(retained) <= {item[0] for item in plan}
    ):
        raise AdaptiveSwitchEvidenceV3Error("retained new-root locks malformed")
    for path, _, _ in plan:
        if path not in retained:
            continue
        item = retained[path]
        observed = base._stat_identity(path.lstat())
        if (
            Path(item.current_path) != path
            or not json_type_equal(observed, base._stat_identity(os.fstat(item.fd)))
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "retained new-root lock identity changed"
            )
    acquired: list[Any] = []
    try:
        for path, role, operation in plan:
            if path not in retained:
                acquired.append(base._HeldLock(path, role, operation))
        return acquired
    except BaseException:
        _close_locks(acquired)
        raise


def _close_locks(locks: Sequence[Any]) -> None:
    for held in reversed(locks):
        held.close()


def _adopt_exclusive_outer_locks(
    root_identities: Sequence[Mapping[str, Any]],
    outer_lock_fds: Sequence[int],
) -> list[Any]:
    """Duplicate eight already-held EX flock OFDs without a release window."""

    identities = [dict(item) for item in root_identities]
    if (
        type(outer_lock_fds) is not list
        or len(identities) != TARGET_COUNT
        or len(outer_lock_fds) != TARGET_COUNT
        or len(set(outer_lock_fds)) != TARGET_COUNT
        or any(type(item) is not int or item < 0 for item in outer_lock_fds)
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "outer lock transfer cardinality malformed"
        )
    expected: dict[tuple[int, int], tuple[Path, dict[str, Any]]] = {}
    for identity in identities:
        root = Path(identity.get("path", ""))
        if not json_type_equal(base._root_identity(root), identity):
            raise AdaptiveSwitchEvidenceV3Error(
                "outer lock transfer root changed"
            )
        path = root / ".adaptive-child.lock"
        lexical = path.lstat()
        key = (int(lexical.st_dev), int(lexical.st_ino))
        if key in expected:
            raise AdaptiveSwitchEvidenceV3Error(
                "outer lock transfer root duplicated"
            )
        expected[key] = (path, base._stat_identity(lexical))
    adopted: list[Any] = []
    seen: set[tuple[int, int]] = set()
    try:
        for source_fd in outer_lock_fds:
            flags = fcntl.fcntl(source_fd, fcntl.F_GETFL)
            observed = os.fstat(source_fd)
            key = (int(observed.st_dev), int(observed.st_ino))
            if (
                key not in expected or key in seen
                or stat.S_IFMT(observed.st_mode) != stat.S_IFREG
                or stat.S_IMODE(observed.st_mode) != 0o600
                or observed.st_uid != os.geteuid()
                or observed.st_nlink != 1 or observed.st_size != 0
                or (flags & os.O_ACCMODE) != os.O_RDWR
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "outer lock transfer fd is unsafe"
                )
            path, identity = expected[key]
            if not json_type_equal(
                base._stat_identity(observed), identity
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "outer lock transfer inode changed"
                )
            duplicate = fcntl.fcntl(
                source_fd, fcntl.F_DUPFD_CLOEXEC, 3
            )
            held = object.__new__(base._HeldLock)
            held.fd = duplicate
            held.role = f"new-root:{path.parent}"
            held.original_path = path
            held.current_path = path
            held.identity = dict(identity)
            held.operation = fcntl.LOCK_EX
            try:
                fcntl.flock(duplicate, fcntl.LOCK_EX | fcntl.LOCK_NB)
                probe = os.open(
                    path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW
                )
                try:
                    try:
                        fcntl.flock(
                            probe, fcntl.LOCK_EX | fcntl.LOCK_NB
                        )
                    except BlockingIOError:
                        pass
                    else:
                        fcntl.flock(probe, fcntl.LOCK_UN)
                        raise AdaptiveSwitchEvidenceV3Error(
                            "transferred fd did not hold exclusive flock"
                        )
                finally:
                    os.close(probe)
            except BaseException:
                held.close()
                raise
            adopted.append(held)
            seen.add(key)
        if seen != set(expected):
            raise AdaptiveSwitchEvidenceV3Error(
                "outer lock transfer misses prepared roots"
            )
        adopted.sort(key=lambda item: str(item.current_path))
        return adopted
    except BaseException:
        _close_locks(adopted)
        raise


def _acquire_retired_old_locks(
    retirements: Sequence[Mapping[str, Any]],
) -> tuple[list[Any], dict[str, Any]]:
    by_role = {
        item.get("role"): dict(item) for item in retirements
        if type(item) is dict
    }
    roles = [
        "batch", *(f"lane-{index}" for index in range(LANE_COUNT)),
        *(f"controller-{index}" for index in range(LANE_COUNT)),
    ]
    if set(by_role) != set(roles):
        raise AdaptiveSwitchEvidenceV3Error("old retirement roles malformed")
    held: list[Any] = []
    try:
        for role in roles:
            operation = (
                fcntl.LOCK_SH if role.startswith("controller-")
                else fcntl.LOCK_EX
            )
            record = by_role[role]
            item = base._HeldLock(
                Path(record["retired_path"]), f"old-retired:{role}", operation
            )
            if not json_type_equal(item.identity, record["identity"]):
                item.close()
                raise AdaptiveSwitchEvidenceV3Error(
                    "old retired inode misses commit"
                )
            held.append(item)
        return held, by_role
    except BaseException:
        _close_locks(held)
        raise


def _restore_external_old_lock(
    held: Any, retirement: Mapping[str, Any],
) -> dict[str, Any]:
    retired = Path(retirement["retired_path"])
    original = Path(retirement["original_path"])
    if (
        Path(held.original_path) != retired
        or Path(held.current_path) != retired
        or original.exists() or original.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old restore target unsafe"
        )
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(path_identity, retirement["identity"])
        or not json_type_equal(fd_identity, retirement["identity"])
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old retired inode changed"
        )
    os.rename(retired, original)
    _fsync_directory(original.parent)
    restored = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(
            restored, base._stat_identity(original.lstat())
        )
        or not json_type_equal(
            _identity_without_ctime(fd_identity),
            _identity_without_ctime(restored),
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old restore identity changed"
        )
    held.current_path = original
    return {
        "role": retirement["role"], "original_path": str(original),
        "retired_path": str(retired), "identity": restored,
    }


def _reretire_external_old_lock(
    held: Any, retirement: Mapping[str, Any],
) -> dict[str, Any]:
    original = Path(retirement["original_path"])
    retired = Path(retirement["retired_path"])
    if (
        Path(held.current_path) != original
        or retired.exists() or retired.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old compensation target unsafe"
        )
    before = base._stat_identity(os.fstat(held.fd))
    if not json_type_equal(before, base._stat_identity(original.lstat())):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old restore changed before compensation"
        )
    os.rename(original, retired)
    _fsync_directory(retired.parent)
    after = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(after, base._stat_identity(retired.lstat()))
        or not json_type_equal(
            _identity_without_ctime(before), _identity_without_ctime(after)
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "external old compensation identity changed"
        )
    held.current_path = retired
    return {
        "role": retirement["role"], "original_path": str(original),
        "retired_path": str(retired), "identity": after,
    }


def _lock_plan(locks: Sequence[Any], suffix: str) -> list[dict[str, Any]]:
    ordered = [*locks[5:], *locks[1:5], locks[0]]
    result: list[dict[str, Any]] = []
    for sequence, held in enumerate(ordered):
        retired = held.original_path.with_name(
            held.original_path.name + f".retired-v3-{suffix}"
        )
        result.append({
            "sequence": sequence, "role": held.role,
            "original_path": str(held.original_path),
            "retired_path": str(retired),
            "pre_rename_identity": dict(held.identity),
        })
    return result


def _direct_controller_inspect(child: Any, lane_root: Path) -> dict[str, Any]:
    controller = child.controller
    runtime = lane_root / child.RUNTIME_ROOT
    with child._fixed_environment():
        config, binaries = controller._load_and_verify_config(runtime)
        numbers = controller._generation_numbers(runtime)
        generations = [
            controller._generation_summary(runtime, number, verify_hashes=True)
            for number in numbers
        ]
        command_hash = controller.stable_file_record(
            binaries["dmtcp_command"]
        )["sha256"]
    if not numbers:
        state = "INITIALIZED"
    elif any(
        item.get("poison_claim") or item.get("active_error")
        or item.get("checkpoint_error") for item in generations
    ):
        state = "POISONED"
    elif generations[-1].get("checkpointed"):
        state = "CHECKPOINTED"
    elif generations[-1].get("pid_identity_alive"):
        state = "RUNNING"
    else:
        state = "INACTIVE_UNCHECKPOINTED"
    return {
        "authority": controller.AUTHORITY,
        "config_manifest_sha256": config["self_sha256"],
        "dmtcp_command_sha256": command_hash,
        "generations": generations,
        "hash_verification_requested": True,
        "root": str(runtime.resolve(strict=True)), "state": state,
    }


def _fresh_restored_old_checkpoint(
    root: Path, *, expected_batch_manifest_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_switch_record: Mapping[str, Any],
    switch_observation_policy: Mapping[str, Any],
) -> dict[str, Any]:
    if (
        type(expected_switch_record) is not dict
        or not selfhash_valid(expected_switch_record)
        or expected_switch_record.get("record_sha256")
            != expected_switch_evidence_sha256
        or expected_switch_record.get("batch_manifest_sha256")
            != expected_batch_manifest_sha256
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "expected switch record misses external pins"
        )
    validate_switch_record_structure(expected_switch_record)
    discovery = base._discover_sources(
        root,
        expected_batch_manifest_sha256=expected_batch_manifest_sha256,
    )
    coordinator, child, executed = _load_legacy_exact(discovery)
    overlay, overlay_record, overlay_executed = _load_overlay_exact()
    snapshot = base._snapshot_locked(root, coordinator, child)
    policy = dict(switch_observation_policy)
    replay = base._build_record(
        root, snapshot, discovery, overlay, executed,
        overlay_record, overlay_executed,
        timeout_seconds=policy["timeout_seconds"],
        elapsed_seconds_by_lane=policy["elapsed_seconds_by_lane"],
    )
    validate_switch_record_structure(replay)
    if (
        snapshot["manifest"].get("record_sha256")
        != expected_batch_manifest_sha256
        or replay.get("batch_manifest_sha256")
        != expected_batch_manifest_sha256
        or replay.get("record_sha256")
        != expected_switch_evidence_sha256
        or not json_type_equal(replay, expected_switch_record)
        or len(snapshot.get("lanes", [])) != LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "restored old checkpoint misses exact switch pin"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-restored-old-checkpoint-replay-v3",
        "batch_manifest_sha256": expected_batch_manifest_sha256,
        "switch_evidence_sha256": expected_switch_evidence_sha256,
        "exact_switch_record_rebuilt": True,
        "checkpoint_result_sha256":
            snapshot["checkpoint_result"]["record_sha256"],
        "lane_transport_chain_sha256s": [
            lane["chain"]["record_sha256"] for lane in snapshot["lanes"]
        ],
        "lane_proof_prefixes": [
            dict(lane["chain"]["latest_proof_prefix"])
            for lane in snapshot["lanes"]
        ],
        "executed_source_closure": executed,
        "overlay_executed_source_closure": overlay_executed,
        "authenticated": False, "launch_authorized": False,
    })


def _writable_holders(
    path: Path, *, expected_identity: Mapping[str, Any] | None = None,
) -> list[int]:
    wanted = os.stat(path, follow_symlinks=False)
    if (
        not stat.S_ISREG(wanted.st_mode)
        or (
            expected_identity is not None
            and not json_type_equal(
                base._stat_identity(wanted), expected_identity
            )
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "proof is not the expected regular inode"
        )
    holders: set[int] = set()
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            descriptors = list((process / "fd").iterdir())
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError as exc:
            raise AdaptiveSwitchEvidenceV3Error("cannot inspect process fds") from exc
        for descriptor in descriptors:
            try:
                observed = os.stat(descriptor)
                if (observed.st_dev, observed.st_ino) != (wanted.st_dev, wanted.st_ino):
                    continue
                lines = (process / "fdinfo" / descriptor.name).read_text(
                    encoding="ascii"
                ).splitlines()
                flags = [item for item in lines if item.startswith("flags:")]
                if len(flags) != 1:
                    raise AdaptiveSwitchEvidenceV3Error("ambiguous descriptor flags")
                value = int(flags[0].split(":", 1)[1].strip(), 8)
                if value & os.O_ACCMODE != os.O_RDONLY:
                    holders.add(int(process.name))
            except (FileNotFoundError, ProcessLookupError):
                continue
            except PermissionError as exc:
                raise AdaptiveSwitchEvidenceV3Error("cannot inspect fd flags") from exc
    final_identity = base._stat_identity(
        os.stat(path, follow_symlinks=False)
    )
    wanted_identity = base._stat_identity(wanted)
    if (
        not json_type_equal(wanted_identity, final_identity)
        or (
            expected_identity is not None
            and not json_type_equal(final_identity, expected_identity)
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "proof changed during writer scan"
        )
    return sorted(holders)


class StartedWorker:
    __slots__ = (
        "_lease", "_lease_nonce", "_token", "permit_binding_sha256",
        "lane_index", "descendant_index", "new_root_identity",
        "new_pid", "new_proc_start_ticks",
        "prepared_target_sha256", "started_worker_journal_sha256",
        "_fenced",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", permit: Any, *,
        new_root_identity: Mapping[str, Any], new_pid: int,
        new_proc_start_ticks: int, prepared_target_sha256: str,
        started_worker_journal_sha256: str,
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self._token = uuid.uuid4().hex
        self.permit_binding_sha256 = permit.permit_binding_sha256
        self.lane_index = permit.lane_index
        self.descendant_index = permit.descendant_index
        self.new_root_identity = dict(new_root_identity)
        self.new_pid = new_pid
        self.new_proc_start_ticks = new_proc_start_ticks
        self.prepared_target_sha256 = prepared_target_sha256
        self.started_worker_journal_sha256 = (
            started_worker_journal_sha256
        )
        self._fenced = False

    def __reduce__(self) -> Any:
        raise TypeError("StartedWorker cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("StartedWorker cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("StartedWorker cannot be copied")



class PostStartFence(base.PostStartFence):
    __slots__ = (
        "prepared_target_sha256", "started_worker_journal_sha256",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", permit: Any, *,
        started_worker: StartedWorker, new_session_sha256: str,
        new_start_commit_sha256: str,
    ) -> None:
        self.prepared_target_sha256 = (
            started_worker.prepared_target_sha256
        )
        self.started_worker_journal_sha256 = (
            started_worker.started_worker_journal_sha256
        )
        super().__init__(
            lease, permit,
            new_root_identity=started_worker.new_root_identity,
            new_session_sha256=new_session_sha256,
            new_start_commit_sha256=new_start_commit_sha256,
            new_pid=started_worker.new_pid,
            new_proc_start_ticks=started_worker.new_proc_start_ticks,
        )

    def audit_binding(self) -> dict[str, Any]:
        result = super().audit_binding()
        result["prepared_target_sha256"] = self.prepared_target_sha256
        result["started_worker_journal_sha256"] = (
            self.started_worker_journal_sha256
        )
        return result


class CohortTransitionPermit:
    __slots__ = (
        "_lease", "_lease_nonce", "_token", "_used",
        "quiescence_sha256s",
    )

    def __init__(
        self, lease: "AtomicSwitchLease",
        quiescence_sha256s: Sequence[str],
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self._token = uuid.uuid4().hex
        self._used = False
        self.quiescence_sha256s = tuple(quiescence_sha256s)

    def __reduce__(self) -> Any:
        raise TypeError("CohortTransitionPermit cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("CohortTransitionPermit cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("CohortTransitionPermit cannot be copied")

class AtomicSwitchLease(base.AtomicSwitchLease):
    __slots__ = (
        "_prepared", "_retired_records", "_target_records",
        "_started_workers", "_outer_locks", "_cohort0_quiescence",
        "_cohort_transition_nonce", "_cohort_locks",
        "_rolled_back", "_v3_sources",
    )

    def __init__(self, *args: Any, v3_sources: Mapping[str, Any], **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        self._prepared: dict[str, Any] | None = None
        self._retired_records: list[dict[str, Any]] = []
        self._target_records: dict[
            tuple[int, int], dict[str, Any]
        ] = {}
        self._started_workers: dict[
            tuple[int, int], StartedWorker
        ] = {}
        self._outer_locks: list[Any] = []
        self._cohort0_quiescence: dict[
            tuple[int, int], dict[str, Any]
        ] = {}
        self._cohort_transition_nonce: str | None = None
        self._cohort_locks: list[Any] = []
        self._rolled_back = False
        self._v3_sources = dict(v3_sources)

    def _assert_retirement_intact(self) -> None:
        self._assert_active()
        if self._prepared is None or len(self._retired_records) != 9:
            raise AdaptiveSwitchEvidenceV3Error("retirement was not prepared")
        for held, record in zip(
            [*self._locks[5:], *self._locks[1:5], self._locks[0]],
            self._retired_records, strict=True,
        ):
            original = Path(record["original_path"])
            retired = Path(record["retired_path"])
            if original.exists() or original.is_symlink():
                raise AdaptiveSwitchEvidenceV3Error("legacy lock entry point reappeared")
            observed = retired.lstat()
            if (
                stat.S_ISLNK(observed.st_mode) or not stat.S_ISREG(observed.st_mode)
                or not json_type_equal(base._stat_identity(observed), record["identity"])
                or not json_type_equal(base._stat_identity(os.fstat(held.fd)), record["identity"])
            ):
                raise AdaptiveSwitchEvidenceV3Error("retired lock identity changed")

    def _old_post_retirement_fence(self) -> None:
        self._assert_retirement_intact()
        for index, runtime_lane in enumerate(self._snapshot["lanes"]):
            lane_root = self._root / "lanes" / f"lane-{index}"
            chain = runtime_lane["chain"]
            active = chain["generations"][-1]
            if self._child.controller._pid_identity(
                active["pid"], active["proc_start_ticks"]
            ):
                raise AdaptiveSwitchEvidenceV3Error("old solver became live")
            inspection = _direct_controller_inspect(self._child, lane_root)
            if (
                inspection.get("state") != "CHECKPOINTED"
                or not json_type_equal(inspection, runtime_lane["inspection"])
            ):
                raise AdaptiveSwitchEvidenceV3Error("old controller state/hash changed")
            proof = lane_root / self._child.RUNTIME_ROOT / "proof.drat"
            record = self._child.controller.stable_file_record(
                proof, relative_to=lane_root / self._child.RUNTIME_ROOT
            )
            if (
                record != chain["latest_proof_prefix"]
                or _writable_holders(proof) != []
                or (lane_root / self._child.TERMINAL_CLAIM).exists()
                or (lane_root / self._child.FINAL_COMMIT).exists()
            ):
                raise AdaptiveSwitchEvidenceV3Error("old proof/terminal state changed")

    def prepare_retirement(self) -> dict[str, Any]:
        self._assert_active()
        if self._candidate_only or self._prepared is not None:
            raise AdaptiveSwitchEvidenceV3Error("retirement cannot be prepared")
        suffix = self._record["record_sha256"][:16]
        target_directory = _make_journal_directory(
            self._root, TARGET_DIRECTORY
        )
        started_directory = _make_journal_directory(
            self._root, STARTED_DIRECTORY
        )
        quiescence_directory = _make_journal_directory(
            self._root, QUIESCENCE_DIRECTORY
        )
        plan = _lock_plan(self._locks, suffix)
        intent = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-adaptive-retirement-intent-v3",
            "gate": GATE, "test_only": True, "production_eligible": False,
            "authenticated": False, "launch_authorized": False,
            "batch_root": str(self._root),
            "batch_manifest_sha256": self._record["batch_manifest_sha256"],
            "switch_evidence_sha256": self._record["record_sha256"],
            "target_journal_directory": str(target_directory),
            "started_journal_directory": str(started_directory),
            "quiescence_journal_directory": str(quiescence_directory),
            "lock_plan": plan, "retirement_complete": False,
            "source_binding": self._v3_sources,
        })
        _publish(self._root / RETIREMENT_INTENT, intent)
        ordered = [*self._locks[5:], *self._locks[1:5], self._locks[0]]
        retired: list[dict[str, Any]] = []
        try:
            for sequence, held in enumerate(ordered):
                record = _retire_lock_v3(
                    held, Path(plan[sequence]["retired_path"])
                )
                retired.append({"sequence": sequence, **record})
                if (
                    record["role"] != plan[sequence]["role"]
                    or record["original_path"]
                    != plan[sequence]["original_path"]
                    or record["retired_path"]
                    != plan[sequence]["retired_path"]
                    or not json_type_equal(
                        record["pre_rename_identity"],
                        plan[sequence]["pre_rename_identity"],
                    )
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "retirement plan drift"
                    )
            prepared = seal({
                "schema_version": SCHEMA_VERSION, "kind": PREPARED_KIND,
                "gate": GATE, "test_only": True,
                "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False, "batch_root": str(self._root),
                "batch_root_identity": base._root_identity(self._root),
                "batch_manifest_sha256":
                    self._record["batch_manifest_sha256"],
                "switch_evidence_sha256": self._record["record_sha256"],
                "retirement_intent_sha256": intent["record_sha256"],
                "retired_locks": retired, "retirement_complete": True,
                "old_runner_entrypoints_reachable": False,
                "source_binding": self._v3_sources,
            })
            _publish(self._root / PREPARED_COMMIT, prepared)
            self._retired_records = retired
            self._prepared = prepared
            self._old_post_retirement_fence()
            return json.loads(canonical_bytes(prepared))
        except BaseException as retirement_error:
            restore_failures: list[BaseException] = []
            for sequence in reversed(range(len(ordered))):
                held = ordered[sequence]
                try:
                    _restore_current_lock_v3(
                        held,
                        original_path=Path(
                            plan[sequence]["original_path"]
                        ),
                        retired_path=Path(
                            plan[sequence]["retired_path"]
                        ),
                    )
                except BaseException as exc:
                    restore_failures.append(exc)
            if restore_failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "pre-yield retirement failed and old restore failed"
                ) from restore_failures[0]
            self._retired_records = []
            self._prepared = None
            try:
                snapshot = base._snapshot_locked(
                    self._root, self._coordinator, self._child
                )
                replay = base._build_record(
                    self._root, snapshot, self._discovery, self._overlay,
                    self._legacy_executed, self._overlay_record,
                    self._overlay_executed,
                    timeout_seconds=self._timeout,
                    elapsed_seconds_by_lane=self._elapsed,
                )
                if not json_type_equal(replay, self._record):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "restored pre-yield old state misses fresh replay"
                    )
            except BaseException as replay_error:
                reretire_failures: list[BaseException] = []
                for sequence, held in enumerate(ordered):
                    try:
                        if Path(held.current_path) == Path(
                            plan[sequence]["original_path"]
                        ):
                            _retire_lock_v3(
                                held,
                                Path(plan[sequence]["retired_path"]),
                            )
                    except BaseException as exc:
                        reretire_failures.append(exc)
                message = (
                    "pre-yield compensation replay failed; old entrypoints "
                    "were re-retired"
                )
                if reretire_failures:
                    message += " with additional retirement failures"
                raise AdaptiveSwitchEvidenceV3Error(message) from replay_error
            raise retirement_error

    def _fresh_record(self) -> dict[str, Any]:
        # Once the lock names are retired the legacy loader correctly refuses
        # to replay its session.  Equivalent post-retirement checking is done
        # directly under the still-held original inodes.
        if self._prepared is not None:
            self._old_post_retirement_fence()
            return dict(self._record)
        return super()._fresh_record()

    def verify_target(
        self, overlay_manifest: Mapping[str, Any], *,
        expected_overlay_sha256: str, global_leaf_index: int,
        expected_hard_evidence_sha256: str,
        candidate_variables: list[int], descendant_index: int,
        expected_descendant_sha256: str,
    ) -> Any:
        matches = [
            lane for lane in self._record["lanes"]
            if lane["global_leaf_index"] == global_leaf_index
        ]
        if len(matches) != 1:
            raise AdaptiveSwitchEvidenceV3Error(
                "target is not one old batch lane"
            )
        lane_index = matches[0]["lane_index"]
        key = (lane_index, descendant_index)
        if key not in TARGET_KEYS or key in self._permits:
            raise AdaptiveSwitchEvidenceV3Error(
                "target permit is duplicated/malformed"
            )
        permit = super().verify_target(
            overlay_manifest,
            expected_overlay_sha256=expected_overlay_sha256,
            global_leaf_index=global_leaf_index,
            expected_hard_evidence_sha256=
                expected_hard_evidence_sha256,
            candidate_variables=candidate_variables,
            descendant_index=descendant_index,
            expected_descendant_sha256=expected_descendant_sha256,
        )
        transient = self._permits.pop(lane_index, None)
        if transient is not permit:
            raise AdaptiveSwitchEvidenceV3Error(
                "base target permit registry drift"
            )
        self._permits[key] = permit
        return permit

    def prepare_target(
        self, *, permit: Any, new_root_identity: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Durably bind a verified permit to its root before spawning."""

        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        if (
            type(permit) is not base.LaunchPermit or permit._lease is not self
            or permit._lease_nonce != self._nonce or permit._used
            or key not in TARGET_KEYS
            or self._permits.get(key) is not permit
            or key in self._target_records
            or key in self._started_workers
        ):
            raise AdaptiveSwitchEvidenceV3Error("prepared target permit is invalid")
        if (
            type(new_root_identity) is not dict
            or type(new_root_identity.get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV3Error("prepared root identity malformed")
        root = base._root_identity(Path(new_root_identity["path"]))
        if not json_type_equal(root, new_root_identity):
            raise AdaptiveSwitchEvidenceV3Error("prepared root identity changed")
        if any(
            item["new_root_identity"]["path"] == root["path"]
            for item in self._target_records.values()
        ):
            raise AdaptiveSwitchEvidenceV3Error("prepared root is duplicated")
        record = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-adaptive-prepared-target-v3",
            "authenticated": False, "launch_authorized": False,
            "lane_index": permit.lane_index,
            "global_leaf_index": permit.global_leaf_index,
            "descendant_index": permit.descendant_index,
            "descendant_sha256": permit.descendant_sha256,
            "overlay_manifest_sha256": permit.overlay_manifest_sha256,
            "hard_evidence_sha256": permit.hard_evidence_sha256,
            "permit_binding_sha256": permit.permit_binding_sha256,
            "new_root_identity": root,
            "switch_evidence_sha256": self._record["record_sha256"],
            "prepared_retirement_sha256": self._prepared["record_sha256"],
        })
        _publish(
            self._root / TARGET_DIRECTORY
            / (
                f"lane-{permit.lane_index}-"
                f"descendant-{permit.descendant_index}.json"
            ),
            record,
        )
        self._target_records[key] = record
        return json.loads(canonical_bytes(record))

    def adopt_prepared_outer_locks(
        self, *, outer_lock_fds: list[int],
    ) -> None:
        """Take continuous ownership of all eight runner-held outer locks."""

        self._assert_retirement_intact()
        if (
            self._candidate_only or self._committed or self._rolled_back
            or self._outer_locks or self._started_workers
            or set(self._target_records) != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "prepared outer locks cannot be adopted"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        locks = _adopt_exclusive_outer_locks(
            identities, outer_lock_fds
        )
        try:
            self._old_post_retirement_fence()
        except BaseException:
            _close_locks(locks)
            raise
        self._outer_locks = locks

    def note_started_worker(
        self, *, permit: Any, new_root_identity: Mapping[str, Any],
        new_pid: int, new_proc_start_ticks: int,
        cohort_transition_permit: CohortTransitionPermit | None = None,
    ) -> StartedWorker:
        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        target_record = self._target_records.get(key)
        transition_valid = (
            type(cohort_transition_permit) is CohortTransitionPermit
            and cohort_transition_permit._lease is self
            and cohort_transition_permit._lease_nonce == self._nonce
            and self._cohort_transition_nonce
                == cohort_transition_permit._token
            and not cohort_transition_permit._used
        )
        if (
            type(permit) is not base.LaunchPermit or permit._lease is not self
            or permit._lease_nonce != self._nonce or permit._used
            or key not in TARGET_KEYS
            or self._permits.get(key) is not permit
            or type(target_record) is not dict
            or len(self._target_records) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or len(self._outer_locks) != TARGET_COUNT
            or key in self._started_workers
            or (
                permit.descendant_index == 0
                and cohort_transition_permit is not None
            )
            or (
                permit.descendant_index == 1
                and not transition_valid
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error("started worker permit is invalid")
        if type(new_pid) is not int or type(new_proc_start_ticks) is not int:
            raise AdaptiveSwitchEvidenceV3Error("new PID identity must be strict ints")
        if base._proc_start_ticks(new_pid) != new_proc_start_ticks:
            raise AdaptiveSwitchEvidenceV3Error("new PID identity is not alive")
        live_existing = 0
        for worker in self._started_workers.values():
            try:
                if (
                    base._proc_start_ticks(worker.new_pid)
                    == worker.new_proc_start_ticks
                ):
                    live_existing += 1
            except Exception:
                pass
        if live_existing >= MAX_LIVE_WORKERS:
            raise AdaptiveSwitchEvidenceV3Error(
                "max-live cohort invariant would be exceeded"
            )
        if (
            type(new_root_identity) is not dict
            or type(new_root_identity.get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV3Error("new root identity malformed")
        root = base._root_identity(Path(new_root_identity["path"]))
        if (
            not json_type_equal(root, new_root_identity)
            or not json_type_equal(root, target_record["new_root_identity"])
        ):
            raise AdaptiveSwitchEvidenceV3Error("new root identity changed")
        journal = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-adaptive-started-worker-v3",
            "authenticated": False, "launch_authorized": False,
            "lane_index": permit.lane_index,
            "descendant_index": permit.descendant_index,
            "prepared_target_sha256": target_record["record_sha256"],
            "permit_binding_sha256": permit.permit_binding_sha256,
            "new_root_identity": root, "new_pid": new_pid,
            "new_proc_start_ticks": new_proc_start_ticks,
            "switch_evidence_sha256": self._record["record_sha256"],
            "prepared_retirement_sha256": self._prepared["record_sha256"],
        })
        started = StartedWorker(
            self, permit, new_root_identity=root, new_pid=new_pid,
            new_proc_start_ticks=new_proc_start_ticks,
            prepared_target_sha256=target_record["record_sha256"],
            started_worker_journal_sha256=journal["record_sha256"],
        )
        # The process exists already.  Register it before the durable publish,
        # so an I/O fault cannot misclassify this lane as never-started.
        self._started_workers[key] = started
        if (
            permit.descendant_index == 1
            and all(
                (lane, 1) in self._started_workers
                for lane in range(LANE_COUNT)
            )
        ):
            cohort_transition_permit._used = True
        _publish(
            self._root / STARTED_DIRECTORY
            / (
                f"lane-{permit.lane_index}-"
                f"descendant-{permit.descendant_index}.json"
            ),
            journal,
        )
        return started

    def started_target_keys(self) -> tuple[tuple[int, int], ...]:
        """Return process-local truth for cleanup after a note fault."""

        self._assert_active()
        return tuple(
            key for key in TARGET_KEYS if key in self._started_workers
        )

    def _verify_quiescent_worker(
        self, key: tuple[int, int], record: Mapping[str, Any], *,
        require_checkpointed: bool = False,
    ) -> dict[str, Any]:
        checked = _validate_quiescence_record(record)
        worker = self._started_workers.get(key)
        target = self._target_records.get(key)
        if (
            worker is None or target is None
            or (
                require_checkpointed
                and checked["state"] != "CHECKPOINTED"
            )
            or (checked["lane_index"], checked["descendant_index"]) != key
            or checked["new_pid"] != worker.new_pid
            or checked["new_proc_start_ticks"] != worker.new_proc_start_ticks
            or not json_type_equal(
                checked["new_root_identity"], worker.new_root_identity
            )
            or not json_type_equal(
                checked["new_root_identity"], target["new_root_identity"]
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "quiescence/start/target binding mismatch"
            )
        try:
            alive = (
                base._proc_start_ticks(worker.new_pid)
                == worker.new_proc_start_ticks
            )
        except Exception:
            alive = False
        if alive:
            raise AdaptiveSwitchEvidenceV3Error(
                "quiescent worker remains alive"
            )
        root = Path(worker.new_root_identity["path"])
        if not json_type_equal(
            base._root_identity(root), worker.new_root_identity
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "quiescent root identity changed"
            )
        inspection = _direct_controller_inspect(self._child, root)
        generations = inspection.get("generations")
        latest = (
            generations[-1]
            if type(generations) is list and generations else {}
        )
        if (
            inspection.get("hash_verification_requested") is not True
            or inspection.get("state") != checked["state"]
            or latest.get("pid_identity_alive") is not False
            or latest.get("poison_claim") not in {None, False}
            or latest.get("active_error") not in {None, False}
            or latest.get("checkpoint_error") not in {None, False}
            or type(latest.get("generation")) is not int
            or latest["generation"] < 0
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "fresh controller quiescence inspection failed"
            )
        runtime = root / self._child.RUNTIME_ROOT
        generation = latest["generation"]
        generation_dir = (
            runtime / "generations" / f"{generation:06d}"
        )
        with self._child._fixed_environment():
            active = self._child.controller._active_commit(
                generation_dir, generation
            )
        fence = self._fences.get(key)
        if (
            active.get("pid") != worker.new_pid
            or active.get("proc_start_ticks")
                != worker.new_proc_start_ticks
            or active.get("self_sha256")
                != latest.get("active_manifest_sha256")
            or (
                fence is not None
                and active.get("self_sha256")
                    != fence.new_start_commit_sha256
            )
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "active generation misses started worker"
            )
        if checked["state"] == "CHECKPOINTED":
            if (
                latest.get("checkpointed") is not True
                or latest.get("checkpoint_hashes_valid") is not True
                or latest.get("checkpoint_manifest_sha256")
                    != checked["checkpoint_commit_sha256"]
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "fresh checkpoint inspection failed"
                )
            with self._child._fixed_environment():
                checkpoint = self._child.controller._checkpoint_commit(
                    generation_dir, generation
                )
            prefix = checkpoint.get("proof_prefix")
            if (
                checkpoint.get("kind") != "checkpoint.commit"
                or checkpoint.get("self_sha256")
                    != checked["checkpoint_commit_sha256"]
                or checkpoint.get("single_writer_stopped") is not True
                or type(prefix) is not dict
                or prefix.get("sha256") != checked["proof_sha256"]
                or prefix.get("bytes") != checked["proof_bytes"]
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "checkpoint commit misses quiescent proof"
                )
        elif latest.get("checkpointed") is not False:
            raise AdaptiveSwitchEvidenceV3Error(
                "inactive generation unexpectedly has a checkpoint"
            )
        proof = runtime / "proof.drat"
        digest, size, proof_identity = _stream_hash_size_identity(proof)
        if (
            digest != checked["proof_sha256"]
            or size != checked["proof_bytes"]
            or _writable_holders(
                proof, expected_identity=proof_identity
            ) != []
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "new proof is not quiescent"
            )
        return checked

    def note_cohort_checkpointed(
        self, *, quiescence_records: list[dict[str, Any]],
    ) -> CohortTransitionPermit:
        """Fence the stopped descendant-0 cohort before descendant-1 starts."""

        self._assert_retirement_intact()
        cohort0 = {(lane, 0) for lane in range(LANE_COUNT)}
        if (
            self._committed or self._rolled_back
            or self._cohort_transition_nonce is not None
            or self._cohort_locks
            or type(quiescence_records) is not list
            or len(quiescence_records) != LANE_COUNT
            or set(self._started_workers) != cohort0
            or set(self._fences) != cohort0
            or len(self._outer_locks) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "cohort transition preconditions failed"
            )
        records: dict[tuple[int, int], dict[str, Any]] = {}
        for value in quiescence_records:
            record = _validate_quiescence_record(value)
            key = (record["lane_index"], record["descendant_index"])
            if key in records:
                raise AdaptiveSwitchEvidenceV3Error(
                    "duplicate cohort quiescence target"
                )
            records[key] = record
        if set(records) != cohort0:
            raise AdaptiveSwitchEvidenceV3Error(
                "cohort quiescence is not exact descendant-0 coverage"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        cohort0_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS if key in cohort0
        ]
        locks = _acquire_new_root_fences(
            identities,
            controller_root_identities=cohort0_identities,
            already_held=self._outer_locks,
        )
        try:
            for key in TARGET_KEYS:
                if key in cohort0:
                    self._verify_quiescent_worker(
                        key, records[key],
                        require_checkpointed=True,
                    )
                    _publish(
                        self._root / QUIESCENCE_DIRECTORY
                        / (
                            f"lane-{key[0]}-"
                            f"descendant-{key[1]}.json"
                        ),
                        records[key],
                    )
            self._old_post_retirement_fence()
        except BaseException:
            _close_locks(locks)
            raise
        self._cohort_locks = locks
        self._cohort0_quiescence = records
        permit = CohortTransitionPermit(
            self, [records[key]["record_sha256"] for key in TARGET_KEYS
                   if key in cohort0],
        )
        self._cohort_transition_nonce = permit._token
        return permit

    def post_start_fence(
        self, *, permit: Any, started_worker: StartedWorker,
        new_session_sha256: str, new_start_commit_sha256: str,
    ) -> PostStartFence:
        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        if (
            type(permit) is not base.LaunchPermit
            or type(started_worker) is not StartedWorker
            or started_worker._lease is not self
            or started_worker._lease_nonce != self._nonce
            or started_worker.permit_binding_sha256
                != permit.permit_binding_sha256
            or self._started_workers.get(key) is not started_worker
            or key in self._fences
            or started_worker._fenced or permit._used
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "started worker is stale/foreign"
            )
        if (
            base._proc_start_ticks(started_worker.new_pid)
            != started_worker.new_proc_start_ticks
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "new worker died before post fence"
            )
        session = base._require_sha256(
            new_session_sha256, label="new session"
        )
        start = base._require_sha256(
            new_start_commit_sha256, label="new start commit"
        )
        self._old_post_retirement_fence()
        fence = PostStartFence(
            self, permit, started_worker=started_worker,
            new_session_sha256=session,
            new_start_commit_sha256=start,
        )
        permit._used = True
        started_worker._fenced = True
        self._fences[key] = fence
        return fence

    def commit_handoff(
        self, *, fences: list[Any], batch_commit_path: Path,
    ) -> dict[str, Any]:
        self._assert_retirement_intact()
        cohort0 = {(lane, 0) for lane in range(LANE_COUNT)}
        cohort1 = {(lane, 1) for lane in range(LANE_COUNT)}
        if (
            self._candidate_only or self._committed or self._rolled_back
            or type(fences) is not list or len(fences) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or set(self._started_workers) != set(TARGET_KEYS)
            or set(self._fences) != set(TARGET_KEYS)
            or set(self._cohort0_quiescence) != cohort0
            or self._cohort_transition_nonce is None
            or len(self._outer_locks) != TARGET_COUNT
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "eight-target commit preconditions failed"
            )
        by_key: dict[tuple[int, int], PostStartFence] = {}
        for fence in fences:
            key = (
                getattr(fence, "lane_index", None),
                getattr(fence, "descendant_index", None),
            )
            if (
                type(fence) is not PostStartFence
                or fence._lease is not self
                or fence._lease_nonce != self._nonce
                or self._fences.get(key) is not fence
                or key in by_key
            ):
                raise AdaptiveSwitchEvidenceV3Error("fence set invalid")
            by_key[key] = fence
        if set(by_key) != set(TARGET_KEYS):
            raise AdaptiveSwitchEvidenceV3Error(
                "fences do not cover eight targets"
            )
        roots = [by_key[key].new_root_identity["path"] for key in TARGET_KEYS]
        pids = [by_key[key].new_pid for key in TARGET_KEYS]
        if (
            len(set(roots)) != TARGET_COUNT
            or len(set(pids)) != TARGET_COUNT
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "new roots/PIDs duplicate"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        extra_controller_locks = _acquire_new_root_fences(
            identities,
            already_held=[*self._outer_locks, *self._cohort_locks],
        )
        self._cohort_locks.extend(extra_controller_locks)
        for key in TARGET_KEYS:
            fence = by_key[key]
            root = Path(fence.new_root_identity["path"])
            if not json_type_equal(
                base._root_identity(root), fence.new_root_identity
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "new root changed before commit"
                )
            if key in cohort0:
                self._verify_quiescent_worker(
                    key, self._cohort0_quiescence[key],
                    require_checkpointed=True,
                )
            else:
                if (
                    base._proc_start_ticks(fence.new_pid)
                    != fence.new_proc_start_ticks
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "running cohort worker died before commit"
                    )
                inspection = _direct_controller_inspect(
                    self._child, root
                )
                generations = inspection.get("generations")
                latest = (
                    generations[-1]
                    if type(generations) is list and generations else {}
                )
                if (
                    inspection.get("hash_verification_requested") is not True
                    or inspection.get("state") != "RUNNING"
                    or latest.get("pid_identity_alive") is not True
                    or latest.get("checkpointed") is not False
                    or latest.get("poison_claim") not in {None, False}
                    or latest.get("active_error") not in {None, False}
                    or latest.get("checkpoint_error") not in {None, False}
                    or type(latest.get("generation")) is not int
                    or latest["generation"] < 0
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "running cohort controller inspection failed"
                    )
                generation = latest["generation"]
                with self._child._fixed_environment():
                    active = self._child.controller._active_commit(
                        root / self._child.RUNTIME_ROOT
                        / "generations" / f"{generation:06d}",
                        generation,
                    )
                if (
                    active.get("pid") != fence.new_pid
                    or active.get("proc_start_ticks")
                        != fence.new_proc_start_ticks
                    or active.get("self_sha256")
                        != latest.get("active_manifest_sha256")
                    or active.get("self_sha256")
                        != fence.new_start_commit_sha256
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "running cohort misses exact start manifest"
                    )
        self._old_post_retirement_fence()
        target = Path(batch_commit_path)
        if target != self._root / HANDOFF_COMMIT:
            raise AdaptiveSwitchEvidenceV3Error(
                "wrong batch commit path"
            )
        bindings: list[dict[str, Any]] = []
        for key in TARGET_KEYS:
            fence = by_key[key]
            quiescence = self._cohort0_quiescence.get(key)
            bindings.append({
                **fence.audit_binding(),
                "fence_sha256": fence.fence_sha256,
                "cohort_index": key[1],
                "handoff_state": (
                    "CHECKPOINTED" if key in cohort0 else "RUNNING"
                ),
                "cohort_quiescence_sha256": (
                    quiescence["record_sha256"]
                    if quiescence is not None else None
                ),
            })
        record = seal({
            "schema_version": SCHEMA_VERSION, "kind": HANDOFF_KIND,
            "gate": GATE, "test_only": True,
            "production_eligible": False,
            "authenticated": False, "launch_authorized": False,
            "scientific_claim": False,
            "historical_atomic_handoff_observed": True,
            "batch_root": str(self._root),
            "batch_root_identity": base._root_identity(self._root),
            "batch_manifest_sha256":
                self._record["batch_manifest_sha256"],
            "switch_evidence_sha256": self._record["record_sha256"],
            "switch_observation_policy":
                dict(self._record["observation_policy"]),
            "prepared_retirement_sha256":
                self._prepared["record_sha256"],
            "retired_locks": list(self._retired_records),
            "root_bindings": bindings,
            "fence_sha256s": [
                item["fence_sha256"] for item in bindings
            ],
            "cohort_policy": {
                "target_keys": [
                    [lane, descendant]
                    for lane, descendant in TARGET_KEYS
                ],
                "target_count": TARGET_COUNT,
                "cohort_count": DESCENDANT_COUNT,
                "cohort_size": LANE_COUNT,
                "max_live_workers": MAX_LIVE_WORKERS,
                "checkpointed_at_commit": LANE_COUNT,
                "running_at_commit": LANE_COUNT,
            },
            "source_binding": self._v3_sources,
            "root_link_policy": {
                "relative_path": "state/15-batch-handoff.json",
                "publish": "o-excl-canonical-json-fsync-v1",
                "repair_only_from_externally_pinned_batch_commit": True,
            },
            "claim_scope": {
                "old_transport_durably_retired_before_first_new_start":
                    True,
                "eight_new_processes_observed_started": True,
                "four_new_processes_checkpointed_at_commit": True,
                "four_new_processes_observed_alive_at_commit": True,
                "max_live_workers": MAX_LIVE_WORKERS,
                "serialized_record_can_authorize_launch": False,
                "serialized_record_can_authenticate_unsat": False,
            },
        })
        _verify_committed_journals(self._root, record)
        _publish(target, record)
        self._committed = True
        return json.loads(canonical_bytes(record))

    def rollback_after_new_quiescent(
        self, *, quiescence_records: list[dict[str, Any]],
        not_started_target_keys: list[tuple[int, int]],
    ) -> dict[str, Any]:
        """Retire all prepared new entrypoints, then restore the old batch."""

        self._assert_retirement_intact()
        if (
            self._committed or self._rolled_back
            or len(self._outer_locks) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or type(quiescence_records) is not list
            or type(not_started_target_keys) is not list
            or any(
                type(item) is not tuple or len(item) != 2
                or type(item[0]) is not int or type(item[1]) is not int
                or item not in TARGET_KEYS
                for item in not_started_target_keys
            )
            or len(not_started_target_keys)
                != len(set(not_started_target_keys))
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "rollback partition malformed"
            )
        records: dict[tuple[int, int], dict[str, Any]] = {}
        for value in quiescence_records:
            record = _validate_quiescence_record(value)
            key = (record["lane_index"], record["descendant_index"])
            if key in records:
                raise AdaptiveSwitchEvidenceV3Error(
                    "duplicate quiescence target"
                )
            records[key] = record
        started = set(self._started_workers)
        not_started = set(not_started_target_keys)
        if (
            set(records) != started
            or not_started != set(TARGET_KEYS) - started
            or set(records) & not_started
            or set(records) | not_started != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "rollback is not an exact target partition"
            )
        for key in TARGET_KEYS:
            if key not in not_started:
                continue
            root = Path(
                self._target_records[key]["new_root_identity"]["path"]
            )
            runtime = root / "runtime/dmtcp"
            if runtime.exists() or runtime.is_symlink():
                raise AdaptiveSwitchEvidenceV3Error(
                    "not-started target has a controller runtime"
                )
        root_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        controller_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS if key in started
        ]
        additional = _acquire_new_root_fences(
            root_identities,
            controller_root_identities=controller_identities,
            already_held=[*self._outer_locks, *self._cohort_locks],
        )
        self._cohort_locks.extend(additional)
        for key in TARGET_KEYS:
            if key in started:
                self._verify_quiescent_worker(key, records[key])
        all_new_locks = sorted(
            [*self._outer_locks, *self._cohort_locks],
            key=lambda item: str(item.current_path),
        )
        if len(all_new_locks) != TARGET_COUNT + len(started):
            raise AdaptiveSwitchEvidenceV3Error(
                "new rollback lock coverage is not exact"
            )
        new_retired: list[tuple[Any, dict[str, Any]]] = []
        try:
            suffix = self._record["record_sha256"][:16] + "-precommit"
            for sequence, held in enumerate(all_new_locks):
                target = held.original_path.with_name(
                    held.original_path.name
                    + f".rolled-back-v3-{suffix}"
                )
                retirement = _retire_lock_v3(held, target)
                new_retired.append((
                    held, {"sequence": sequence, **retirement}
                ))
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "partial prepared-new retirement could not be restored"
                ) from failures[0]
            raise
        ordered = [
            *self._locks[5:], *self._locks[1:5], self._locks[0]
        ]
        pairs = list(zip(
            ordered, self._retired_records, strict=True
        ))
        restored_pairs: list[tuple[Any, dict[str, Any]]] = []
        try:
            restored: list[str] = []
            for held, retirement in reversed(pairs):
                _restore_lock_v3(held, retirement)
                restored_pairs.append((held, retirement))
                restored.append(held.role)
            snapshot = base._snapshot_locked(
                self._root, self._coordinator, self._child
            )
            replay = base._build_record(
                self._root, snapshot, self._discovery, self._overlay,
                self._legacy_executed, self._overlay_record,
                self._overlay_executed,
                timeout_seconds=self._timeout,
                elapsed_seconds_by_lane=self._elapsed,
            )
            if not json_type_equal(replay, self._record):
                raise AdaptiveSwitchEvidenceV3Error(
                    "old checkpoint failed rollback replay"
                )
            rollback = seal({
                "schema_version": SCHEMA_VERSION,
                "kind": ROLLBACK_KIND, "gate": GATE,
                "test_only": True, "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False,
                "batch_root": str(self._root),
                "batch_manifest_sha256":
                    self._record["batch_manifest_sha256"],
                "switch_evidence_sha256":
                    self._record["record_sha256"],
                "prepared_retirement_sha256":
                    self._prepared["record_sha256"],
                "quiescence_record_sha256s": [
                    records[key]["record_sha256"]
                    for key in TARGET_KEYS if key in records
                ],
                "not_started_target_keys": [
                    [lane, descendant]
                    for lane, descendant in TARGET_KEYS
                    if (lane, descendant) in not_started
                ],
                "retired_new_locks": [
                    item for _, item in new_retired
                ],
                "restored_roles": restored,
                "old_checkpoint_replayed": True,
                "new_workers_quiescent": True,
                "claim_scope": {
                    "all_prepared_outer_entrypoints_retired": True,
                    "all_started_controller_entrypoints_retired": True,
                    "new_locks_held_until_old_replay_and_publish": True,
                    "serialized_record_can_authorize_launch": False,
                },
                "source_binding": self._v3_sources,
            })
            _publish(self._root / ROLLBACK_COMMIT, rollback)
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(restored_pairs):
                try:
                    _retire_lock_v3(
                        held, Path(retirement["retired_path"])
                    )
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "rollback failed and old entrypoint compensation failed"
                ) from failures[0]
            raise
        self._rolled_back = True
        self._outer_locks = []
        self._cohort_locks = []
        _close_locks(all_new_locks)
        return json.loads(canonical_bytes(rollback))

    def _close(self) -> None:
        if not self._active:
            return
        _close_locks(self._cohort_locks)
        _close_locks(self._outer_locks)
        self._cohort_locks = []
        self._outer_locks = []
        super()._close()


def _enter(
    batch_root: Path, *, expected_batch_manifest_sha256: str | None,
    expected_switch_evidence_sha256: str | None,
    expected_hard_evidence_sha256s: list[str] | None,
    timeout_seconds: float, elapsed_seconds_by_lane: list[float],
    strict_base: bool, candidate_only: bool,
) -> AtomicSwitchLease:
    if type(strict_base) is not bool or strict_base is not True:
        raise AdaptiveSwitchEvidenceV3Error("only strict real replay is allowed")
    root = Path(batch_root)
    locks, discovery = base._acquire_all_locks(root)
    try:
        discovery = base._discover_sources(
            root, expected_batch_manifest_sha256=expected_batch_manifest_sha256
        )
        coordinator, child, legacy_executed = _load_legacy_exact(discovery)
        overlay, overlay_record, overlay_executed = _load_overlay_exact()
        snapshot = base._snapshot_locked(root, coordinator, child)
        record = base._build_record(
            root, snapshot, discovery, overlay, legacy_executed,
            overlay_record, overlay_executed,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        )
        validate_switch_record_structure(record)
        if not candidate_only:
            switch_pin = base._require_sha256(
                expected_switch_evidence_sha256, label="switch evidence pin"
            )
            batch_pin = base._require_sha256(
                expected_batch_manifest_sha256, label="batch manifest pin"
            )
            if (
                record["record_sha256"] != switch_pin
                or record["batch_manifest_sha256"] != batch_pin
            ):
                raise AdaptiveSwitchEvidenceV3Error("fresh replay misses external pins")
            if (
                type(expected_hard_evidence_sha256s) is not list
                or len(expected_hard_evidence_sha256s) != LANE_COUNT
                or [item["hard_evidence_sha256"] for item in record["lanes"]]
                != [
                    base._require_sha256(item, label="hard evidence pin")
                    for item in expected_hard_evidence_sha256s
                ]
            ):
                raise AdaptiveSwitchEvidenceV3Error("hard evidence pins mismatch")
        lease = AtomicSwitchLease(
            root, locks, discovery, coordinator, child, overlay,
            legacy_executed, overlay_record, overlay_executed, snapshot, record,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
            candidate_only=candidate_only, v3_sources=_v3_source_binding(),
        )
        if not candidate_only:
            lease.prepare_retirement()
        return lease
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
    lease = _enter(
        batch_root,
        expected_batch_manifest_sha256=expected_batch_manifest_sha256,
        expected_switch_evidence_sha256=expected_switch_evidence_sha256,
        expected_hard_evidence_sha256s=expected_hard_evidence_sha256s,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        strict_base=strict_base, candidate_only=False,
    )
    normal_exit = False
    try:
        yield lease
        normal_exit = True
        if not lease._committed and not lease._rolled_back:
            raise AdaptiveSwitchEvidenceV3Error(
                "lease exited without commit or explicit quiescent rollback"
            )
    finally:
        # Retired names, not process-lifetime flocks, are the crash fence.  It
        # is safe to close fds on an uncommitted exceptional exit: old entry
        # points remain absent until explicit audited rollback.
        lease._close()
        del normal_exit


def build_switch_evidence_record(
    batch_root: Path, *, timeout_seconds: float,
    elapsed_seconds_by_lane: list[float], strict_base: bool = True,
) -> dict[str, Any]:
    lease = _enter(
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


def _validate_committed(record: Mapping[str, Any]) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "test_only",
        "production_eligible", "authenticated", "launch_authorized",
        "scientific_claim", "historical_atomic_handoff_observed",
        "batch_root", "batch_root_identity", "batch_manifest_sha256",
        "switch_evidence_sha256", "switch_observation_policy",
        "prepared_retirement_sha256", "retired_locks",
        "root_bindings", "fence_sha256s", "cohort_policy",
        "source_binding", "root_link_policy", "claim_scope",
        "record_sha256",
    }
    if (
        type(record) is not dict or set(record) != fields
        or not selfhash_valid(record)
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff schema/self-hash mismatch"
        )
    if (
        type(record.get("schema_version")) is not int
        or record.get("schema_version") != SCHEMA_VERSION
        or record.get("kind") != HANDOFF_KIND
        or record.get("gate") != GATE
        or record.get("test_only") is not True
        or record.get("production_eligible") is not False
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or record.get("scientific_claim") is not False
        or record.get("historical_atomic_handoff_observed") is not True
        or type(record.get("batch_root")) is not str
        or any(
            not base._is_sha256(record.get(field))
            for field in (
                "batch_manifest_sha256", "switch_evidence_sha256",
                "prepared_retirement_sha256", "record_sha256",
            )
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff authority/hash mismatch"
        )
    policy = record.get("switch_observation_policy")
    try:
        rebuilt_policy = base._observation_policy(
            policy["timeout_seconds"],
            policy["elapsed_seconds_by_lane"],
        )
    except Exception as exc:
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff observation policy malformed"
        ) from exc
    if not json_type_equal(policy, rebuilt_policy):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff observation policy mismatch"
        )
    expected_cohort_policy = {
        "target_keys": [
            [lane, descendant] for lane, descendant in TARGET_KEYS
        ],
        "target_count": TARGET_COUNT,
        "cohort_count": DESCENDANT_COUNT,
        "cohort_size": LANE_COUNT,
        "max_live_workers": MAX_LIVE_WORKERS,
        "checkpointed_at_commit": LANE_COUNT,
        "running_at_commit": LANE_COUNT,
    }
    if not json_type_equal(
        record.get("cohort_policy"), expected_cohort_policy
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff cohort policy mismatch"
        )
    bindings = record.get("root_bindings")
    fences = record.get("fence_sha256s")
    retired = record.get("retired_locks")
    if (
        type(bindings) is not list or len(bindings) != TARGET_COUNT
        or type(fences) is not list or len(fences) != TARGET_COUNT
        or type(retired) is not list or len(retired) != 9
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff cardinality mismatch"
        )
    binding_fields = {
        "lane_index", "global_leaf_index", "descendant_index",
        "descendant_sha256", "new_root_identity",
        "new_session_sha256", "new_start_commit_sha256",
        "new_pid", "new_proc_start_ticks", "permit_binding_sha256",
        "prepared_target_sha256", "started_worker_journal_sha256",
        "fence_sha256", "cohort_index", "handoff_state",
        "cohort_quiescence_sha256",
    }
    roots: set[str] = set()
    pids: set[int] = set()
    for position, (key, item) in enumerate(
        zip(TARGET_KEYS, bindings, strict=True)
    ):
        unsigned = dict(item) if type(item) is dict else {}
        fence = unsigned.pop("fence_sha256", None)
        cohort_index = unsigned.pop("cohort_index", None)
        state = unsigned.pop("handoff_state", None)
        quiescence = unsigned.pop(
            "cohort_quiescence_sha256", None
        )
        expected_state = (
            "CHECKPOINTED" if key[1] == 0 else "RUNNING"
        )
        if (
            type(item) is not dict or set(item) != binding_fields
            or (item.get("lane_index"),
                item.get("descendant_index")) != key
            or cohort_index != key[1] or state != expected_state
            or (
                key[1] == 0 and not base._is_sha256(quiescence)
            )
            or (key[1] == 1 and quiescence is not None)
            or canonical_sha256(unsigned) != fence
            or fences[position] != fence
            or any(
                not base._is_sha256(item.get(field))
                for field in (
                    "descendant_sha256", "new_session_sha256",
                    "new_start_commit_sha256",
                    "permit_binding_sha256",
                    "prepared_target_sha256",
                    "started_worker_journal_sha256", "fence_sha256",
                )
            )
            or type(item.get("global_leaf_index")) is not int
            or type(item.get("new_pid")) is not int
            or type(item.get("new_proc_start_ticks")) is not int
            or item["new_pid"] <= 0
            or item["new_proc_start_ticks"] <= 0
            or type(item.get("new_root_identity")) is not dict
            or type(item["new_root_identity"].get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "fence/cohort binding mismatch"
            )
        roots.add(item["new_root_identity"]["path"])
        pids.add(item["new_pid"])
    if len(roots) != TARGET_COUNT or len(pids) != TARGET_COUNT:
        raise AdaptiveSwitchEvidenceV3Error(
            "handoff roots/PIDs duplicate"
        )
    return dict(record)


def verify_committed_handoff(
    batch_commit_path: Path, *, expected_batch_commit_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str,
) -> dict[str, Any]:
    commit_pin = base._require_sha256(
        expected_batch_commit_sha256, label="batch handoff pin"
    )
    switch_pin = base._require_sha256(
        expected_switch_evidence_sha256, label="switch evidence pin"
    )
    batch_pin = base._require_sha256(
        expected_batch_manifest_sha256, label="batch manifest pin"
    )
    path = Path(batch_commit_path)
    record = _validate_committed(base._read_json(path))
    root = Path(record["batch_root"])
    rollback_path = root / ROLLBACK_COMMIT
    if rollback_path.exists() or rollback_path.is_symlink():
        raise AdaptiveSwitchEvidenceV3Error(
            "committed handoff was rolled back"
        )
    if (
        path != root / HANDOFF_COMMIT or record["record_sha256"] != commit_pin
        or record["switch_evidence_sha256"] != switch_pin
        or record["batch_manifest_sha256"] != batch_pin
        or not json_type_equal(record["batch_root_identity"], base._root_identity(root))
    ):
        raise AdaptiveSwitchEvidenceV3Error("handoff path/pin mismatch")
    prepared = base._read_json(root / PREPARED_COMMIT)
    if (
        not selfhash_valid(prepared)
        or prepared.get("kind") != PREPARED_KIND
        or prepared.get("record_sha256")
            != record["prepared_retirement_sha256"]
        or prepared.get("switch_evidence_sha256") != switch_pin
        or prepared.get("batch_manifest_sha256") != batch_pin
        or not json_type_equal(
            prepared.get("retired_locks"),
            record["retired_locks"],
        )
        or not json_type_equal(
            record.get("source_binding"), _v3_source_binding()
        )
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "prepared retirement/source binding mismatch"
        )
    journal_bindings = _verify_committed_journals(root, record)
    verified: list[dict[str, Any]] = []
    for item in record["retired_locks"]:
        original = Path(item["original_path"])
        retired = Path(item["retired_path"])
        if original.exists() or original.is_symlink():
            raise AdaptiveSwitchEvidenceV3Error("old runner entry point was restored")
        observed = retired.lstat()
        if (
            stat.S_ISLNK(observed.st_mode) or not stat.S_ISREG(observed.st_mode)
            or not json_type_equal(base._stat_identity(observed), item["identity"])
        ):
            raise AdaptiveSwitchEvidenceV3Error("retired lock identity mismatch")
        verified.append(dict(item))
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": HANDOFF_VERIFY_KIND,
        "valid": True, "authenticated": False, "launch_authorized": False,
        "production_eligible": False, "scientific_claim": False,
        "historical_handoff_only": True,
        "batch_commit_sha256": record["record_sha256"],
        "switch_evidence_sha256": record["switch_evidence_sha256"],
        "batch_manifest_sha256": record["batch_manifest_sha256"],
        "prepared_retirement_sha256": record["prepared_retirement_sha256"],
        "old_runner_entrypoints_absent": True,
        "retired_locks": verified,
        "root_bindings": list(record["root_bindings"]),
        "fence_sha256s": list(record["fence_sha256s"]),
        "cohort_policy": dict(record["cohort_policy"]),
        "journal_bindings": journal_bindings,
        "root_link_policy": dict(record["root_link_policy"]),
    })


def rollback_committed_handoff(
    batch_commit_path: Path, *, expected_batch_commit_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str,
    expected_switch_record: Mapping[str, Any],
    quiescence_records: list[dict[str, Any]],
) -> dict[str, Any]:
    """Retire eight new roots/16 entrypoints and restore the exact old batch."""

    commit_pin = base._require_sha256(
        expected_batch_commit_sha256, label="batch handoff pin"
    )
    switch_pin = base._require_sha256(
        expected_switch_evidence_sha256, label="switch evidence pin"
    )
    batch_pin = base._require_sha256(
        expected_batch_manifest_sha256, label="batch manifest pin"
    )
    if (
        type(expected_switch_record) is not dict
        or not selfhash_valid(expected_switch_record)
        or expected_switch_record.get("record_sha256") != switch_pin
        or expected_switch_record.get("batch_manifest_sha256")
            != batch_pin
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "committed rollback switch record misses external pins"
        )
    validate_switch_record_structure(expected_switch_record)
    verify_committed_handoff(
        batch_commit_path,
        expected_batch_commit_sha256=commit_pin,
        expected_switch_evidence_sha256=switch_pin,
        expected_batch_manifest_sha256=batch_pin,
    )
    if (
        type(quiescence_records) is not list
        or len(quiescence_records) != TARGET_COUNT
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "committed rollback quiescence cardinality malformed"
        )
    by_key: dict[tuple[int, int], dict[str, Any]] = {}
    for value in quiescence_records:
        item = _validate_quiescence_record(value)
        key = (item["lane_index"], item["descendant_index"])
        if key in by_key:
            raise AdaptiveSwitchEvidenceV3Error(
                "duplicate committed rollback target"
            )
        by_key[key] = item
    if set(by_key) != set(TARGET_KEYS):
        raise AdaptiveSwitchEvidenceV3Error(
            "committed rollback must cover eight targets"
        )
    path = Path(batch_commit_path)
    commit = _validate_committed(base._read_json(path))
    root = Path(commit["batch_root"])
    if (
        path != root / HANDOFF_COMMIT
        or commit["record_sha256"] != commit_pin
        or commit["switch_evidence_sha256"] != switch_pin
        or commit["batch_manifest_sha256"] != batch_pin
    ):
        raise AdaptiveSwitchEvidenceV3Error(
            "committed rollback pin/path mismatch"
        )
    bindings = {
        (item["lane_index"], item["descendant_index"]): item
        for item in commit["root_bindings"]
    }
    if set(bindings) != set(TARGET_KEYS):
        raise AdaptiveSwitchEvidenceV3Error(
            "committed root bindings are not exact"
        )
    root_identities = [
        bindings[key]["new_root_identity"] for key in TARGET_KEYS
    ]
    for key in TARGET_KEYS:
        item = by_key[key]
        if not json_type_equal(
            item["new_root_identity"],
            bindings[key]["new_root_identity"],
        ):
            raise AdaptiveSwitchEvidenceV3Error(
                "committed quiescence misses target root"
            )
    discovery = base._discover_sources(
        root, expected_batch_manifest_sha256=batch_pin
    )
    _, child, _ = _load_legacy_exact(discovery)
    new_locks = _acquire_new_root_fences(root_identities)
    new_retired: list[tuple[Any, dict[str, Any]]] = []
    old_locks: list[Any] = []
    old_restored: list[tuple[Any, dict[str, Any]]] = []
    try:
        rollback_path = root / ROLLBACK_COMMIT
        if rollback_path.exists() or rollback_path.is_symlink():
            raise AdaptiveSwitchEvidenceV3Error(
                "committed handoff already rolled back"
            )
        fresh_commit = _validate_committed(base._read_json(path))
        if not json_type_equal(fresh_commit, commit):
            raise AdaptiveSwitchEvidenceV3Error(
                "handoff commit changed under rollback locks"
            )
        _verify_committed_journals(root, fresh_commit)
        for key in TARGET_KEYS:
            item = by_key[key]
            binding = bindings[key]
            identity = binding["new_root_identity"]
            target_root = Path(identity["path"])
            if not json_type_equal(
                base._root_identity(target_root), identity
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "new root changed before rollback"
                )
            try:
                alive = (
                    base._proc_start_ticks(item["new_pid"])
                    == item["new_proc_start_ticks"]
                )
            except Exception:
                alive = False
            if alive:
                raise AdaptiveSwitchEvidenceV3Error(
                    "new worker remains alive"
                )
            inspection = _direct_controller_inspect(child, target_root)
            generations = inspection.get("generations")
            latest = (
                generations[-1]
                if type(generations) is list and generations else {}
            )
            if (
                inspection.get("hash_verification_requested") is not True
                or inspection.get("state") != item["state"]
                or latest.get("pid_identity_alive") is not False
                or latest.get("poison_claim") not in {None, False}
                or latest.get("active_error") not in {None, False}
                or latest.get("checkpoint_error") not in {None, False}
                or type(latest.get("generation")) is not int
                or latest["generation"] < 0
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "committed rollback controller is not quiescent"
                )
            generation = latest["generation"]
            generation_dir = (
                target_root / child.RUNTIME_ROOT
                / "generations" / f"{generation:06d}"
            )
            with child._fixed_environment():
                active = child.controller._active_commit(
                    generation_dir, generation
                )
            if (
                active.get("pid") != item["new_pid"]
                or active.get("proc_start_ticks")
                    != item["new_proc_start_ticks"]
                or active.get("self_sha256")
                    != latest.get("active_manifest_sha256")
                or (
                    item["new_pid"] == binding["new_pid"]
                    and item["new_proc_start_ticks"]
                        == binding["new_proc_start_ticks"]
                    and active.get("self_sha256")
                        != binding["new_start_commit_sha256"]
                )
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "committed rollback active generation mismatch"
                )
            if item["state"] == "CHECKPOINTED":
                if (
                    latest.get("checkpointed") is not True
                    or latest.get("checkpoint_hashes_valid") is not True
                    or latest.get("checkpoint_manifest_sha256")
                        != item["checkpoint_commit_sha256"]
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "committed rollback checkpoint mismatch"
                    )
                with child._fixed_environment():
                    checkpoint = child.controller._checkpoint_commit(
                        generation_dir, generation
                    )
                prefix = checkpoint.get("proof_prefix")
                if (
                    checkpoint.get("self_sha256")
                        != item["checkpoint_commit_sha256"]
                    or checkpoint.get("single_writer_stopped") is not True
                    or type(prefix) is not dict
                    or prefix.get("sha256") != item["proof_sha256"]
                    or prefix.get("bytes") != item["proof_bytes"]
                ):
                    raise AdaptiveSwitchEvidenceV3Error(
                        "committed checkpoint proof mismatch"
                    )
            elif latest.get("checkpointed") is not False:
                raise AdaptiveSwitchEvidenceV3Error(
                    "inactive rollback target has a checkpoint"
                )
            proof = (
                target_root / child.RUNTIME_ROOT / "proof.drat"
            )
            digest, size, proof_identity = _stream_hash_size_identity(
                proof
            )
            if (
                digest != item["proof_sha256"]
                or size != item["proof_bytes"]
                or _writable_holders(
                    proof, expected_identity=proof_identity
                ) != []
            ):
                raise AdaptiveSwitchEvidenceV3Error(
                    "new proof changed or has a writer"
                )
        suffix = commit_pin[:16]
        try:
            for sequence, held in enumerate(new_locks):
                retired_path = held.original_path.with_name(
                    held.original_path.name
                    + f".rolled-back-v3-{suffix}"
                )
                retirement = _retire_lock_v3(held, retired_path)
                new_retired.append((
                    held, {"sequence": sequence, **retirement}
                ))
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "partial new retirement could not be compensated"
                ) from failures[0]
            raise
        try:
            old_locks, old_by_role = _acquire_retired_old_locks(
                commit["retired_locks"]
            )
        except BaseException:
            failures = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "old lock acquisition failed and new restore failed"
                ) from failures[0]
            raise
        try:
            roles = [
                "batch", *(
                    f"lane-{index}" for index in range(LANE_COUNT)
                ), *(
                    f"controller-{index}"
                    for index in range(LANE_COUNT)
                ),
            ]
            held_by_role = {
                held.role.removeprefix("old-retired:"): held
                for held in old_locks
            }
            restored_old: list[dict[str, Any]] = []
            for role in reversed(roles):
                held = held_by_role[role]
                retirement = old_by_role[role]
                restored_old.append(
                    _restore_external_old_lock(held, retirement)
                )
                old_restored.append((held, retirement))
            replay = _fresh_restored_old_checkpoint(
                root,
                expected_batch_manifest_sha256=batch_pin,
                expected_switch_evidence_sha256=switch_pin,
                expected_switch_record=expected_switch_record,
                switch_observation_policy=
                    commit["switch_observation_policy"],
            )
            rollback = seal({
                "schema_version": SCHEMA_VERSION,
                "kind": ROLLBACK_KIND, "gate": GATE,
                "test_only": True, "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False,
                "batch_root": str(root),
                "batch_root_identity": base._root_identity(root),
                "committed_handoff_sha256": commit_pin,
                "switch_evidence_sha256": switch_pin,
                "batch_manifest_sha256": batch_pin,
                "prepared_retirement_sha256":
                    commit["prepared_retirement_sha256"],
                "quiescence_record_sha256s": [
                    by_key[key]["record_sha256"]
                    for key in TARGET_KEYS
                ],
                "retired_new_locks": [
                    item for _, item in new_retired
                ],
                "restored_old_locks": restored_old,
                "old_checkpoint_replay": replay,
                "old_checkpoint_replayed": True,
                "exact_switch_record_equal": True,
                "new_workers_quiescent": True,
                "claim_scope": {
                    "sixteen_new_entrypoints_retired_before_old_restore":
                        True,
                    "eight_new_roots_locked_during_transition": True,
                    "serialized_record_can_authorize_launch": False,
                    "serialized_record_can_authenticate_unsat": False,
                },
                "source_binding": _v3_source_binding(),
            })
            _publish(rollback_path, rollback)
        except BaseException:
            compensation_failures: list[BaseException] = []
            for held, retirement in reversed(old_restored):
                try:
                    _reretire_external_old_lock(held, retirement)
                except BaseException as exc:
                    compensation_failures.append(exc)
            if compensation_failures:
                raise AdaptiveSwitchEvidenceV3Error(
                    "committed rollback failed and old re-retirement failed"
                ) from compensation_failures[0]
            raise
        return json.loads(canonical_bytes(rollback))
    finally:
        _close_locks(old_locks)
        _close_locks(new_locks)


LaunchPermit = base.LaunchPermit

__all__ = [
    "AdaptiveSwitchEvidenceV3Error", "AtomicSwitchLease", "LaunchPermit",
    "StartedWorker", "PostStartFence", "CohortTransitionPermit",
    "HANDOFF_COMMIT", "PREPARED_COMMIT", "ROLLBACK_COMMIT",
    "TARGET_KEYS", "TARGET_COUNT", "MAX_LIVE_WORKERS",
    "QUIESCENCE_KIND", "acquire_atomic_switch_lease",
    "build_switch_evidence_record", "validate_switch_record_structure",
    "verify_committed_handoff", "rollback_committed_handoff",
    "canonical_bytes", "canonical_sha256",
    "seal", "selfhash_valid", "json_type_equal",
]
