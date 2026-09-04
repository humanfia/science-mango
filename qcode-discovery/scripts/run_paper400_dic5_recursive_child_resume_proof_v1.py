#!/usr/bin/env python3
"""Proof-producing DMTCP runner for one audited recursive Paper400 child.

This runner intentionally does not reinterpret or modify a legacy Paper400
root.  A sidecar first freezes a parent CNF, an authenticated binary split
manifest, and a hardness-only timeout audit.  ``prepare`` then creates a new
mode-0700 child root containing exact local copies of that material.  The
child is started through the frozen single-process DMTCP controller on one
explicit CPU.  A checkpoint is transport only: an UNSAT certificate is sealed
only after a stopped proof stream has passed DRAT verification, DRAT-to-LRAT
conversion, LRAT verification, and fresh replays of both proof formats.

The resulting certificate binds the exact recursive frontier leaf record, so
``paper400_dic5_recursive_split_v1`` can aggregate it only with every sibling.
No command here deletes a parent root or resumes a legacy parent process.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import importlib.util
import json
import os
import resource
import stat
import sys
import time
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive


CONTROLLER_RELATIVE = Path("scripts/run_cadical_dmtcp_resume_v1.py")
PROOF_HELPER_RELATIVE = Path("scripts/run_paper400_dic5_cube16_standalone_proof_v1.py")
EXPECTED_CONTROLLER_SHA256 = (
    "9e57ea9b99a4b041c73a97939f997671790b77b6cb5c7b3d7fe04e1d925f47d2"
)
EXPECTED_PROOF_HELPER_SHA256 = (
    "2d1c2e0240a7eacb5e07695fc55028860ec1a23eb15681af9f1e49fbb42d2a38"
)

SOLVER = Path("/home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical")
DMTCP_PREFIX = Path("/home/jing/paper400-toolchain/dmtcp-4.2.0")
DRAT_CHECKER = Path("/home/jing/paper400-toolchain/proof-checkers/bin/drat-trim")
LRAT_CHECKER = Path("/home/jing/paper400-toolchain/proof-checkers/bin/lrat-check")
EXPECTED_SOLVER_SHA256 = (
    "6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21"
)
EXPECTED_DMTCP_LAUNCH_SHA256 = (
    "2036e98a96ca701425a4d47d86b82d0b4657cf39cbac90cd22770dc9d65480ab"
)
EXPECTED_DMTCP_COMMAND_SHA256 = (
    "aa4eebcbdaa62abde9af5e849f93423de22ce4415871c678095613598d3c4c98"
)
EXPECTED_DMTCP_RESTART_SHA256 = (
    "b1e72dd345660cdcb3688accb4888542df3c8d1ed97e08ebbbfc46e783da32ae"
)
EXPECTED_DRAT_SHA256 = (
    "8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394"
)
EXPECTED_LRAT_SHA256 = (
    "c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79"
)

SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-child-resume-proof-v1"
STATIC_KIND = "paper400-dic5-recursive-child-static-v1"
SESSION_KIND = "paper400-dic5-recursive-child-dmtcp-session-v1"
START_CLAIM_KIND = "paper400-dic5-recursive-child-start-claim-v1"
TERMINAL_CLAIM_KIND = "paper400-dic5-recursive-child-terminal-claim-v1"
CERTIFICATE_KIND = "paper400-dic5-recursive-child-unsat-v1"
VALIDATION_KIND = "paper400-dic5-recursive-child-validation-v1"
FINAL_KIND = "paper400-dic5-recursive-child-final-v1"
PARENT_AUDIT_KIND = "paper400-dic5-recursive-parent-timeout-audit-v1"

MAX_JSON_BYTES = 256 << 20
MAX_DIMACS_BYTES = 1 << 30
MAX_PROOF_BYTES = 128 << 30
MAX_CHECKPOINT_IMAGE_BYTES = 32 << 30
DEFAULT_PROOF_MAX_BYTES = 64 << 30
DEFAULT_CHECKPOINT_IMAGE_MAX_BYTES = 16 << 30
DEFAULT_CHECKPOINT_GENERATION_MAX = 64
MIN_AVAILABLE_MEMORY_BYTES = 12 << 30
MIN_AVAILABLE_DISK_HEADROOM_BYTES = 16 << 30
HASH_CHUNK_BYTES = 8 << 20

STATIC_PARENT_DIMACS = Path("static/parent.cnf")
STATIC_SPLIT_MANIFEST = Path("static/split-manifest.json")
STATIC_LEAF = Path("static/leaf.json")
STATIC_PARENT_AUDIT = Path("static/parent-audit.json")
STATIC_CHILD_DIMACS = Path("static/cube.cnf")
STATIC_COMMIT = Path("state/00-recursive-static.json")
START_CLAIM = Path("state/05-start.claim.json")
SESSION_COMMIT = Path("state/10-session.json")
TERMINAL_CLAIM = Path("state/30-terminal.claim.json")
CERTIFICATE = Path("certificate.json")
VALIDATION = Path("validation.json")
FINAL_COMMIT = Path("COMMIT.json")
ROOT_LOCK = ".recursive-child.lock"
RUNTIME_ROOT = Path("runtime/dmtcp")

PHYSICAL_RECORD_FIELDS = {
    "role", "relative_path", "file_sha256", "bytes", "mode", "device", "inode", "links",
}


class RecursiveChildRunnerError(RuntimeError):
    """A static, transport, proof, or publication invariant failed."""


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev), int(info.st_ino), int(info.st_mode), int(info.st_uid),
        int(info.st_nlink), int(info.st_size), int(info.st_mtime_ns),
        int(info.st_ctime_ns),
    )


def _stable_bytes(path: Path, *, cap: int, executable: bool | None = None) -> bytes:
    """Read an owned regular file without accepting alias/race substitutions."""

    target = Path(path)
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise RecursiveChildRunnerError(f"cannot resolve file: {target}") from exc
    if (
        resolved != target
        or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or lexical.st_nlink != 1
        or lexical.st_size > cap
        or (executable is True and not (lexical.st_mode & stat.S_IXUSR))
        or (executable is False and (lexical.st_mode & stat.S_IXUSR))
    ):
        raise RecursiveChildRunnerError(f"unsafe file binding: {target}")
    fd = os.open(target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    total = 0
    try:
        before = os.fstat(fd)
        if _identity(before) != _identity(lexical):
            raise RecursiveChildRunnerError("file changed before secure read")
        while True:
            chunk = os.read(fd, min(HASH_CHUNK_BYTES, cap + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > cap:
                raise RecursiveChildRunnerError("file exceeds configured cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if _identity(before) != _identity(after) or total != before.st_size:
        raise RecursiveChildRunnerError("file changed during secure read")
    return b"".join(chunks)


def _sha256_file(path: Path, *, cap: int, executable: bool | None = None) -> tuple[str, int]:
    payload = _stable_bytes(path, cap=cap, executable=executable)
    return hashlib.sha256(payload).hexdigest(), len(payload)


def _stable_source(path: Path, expected_sha256: str) -> bytes:
    payload = _stable_bytes(path, cap=32 << 20, executable=False)
    if hashlib.sha256(payload).hexdigest() != expected_sha256:
        raise RecursiveChildRunnerError(f"pinned source hash mismatch: {path}")
    return payload


def _load_pinned_module(name: str, relative: Path, expected_sha256: str) -> Any:
    path = (PROJECT / relative).resolve(strict=True)
    payload = _stable_source(path, expected_sha256)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RecursiveChildRunnerError(f"cannot load pinned source: {relative}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    try:
        exec(compile(payload, str(path), "exec"), module.__dict__)
    except BaseException:
        if sys.modules.get(name) is module:
            del sys.modules[name]
        raise
    return module


controller = _load_pinned_module(
    "_paper400_recursive_dmtcp_controller_v1",
    CONTROLLER_RELATIVE,
    EXPECTED_CONTROLLER_SHA256,
)
proof_helper = _load_pinned_module(
    "_paper400_recursive_proof_helper_v1",
    PROOF_HELPER_RELATIVE,
    EXPECTED_PROOF_HELPER_SHA256,
)
v2 = proof_helper.v2


def canonical_bytes(value: Any) -> bytes:
    return recursive.canonical_bytes(value)


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    return recursive.seal(value, field)


def _same(left: Any, right: Any) -> bool:
    return canonical_bytes(left) == canonical_bytes(right)


def _safe_root(root: Path, *, new: bool = False) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise RecursiveChildRunnerError("root must be an absolute normalized path")
    if new:
        parent = target.parent
        try:
            info = parent.lstat()
        except OSError as exc:
            raise RecursiveChildRunnerError("new root parent is unavailable") from exc
        if (
            stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
            or parent.resolve(strict=True) != parent or info.st_uid != os.geteuid()
        ):
            raise RecursiveChildRunnerError("new root parent is unsafe")
        if target.exists() or target.is_symlink():
            raise RecursiveChildRunnerError("recursive child root already exists")
        return target
    try:
        info = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise RecursiveChildRunnerError("recursive child root is unavailable") from exc
    if (
        resolved != target or stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise RecursiveChildRunnerError("recursive child root must be owned mode 0700")
    return target


def _root_identity(root: Path) -> dict[str, Any]:
    info = root.lstat()
    return {
        "path": str(root), "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": int(stat.S_IMODE(info.st_mode)), "uid": int(info.st_uid),
    }


def _mkdir(parent: Path, name: str) -> Path:
    target = parent / name
    os.mkdir(target, 0o700)
    return target


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _write_all(fd: int, payload: bytes) -> None:
    view = memoryview(payload)
    while view:
        written = os.write(fd, view)
        if written <= 0:
            raise RecursiveChildRunnerError("short immutable publication write")
        view = view[written:]


def _publish_new(path: Path, payload: bytes, *, mode: int = 0o600) -> None:
    """Publish one immutable file with a hard-link commit point."""

    if path.exists() or path.is_symlink():
        raise RecursiveChildRunnerError(f"immutable path already exists: {path}")
    temporary = path.parent / f".{path.name}.private-{uuid.uuid4().hex}"
    fd = os.open(
        temporary,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        mode,
    )
    linked = False
    try:
        _write_all(fd, payload)
        os.fsync(fd)
        os.close(fd)
        fd = -1
        os.link(temporary, path, follow_symlinks=False)
        linked = True
        _fsync_dir(path.parent)
    except FileExistsError as exc:
        raise RecursiveChildRunnerError(f"immutable path already exists: {path}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()
        if linked:
            _fsync_dir(path.parent)


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    _publish_new(path, canonical_bytes(dict(value)) + b"\n")


def _json_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RecursiveChildRunnerError("JSON has duplicate object key")
        result[key] = value
    return result


def _read_json(path: Path, *, cap: int = MAX_JSON_BYTES) -> dict[str, Any]:
    payload = _stable_bytes(path, cap=cap, executable=False)
    try:
        value = json.loads(payload, object_pairs_hook=_json_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecursiveChildRunnerError(f"invalid JSON: {path}") from exc
    if type(value) is not dict or payload not in {canonical_bytes(value), canonical_bytes(value) + b"\n"}:
        raise RecursiveChildRunnerError(f"noncanonical JSON: {path}")
    return value


@contextlib.contextmanager
def _root_lock(root: Path, *, exclusive: bool = True) -> Iterator[None]:
    path = root / ROOT_LOCK
    fd = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
            or info.st_nlink != 1 or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise RecursiveChildRunnerError("recursive child lock metadata is unsafe")
        fcntl.flock(fd, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


@contextlib.contextmanager
def _clean_controller_environment() -> Iterator[None]:
    old = dict(os.environ)
    os.environ.clear()
    os.environ.update(controller._clean_dmtcp_environment())
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(old)


@contextlib.contextmanager
def _temporary_cpu(cpu: int) -> Iterator[None]:
    if type(cpu) is not int or cpu < 0 or cpu >= os.cpu_count():
        raise RecursiveChildRunnerError("CPU identifier is invalid")
    old = os.sched_getaffinity(0)
    if cpu not in old:
        raise RecursiveChildRunnerError("requested CPU is outside current affinity")
    os.sched_setaffinity(0, {cpu})
    try:
        yield
    finally:
        os.sched_setaffinity(0, old)


@contextlib.contextmanager
def _solver_limits(proof_cap: int) -> Iterator[None]:
    if type(proof_cap) is not int or not 0 < proof_cap <= MAX_PROOF_BYTES:
        raise RecursiveChildRunnerError("proof cap is invalid")
    old_fsize = resource.getrlimit(resource.RLIMIT_FSIZE)
    old_core = resource.getrlimit(resource.RLIMIT_CORE)
    old_cpu = resource.getrlimit(resource.RLIMIT_CPU)
    if old_fsize[1] != resource.RLIM_INFINITY and old_fsize[1] < proof_cap:
        raise RecursiveChildRunnerError("hard FSIZE limit is below proof cap")
    if old_cpu[1] != resource.RLIM_INFINITY:
        raise RecursiveChildRunnerError("hard CPU limit must be unlimited")
    try:
        resource.setrlimit(resource.RLIMIT_FSIZE, (proof_cap, old_fsize[1]))
        resource.setrlimit(resource.RLIMIT_CORE, (0, old_core[1]))
        resource.setrlimit(resource.RLIMIT_CPU, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
        yield
    finally:
        resource.setrlimit(resource.RLIMIT_CPU, old_cpu)
        resource.setrlimit(resource.RLIMIT_FSIZE, old_fsize)
        resource.setrlimit(resource.RLIMIT_CORE, old_core)


def _file_binding(role: str, path: Path, *, cap: int, executable: bool) -> dict[str, Any]:
    digest, size = _sha256_file(path, cap=cap, executable=executable)
    return {
        "role": role, "path": str(path), "sha256": digest,
        "bytes": size, "executable": executable,
    }


def _source_binding() -> dict[str, Any]:
    own = Path(__file__).resolve(strict=True)
    sources = {
        "runner": _file_binding("runner", own, cap=32 << 20, executable=False),
        "recursive_split": _file_binding(
            "recursive_split", Path(recursive.__file__).resolve(strict=True),
            cap=32 << 20, executable=False,
        ),
        "dmtcp_controller": _file_binding(
            "dmtcp_controller", PROJECT / CONTROLLER_RELATIVE,
            cap=32 << 20, executable=False,
        ),
        "proof_helper": _file_binding(
            "proof_helper", PROJECT / PROOF_HELPER_RELATIVE,
            cap=32 << 20, executable=False,
        ),
    }
    if sources["dmtcp_controller"]["sha256"] != EXPECTED_CONTROLLER_SHA256:
        raise RecursiveChildRunnerError("controller source is not the frozen revision")
    if sources["proof_helper"]["sha256"] != EXPECTED_PROOF_HELPER_SHA256:
        raise RecursiveChildRunnerError("proof helper source is not the frozen revision")
    return {
        "method": "exact-source-sha256-replay-v1",
        "sources": sources,
        "source_sequence_sha256": recursive.canonical_sha256(sources),
    }


def _toolchain_binding() -> dict[str, Any]:
    paths = {
        "cadical_solver": (SOLVER, EXPECTED_SOLVER_SHA256),
        "dmtcp_launch": (DMTCP_PREFIX / "bin/dmtcp_launch", EXPECTED_DMTCP_LAUNCH_SHA256),
        "dmtcp_command": (DMTCP_PREFIX / "bin/dmtcp_command", EXPECTED_DMTCP_COMMAND_SHA256),
        "dmtcp_restart": (DMTCP_PREFIX / "bin/dmtcp_restart", EXPECTED_DMTCP_RESTART_SHA256),
        "drat_checker": (DRAT_CHECKER, EXPECTED_DRAT_SHA256),
        "lrat_checker": (LRAT_CHECKER, EXPECTED_LRAT_SHA256),
    }
    tools: dict[str, dict[str, Any]] = {}
    for role, (path, expected) in paths.items():
        record = _file_binding(role, path, cap=512 << 20, executable=True)
        if record["sha256"] != expected:
            raise RecursiveChildRunnerError(f"tool hash mismatch: {role}")
        tools[role] = record
    if str(v2.DRAT_TRIM_PATH) != str(DRAT_CHECKER) or str(v2.LRAT_CHECK_PATH) != str(LRAT_CHECKER):
        raise RecursiveChildRunnerError("proof helper checker paths do not match fixed tools")
    return {
        "method": "fixed-tool-path-sha256-v1",
        "tools": tools,
        "tool_sequence_sha256": recursive.canonical_sha256(tools),
    }


def _validate_parent_audit(audit: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "schema_version", "kind", "parent_root", "parent_root_identity",
        "parent_static_sha256", "parent_session_sha256", "parent_dimacs_sha256",
        "parent_dimacs_bytes", "parent_generation", "parent_pid",
        "parent_proc_start_ticks", "observed_state", "timing_ledger",
        "timing_evidence", "timing_trigger", "split_allowed", "hardness_only",
        "solver_terminal_claim", "source_binding", "audit_sha256",
    }
    value = dict(audit)
    if (
        set(value) != required or not recursive.selfhash_valid(value, "audit_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != PARENT_AUDIT_KIND
        or type(value.get("parent_root")) is not str
        or not recursive.is_sha256(value.get("parent_static_sha256"))
        or not recursive.is_sha256(value.get("parent_session_sha256"))
        or not recursive.is_sha256(value.get("parent_dimacs_sha256"))
        or type(value.get("parent_dimacs_bytes")) is not int
        or value["parent_dimacs_bytes"] <= 0
        or type(value.get("parent_generation")) is not int or value["parent_generation"] < 0
        or type(value.get("parent_pid")) is not int or value["parent_pid"] <= 0
        or type(value.get("parent_proc_start_ticks")) is not int or value["parent_proc_start_ticks"] < 0
        or value.get("observed_state") not in {"RUNNING", "CHECKPOINTED", "INACTIVE"}
        or value.get("split_allowed") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or type(value.get("timing_ledger")) is not dict
        or type(value.get("timing_evidence")) is not dict
        or type(value.get("timing_trigger")) is not dict
        or type(value.get("source_binding")) is not dict
    ):
        raise RecursiveChildRunnerError("parent timeout audit is malformed")
    if not recursive.selfhash_valid(value["timing_ledger"], "ledger_sha256"):
        raise RecursiveChildRunnerError("parent audit ledger self-hash is invalid")
    if not recursive.selfhash_valid(value["timing_evidence"], "evidence_sha256"):
        raise RecursiveChildRunnerError("parent audit evidence self-hash is invalid")
    if not recursive.selfhash_valid(value["timing_trigger"], "trigger_sha256"):
        raise RecursiveChildRunnerError("parent audit trigger self-hash is invalid")
    if value["timing_trigger"].get("evidence_sha256") != value["timing_evidence"]["evidence_sha256"]:
        raise RecursiveChildRunnerError("parent audit trigger/evidence mismatch")
    if value["timing_evidence"].get("timed_out") is not True:
        raise RecursiveChildRunnerError("parent audit has no timeout evidence")
    return value


def _resource_policy(
    *, proof_max_bytes: int, checkpoint_image_max_bytes: int,
    checkpoint_generation_max: int,
) -> dict[str, Any]:
    if (
        type(proof_max_bytes) is not int or not 0 < proof_max_bytes <= MAX_PROOF_BYTES
        or type(checkpoint_image_max_bytes) is not int
        or not 0 < checkpoint_image_max_bytes <= MAX_CHECKPOINT_IMAGE_BYTES
        or type(checkpoint_generation_max) is not int
        or not 1 <= checkpoint_generation_max <= 256
    ):
        raise RecursiveChildRunnerError("recursive child resource policy is invalid")
    return {
        "proof_max_bytes": proof_max_bytes,
        "checkpoint_image_max_bytes": checkpoint_image_max_bytes,
        "checkpoint_generation_max": checkpoint_generation_max,
        "checker_timeout_seconds": int(v2.CHECKER_TIMEOUT_S),
        "solver_workers": 1,
        "memory_admission_min_available_bytes": MIN_AVAILABLE_MEMORY_BYTES,
        "disk_admission_headroom_bytes": MIN_AVAILABLE_DISK_HEADROOM_BYTES,
    }


def _child_from_manifest(manifest: Mapping[str, Any], path: str) -> dict[str, Any]:
    leaves = manifest.get("leaves")
    if type(path) is not str or type(leaves) is not list:
        raise RecursiveChildRunnerError("recursive leaf path is invalid")
    matches = [item for item in leaves if type(item) is dict and item.get("path") == path]
    if len(matches) != 1:
        raise RecursiveChildRunnerError("recursive leaf path is missing or ambiguous")
    leaf = matches[0]
    if not recursive.selfhash_valid(leaf, "leaf_sha256"):
        raise RecursiveChildRunnerError("recursive leaf self-hash is invalid")
    return dict(leaf)


def _static_value(
    *, root: Path, parent_payload: bytes, manifest: Mapping[str, Any],
    leaf: Mapping[str, Any], parent_audit: Mapping[str, Any], policy: Mapping[str, Any],
) -> dict[str, Any]:
    parent_sha = hashlib.sha256(parent_payload).hexdigest()
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": STATIC_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "parent": {
            "parent_root": parent_audit["parent_root"],
            "parent_static_sha256": parent_audit["parent_static_sha256"],
            "parent_session_sha256": parent_audit["parent_session_sha256"],
            "parent_dimacs_sha256": parent_sha,
            "parent_dimacs_bytes": len(parent_payload),
            "parent_audit_sha256": parent_audit["audit_sha256"],
        },
        "split_manifest_sha256": manifest["manifest_sha256"],
        "leaf": dict(leaf),
        "child": {
            "leaf_id": leaf["leaf_id"],
            "leaf_sha256": leaf["leaf_sha256"],
            "path": leaf["path"],
            "child_cnf_sha256": leaf["child_cnf_sha256"],
            "child_dimacs_sha256": leaf["child_dimacs_sha256"],
            "child_num_variables": leaf["child_num_variables"],
            "child_num_clauses": leaf["child_num_clauses"],
            "child_dimacs_bytes": leaf["child_dimacs_bytes"],
        },
        "resource_policy": dict(policy),
        "source_binding": _source_binding(),
        "toolchain_binding": _toolchain_binding(),
        "transport_authority": "TEST_ONLY",
        "transport_trusted_for_scientific_proof": False,
        "hardness_only_trigger": True,
        "parent_solver_terminal_claim": False,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "static_sha256")


def prepare_root_from_material(
    root: Path,
    *,
    parent_dimacs: bytes,
    split_manifest: Mapping[str, Any],
    leaf_path: str,
    parent_audit: Mapping[str, Any],
    proof_max_bytes: int = DEFAULT_PROOF_MAX_BYTES,
    checkpoint_image_max_bytes: int = DEFAULT_CHECKPOINT_IMAGE_MAX_BYTES,
    checkpoint_generation_max: int = DEFAULT_CHECKPOINT_GENERATION_MAX,
) -> dict[str, Any]:
    """Create one immutable recursive child root from audited local material."""

    target = _safe_root(root, new=True)
    audit = _validate_parent_audit(parent_audit)
    payload = bytes(parent_dimacs)
    if len(payload) > MAX_DIMACS_BYTES:
        raise RecursiveChildRunnerError("parent DIMACS exceeds cap")
    if (
        hashlib.sha256(payload).hexdigest() != audit["parent_dimacs_sha256"]
        or len(payload) != audit["parent_dimacs_bytes"]
    ):
        raise RecursiveChildRunnerError("parent DIMACS does not match timeout audit")
    manifest = dict(split_manifest)
    recursive.verify_cover(manifest, payload)
    if manifest.get("trigger") != audit["timing_trigger"]:
        raise RecursiveChildRunnerError("split manifest trigger does not match timeout audit")
    leaf = _child_from_manifest(manifest, leaf_path)
    child_payload = recursive.render_leaf_payload(manifest, payload, leaf_path)
    if (
        hashlib.sha256(child_payload).hexdigest() != leaf["child_dimacs_sha256"]
        or len(child_payload) != leaf["child_dimacs_bytes"]
    ):
        raise RecursiveChildRunnerError("rendered child DIMACS does not bind manifest leaf")
    policy = _resource_policy(
        proof_max_bytes=proof_max_bytes,
        checkpoint_image_max_bytes=checkpoint_image_max_bytes,
        checkpoint_generation_max=checkpoint_generation_max,
    )
    os.mkdir(target, 0o700)
    _fsync_dir(target.parent)
    try:
        for name in ("static", "state", "artifacts", "runtime", "logs"):
            _mkdir(target, name)
        _publish_new(target / ROOT_LOCK, b"")
        _publish_new(target / STATIC_PARENT_DIMACS, payload)
        _publish_json(target / STATIC_SPLIT_MANIFEST, manifest)
        _publish_json(target / STATIC_LEAF, leaf)
        _publish_json(target / STATIC_PARENT_AUDIT, audit)
        _publish_new(target / STATIC_CHILD_DIMACS, child_payload)
        static = _static_value(
            root=target, parent_payload=payload, manifest=manifest, leaf=leaf,
            parent_audit=audit, policy=policy,
        )
        _publish_json(target / STATIC_COMMIT, static)
        _load_static(target)
        return static
    except BaseException:
        # Retain incomplete roots as forensic evidence.  They can never pass
        # ``_load_static`` and are never reused in place.
        raise


def _load_static(root: Path) -> dict[str, Any]:
    target = _safe_root(root)
    static = _read_json(target / STATIC_COMMIT)
    required = {
        "schema_version", "kind", "gate", "root", "root_identity", "parent",
        "split_manifest_sha256", "leaf", "child", "resource_policy",
        "source_binding", "toolchain_binding", "transport_authority",
        "transport_trusted_for_scientific_proof", "hardness_only_trigger",
        "parent_solver_terminal_claim", "global_distance_claim",
        "publication_certificate", "upload_authorized", "static_sha256",
    }
    if (
        set(static) != required or not recursive.selfhash_valid(static, "static_sha256")
        or static.get("schema_version") != SCHEMA_VERSION or static.get("kind") != STATIC_KIND
        or static.get("gate") != GATE or static.get("root") != str(target)
        or not _same(static.get("root_identity"), _root_identity(target))
        or static.get("transport_authority") != "TEST_ONLY"
        or static.get("transport_trusted_for_scientific_proof") is not False
        or static.get("hardness_only_trigger") is not True
        or static.get("parent_solver_terminal_claim") is not False
        or static.get("global_distance_claim") is not None
        or static.get("publication_certificate") is not False
        or static.get("upload_authorized") is not False
    ):
        raise RecursiveChildRunnerError("recursive static record is malformed")
    if not _same(static.get("source_binding"), _source_binding()):
        raise RecursiveChildRunnerError("recursive source binding changed")
    if not _same(static.get("toolchain_binding"), _toolchain_binding()):
        raise RecursiveChildRunnerError("recursive toolchain binding changed")
    audit = _validate_parent_audit(_read_json(target / STATIC_PARENT_AUDIT))
    parent_payload = _stable_bytes(target / STATIC_PARENT_DIMACS, cap=MAX_DIMACS_BYTES, executable=False)
    parent = static.get("parent")
    if (
        type(parent) is not dict
        or parent.get("parent_audit_sha256") != audit["audit_sha256"]
        or parent.get("parent_root") != audit["parent_root"]
        or parent.get("parent_static_sha256") != audit["parent_static_sha256"]
        or parent.get("parent_session_sha256") != audit["parent_session_sha256"]
        or parent.get("parent_dimacs_sha256") != hashlib.sha256(parent_payload).hexdigest()
        or parent.get("parent_dimacs_bytes") != len(parent_payload)
    ):
        raise RecursiveChildRunnerError("parent material/audit binding mismatch")
    manifest = _read_json(target / STATIC_SPLIT_MANIFEST)
    recursive.verify_cover(manifest, parent_payload)
    if manifest.get("manifest_sha256") != static.get("split_manifest_sha256"):
        raise RecursiveChildRunnerError("static split manifest binding mismatch")
    if manifest.get("trigger") != audit["timing_trigger"]:
        raise RecursiveChildRunnerError("static timeout trigger mismatch")
    leaf = _read_json(target / STATIC_LEAF)
    selected = _child_from_manifest(manifest, static.get("child", {}).get("path"))
    if not _same(leaf, selected) or not _same(static.get("leaf"), selected):
        raise RecursiveChildRunnerError("static recursive leaf binding mismatch")
    child_payload = _stable_bytes(target / STATIC_CHILD_DIMACS, cap=MAX_DIMACS_BYTES, executable=False)
    expected_payload = recursive.render_leaf_payload(manifest, parent_payload, selected["path"])
    if child_payload != expected_payload:
        raise RecursiveChildRunnerError("static child DIMACS bytes changed")
    child = static.get("child")
    if not isinstance(child, dict) or any(
        child.get(key) != selected.get(key)
        for key in (
            "leaf_id", "leaf_sha256", "path", "child_cnf_sha256",
            "child_dimacs_sha256", "child_num_variables", "child_num_clauses",
            "child_dimacs_bytes",
        )
    ):
        raise RecursiveChildRunnerError("static child identity mismatch")
    if (
        hashlib.sha256(child_payload).hexdigest() != child["child_dimacs_sha256"]
        or len(child_payload) != child["child_dimacs_bytes"]
    ):
        raise RecursiveChildRunnerError("static child DIMACS hash mismatch")
    policy = static.get("resource_policy")
    if not isinstance(policy, dict) or policy != _resource_policy(
        proof_max_bytes=policy.get("proof_max_bytes"),
        checkpoint_image_max_bytes=policy.get("checkpoint_image_max_bytes"),
        checkpoint_generation_max=policy.get("checkpoint_generation_max"),
    ):
        raise RecursiveChildRunnerError("static resource policy mismatch")
    return {
        "static": static, "audit": audit, "manifest": manifest, "leaf": selected,
        "parent_payload": parent_payload, "child_payload": child_payload,
        "policy": policy,
    }


def _runtime_libraries() -> list[Path]:
    binding = proof_helper._toolchain_binding()
    closure = binding.get("dynamic_elf_tcb") if type(binding) is dict else None
    objects = closure.get("objects") if type(closure) is dict else None
    if type(objects) is not list or not objects:
        raise RecursiveChildRunnerError("pinned proof helper runtime closure is unavailable")
    paths: list[Path] = []
    for item in objects:
        physical = item.get("physical") if type(item) is dict else None
        value = physical.get("realpath") if type(physical) is dict else None
        if type(value) is not str or not Path(value).is_absolute():
            raise RecursiveChildRunnerError("runtime closure entry is malformed")
        paths.append(Path(value))
    return sorted(set(paths), key=str)


def _memory_available_bytes() -> int:
    try:
        for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
            fields = line.split()
            if len(fields) == 3 and fields[0] == "MemAvailable:" and fields[2] == "kB":
                return int(fields[1]) * 1024
    except (OSError, UnicodeDecodeError, ValueError):
        pass
    raise RecursiveChildRunnerError("cannot read available memory")


def _resource_admission(root: Path, policy: Mapping[str, Any]) -> dict[str, Any]:
    available_memory = _memory_available_bytes()
    statvfs = os.statvfs(root)
    available_disk = statvfs.f_bavail * statvfs.f_frsize
    memory_minimum = policy["memory_admission_min_available_bytes"]
    disk_minimum = policy["disk_admission_headroom_bytes"] + policy["proof_max_bytes"]
    if available_memory < memory_minimum:
        raise RecursiveChildRunnerError("available memory is below recursive child admission floor")
    if available_disk < disk_minimum:
        raise RecursiveChildRunnerError("available disk is below recursive child admission floor")
    return {
        "available_memory_bytes": available_memory,
        "available_disk_bytes": available_disk,
        "minimum_memory_bytes": memory_minimum,
        "minimum_disk_bytes": disk_minimum,
        "passed": True,
    }


def _verify_live_affinity(pid: int, cpu: int) -> dict[str, Any]:
    try:
        observed = sorted(os.sched_getaffinity(pid))
    except (OSError, ProcessLookupError) as exc:
        raise RecursiveChildRunnerError("cannot inspect child solver affinity") from exc
    if observed != [cpu]:
        raise RecursiveChildRunnerError("child solver affinity is not the leased singleton CPU")
    return {"pid": pid, "cpu": cpu, "observed_affinity": observed, "verified": True}


def _verify_live_limits(pid: int, proof_cap: int) -> dict[str, Any]:
    if not hasattr(resource, "prlimit"):
        raise RecursiveChildRunnerError("platform cannot inspect solver resource limits")
    try:
        fsize = resource.prlimit(pid, resource.RLIMIT_FSIZE)
        core = resource.prlimit(pid, resource.RLIMIT_CORE)
        cpu = resource.prlimit(pid, resource.RLIMIT_CPU)
    except (OSError, PermissionError, ProcessLookupError) as exc:
        raise RecursiveChildRunnerError("cannot inspect child solver resource limits") from exc
    if (
        fsize[0] != proof_cap or (fsize[1] != resource.RLIM_INFINITY and fsize[1] < proof_cap)
        or core[0] != 0 or cpu != (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
    ):
        raise RecursiveChildRunnerError("child solver resource limit policy mismatch")
    return {
        "pid": pid, "proof_fsize_soft_bytes": fsize[0], "proof_fsize_hard_bytes": fsize[1],
        "core_soft_bytes": core[0], "core_hard_bytes": core[1],
        "cpu_soft_seconds": cpu[0], "cpu_hard_seconds": cpu[1], "verified": True,
    }


def _session_value(
    root: Path, loaded: Mapping[str, Any], *, cpu: int,
    config: Mapping[str, Any], started: Mapping[str, Any],
    affinity: Mapping[str, Any], limits: Mapping[str, Any], admission: Mapping[str, Any],
) -> dict[str, Any]:
    child = loaded["static"]["child"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": SESSION_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "static_sha256": loaded["static"]["static_sha256"],
        "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
        "leaf_id": child["leaf_id"],
        "leaf_sha256": child["leaf_sha256"],
        "child_dimacs_sha256": child["child_dimacs_sha256"],
        "controller_root": str(root / RUNTIME_ROOT),
        "controller_config_sha256": config["self_sha256"],
        "controller_start_sha256": started["self_sha256"],
        "expected_single_cpu": cpu,
        "started_affinity": dict(affinity),
        "started_limits": dict(limits),
        "resource_admission": dict(admission),
        "transport_authority": "TEST_ONLY",
        "transport_trusted_for_scientific_proof": False,
    }, "record_sha256")


def _start_claim_value(
    root: Path, loaded: Mapping[str, Any], *, cpu: int,
    admission: Mapping[str, Any],
) -> dict[str, Any]:
    """Bind the intended singleton CPU before any transport mutation.

    A controller start can finish before this runner has published its session
    receipt.  This immutable claim makes that narrow crash window recoverable
    without ever trying a second controller initialization on the same root.
    """

    child = loaded["static"]["child"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": START_CLAIM_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "static_sha256": loaded["static"]["static_sha256"],
        "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
        "leaf_id": child["leaf_id"],
        "leaf_sha256": child["leaf_sha256"],
        "child_dimacs_sha256": child["child_dimacs_sha256"],
        "controller_root": str(root / RUNTIME_ROOT),
        "expected_single_cpu": cpu,
        "resource_admission": dict(admission),
        "transport_authority": "TEST_ONLY",
        "transport_trusted_for_scientific_proof": False,
    }, "record_sha256")


def _validate_resource_admission(admission: Any, policy: Mapping[str, Any]) -> bool:
    if not isinstance(admission, dict):
        return False
    required = {
        "available_memory_bytes", "available_disk_bytes", "minimum_memory_bytes",
        "minimum_disk_bytes", "passed",
    }
    if set(admission) != required or admission.get("passed") is not True:
        return False
    values = ("available_memory_bytes", "available_disk_bytes", "minimum_memory_bytes", "minimum_disk_bytes")
    if any(type(admission.get(key)) is not int or admission[key] < 0 for key in values):
        return False
    return bool(
        admission["minimum_memory_bytes"] == policy["memory_admission_min_available_bytes"]
        and admission["minimum_disk_bytes"]
        == policy["disk_admission_headroom_bytes"] + policy["proof_max_bytes"]
        and admission["available_memory_bytes"] >= admission["minimum_memory_bytes"]
        and admission["available_disk_bytes"] >= admission["minimum_disk_bytes"]
    )


def _read_start_claim(root: Path, loaded: Mapping[str, Any]) -> dict[str, Any]:
    claim = _read_json(root / START_CLAIM)
    required = {
        "schema_version", "kind", "gate", "root", "root_identity", "static_sha256",
        "split_manifest_sha256", "leaf_id", "leaf_sha256", "child_dimacs_sha256",
        "controller_root", "expected_single_cpu", "resource_admission",
        "transport_authority", "transport_trusted_for_scientific_proof", "record_sha256",
    }
    child = loaded["static"]["child"]
    if (
        set(claim) != required or not recursive.selfhash_valid(claim, "record_sha256")
        or claim.get("schema_version") != SCHEMA_VERSION or claim.get("kind") != START_CLAIM_KIND
        or claim.get("gate") != GATE or claim.get("root") != str(root)
        or not _same(claim.get("root_identity"), _root_identity(root))
        or claim.get("static_sha256") != loaded["static"]["static_sha256"]
        or claim.get("split_manifest_sha256") != loaded["manifest"]["manifest_sha256"]
        or claim.get("leaf_id") != child["leaf_id"] or claim.get("leaf_sha256") != child["leaf_sha256"]
        or claim.get("child_dimacs_sha256") != child["child_dimacs_sha256"]
        or claim.get("controller_root") != str(root / RUNTIME_ROOT)
        or type(claim.get("expected_single_cpu")) is not int
        or claim["expected_single_cpu"] < 0 or claim["expected_single_cpu"] >= os.cpu_count()
        or not _validate_resource_admission(claim.get("resource_admission"), loaded["policy"])
        or claim.get("transport_authority") != "TEST_ONLY"
        or claim.get("transport_trusted_for_scientific_proof") is not False
    ):
        raise RecursiveChildRunnerError("recursive child start claim is malformed")
    return claim


def _ensure_start_claim(root: Path, loaded: Mapping[str, Any], *, cpu: int) -> dict[str, Any]:
    path = root / START_CLAIM
    if path.exists():
        claim = _read_start_claim(root, loaded)
        if claim["expected_single_cpu"] != cpu:
            raise RecursiveChildRunnerError("recursive child start CPU changed after claim")
        return claim
    admission = _resource_admission(root, loaded["policy"])
    claim = _start_claim_value(root, loaded, cpu=cpu, admission=admission)
    _publish_json(path, claim)
    return claim


def _expected_controller_config(root: Path) -> dict[str, Any]:
    """Return the exact controller bindings this runner is allowed to join."""

    runtime = root / RUNTIME_ROOT
    solver = SOLVER.resolve(strict=True)
    runtime_paths = {path.resolve(strict=True) for path in _runtime_libraries()}
    interpreter = controller._elf_interpreter(solver)
    if interpreter is not None:
        runtime_paths.add(Path(interpreter).resolve(strict=True))
    return {
        "root": str(runtime.resolve(strict=True)),
        "cnf": controller.stable_file_record(root / STATIC_CHILD_DIMACS),
        "solver": controller.stable_file_record(solver),
        "solver_args": ["-q"],
        "proof_relative_path": "proof.drat",
        "controller_source": controller.stable_file_record(PROJECT / CONTROLLER_RELATIVE),
        "dmtcp": controller.build_dmtcp_binding(DMTCP_PREFIX),
        "runtime_libraries": [
            controller.stable_file_record(path) for path in sorted(runtime_paths, key=str)
        ],
        "runtime_libraries_complete_attestation": True,
    }


def _load_expected_controller_config(root: Path) -> dict[str, Any]:
    """Verify a pre-existing controller before any recovery/start action."""

    runtime = root / RUNTIME_ROOT
    with _clean_controller_environment():
        config, _binaries = controller._load_and_verify_config(runtime)
    expected = _expected_controller_config(root)
    if any(config.get(key) != value for key, value in expected.items()):
        raise RecursiveChildRunnerError("controller configuration is not this recursive child")
    return config


def _active_start_commit(root: Path, config: Mapping[str, Any]) -> dict[str, Any]:
    """Read the authenticated generation-zero start commit exactly once."""

    runtime = root / RUNTIME_ROOT
    with _clean_controller_environment():
        status = controller.inspect(runtime, verify_hashes=True)
    generations = status.get("generations")
    if (
        status.get("config_manifest_sha256") != config.get("self_sha256")
        or not isinstance(generations, list) or len(generations) != 1
        or not isinstance(generations[0], dict) or generations[0].get("generation") != 0
        or status.get("state") != "RUNNING"
    ):
        raise RecursiveChildRunnerError("unsealed child start is not one live generation zero")
    active = controller._active_commit(controller._generation_dir(runtime, 0), 0)
    if (
        active.get("kind") != "start.commit"
        or active.get("init_manifest_sha256") != config["self_sha256"]
        or active.get("self_sha256") != generations[0].get("active_manifest_sha256")
        or generations[0].get("pid_identity_alive") is not True
    ):
        raise RecursiveChildRunnerError("unsealed child start commit is not live and bound")
    return active


def _seal_started_session(
    root: Path, loaded: Mapping[str, Any], claim: Mapping[str, Any],
    *, config: Mapping[str, Any], started: Mapping[str, Any],
) -> dict[str, Any]:
    """Publish the idempotent session receipt only for a bound live solver."""

    if claim != _read_start_claim(root, loaded):
        raise RecursiveChildRunnerError("recursive child start claim changed before session seal")
    if started.get("init_manifest_sha256") != config.get("self_sha256"):
        raise RecursiveChildRunnerError("start commit/config binding mismatch")
    pid = started.get("pid")
    if type(pid) is not int or pid <= 0:
        raise RecursiveChildRunnerError("controller start did not expose a solver PID")
    affinity = _verify_live_affinity(pid, claim["expected_single_cpu"])
    limits = _verify_live_limits(pid, loaded["policy"]["proof_max_bytes"])
    session = _session_value(
        root, loaded, cpu=claim["expected_single_cpu"], config=config, started=started,
        affinity=affinity, limits=limits, admission=claim["resource_admission"],
    )
    path = root / SESSION_COMMIT
    if path.exists():
        existing = _load_session(root, loaded)
        if not _same(existing, session):
            raise RecursiveChildRunnerError("existing recursive child session does not replay start")
        return existing
    _publish_json(path, session)
    return session


def _load_session(root: Path, loaded: Mapping[str, Any]) -> dict[str, Any]:
    session = _read_json(root / SESSION_COMMIT)
    required = {
        "schema_version", "kind", "gate", "root", "root_identity", "static_sha256",
        "split_manifest_sha256", "leaf_id", "leaf_sha256", "child_dimacs_sha256",
        "controller_root", "controller_config_sha256", "controller_start_sha256",
        "expected_single_cpu", "started_affinity", "started_limits", "resource_admission",
        "transport_authority", "transport_trusted_for_scientific_proof", "record_sha256",
    }
    child = loaded["static"]["child"]
    if (
        set(session) != required or not recursive.selfhash_valid(session, "record_sha256")
        or session.get("schema_version") != SCHEMA_VERSION or session.get("kind") != SESSION_KIND
        or session.get("gate") != GATE or session.get("root") != str(root)
        or not _same(session.get("root_identity"), _root_identity(root))
        or session.get("static_sha256") != loaded["static"]["static_sha256"]
        or session.get("split_manifest_sha256") != loaded["manifest"]["manifest_sha256"]
        or session.get("leaf_id") != child["leaf_id"] or session.get("leaf_sha256") != child["leaf_sha256"]
        or session.get("child_dimacs_sha256") != child["child_dimacs_sha256"]
        or session.get("controller_root") != str(root / RUNTIME_ROOT)
        or type(session.get("expected_single_cpu")) is not int
        or session["expected_single_cpu"] < 0
        or type(session.get("controller_config_sha256")) is not str
        or not recursive.is_sha256(session["controller_config_sha256"])
        or type(session.get("controller_start_sha256")) is not str
        or not recursive.is_sha256(session["controller_start_sha256"])
        or not _validate_resource_admission(session.get("resource_admission"), loaded["policy"])
        or session.get("transport_authority") != "TEST_ONLY"
        or session.get("transport_trusted_for_scientific_proof") is not False
    ):
        raise RecursiveChildRunnerError("recursive child session is malformed")
    affinity = session["started_affinity"]
    limits = session["started_limits"]
    if (
        not isinstance(affinity, dict)
        or set(affinity) != {"pid", "cpu", "observed_affinity", "verified"}
        or type(affinity.get("pid")) is not int or affinity["pid"] <= 0
        or affinity.get("cpu") != session["expected_single_cpu"]
        or affinity.get("observed_affinity") != [session["expected_single_cpu"]]
        or affinity.get("verified") is not True
        or not isinstance(limits, dict)
        or set(limits) != {
            "pid", "proof_fsize_soft_bytes", "proof_fsize_hard_bytes", "core_soft_bytes",
            "core_hard_bytes", "cpu_soft_seconds", "cpu_hard_seconds", "verified",
        }
        or limits.get("pid") != affinity["pid"]
        or limits.get("proof_fsize_soft_bytes") != loaded["policy"]["proof_max_bytes"]
        or type(limits.get("proof_fsize_hard_bytes")) is not int
        or limits["proof_fsize_hard_bytes"] != resource.RLIM_INFINITY
        and limits["proof_fsize_hard_bytes"] < loaded["policy"]["proof_max_bytes"]
        or limits.get("core_soft_bytes") != 0
        or type(limits.get("core_hard_bytes")) is not int
        or limits.get("cpu_soft_seconds") != resource.RLIM_INFINITY
        or limits.get("cpu_hard_seconds") != resource.RLIM_INFINITY
        or limits.get("verified") is not True
    ):
        raise RecursiveChildRunnerError("recursive child session start attestation is malformed")
    return session


def start_root(root: Path, *, cpu: int) -> dict[str, Any]:
    target = _safe_root(root)
    with _root_lock(target):
        loaded = _load_static(target)
        if (target / SESSION_COMMIT).exists():
            session = _load_session(target, loaded)
            if session["expected_single_cpu"] != cpu:
                raise RecursiveChildRunnerError("recursive child start CPU differs from session")
            return session
        if (target / FINAL_COMMIT).exists() or (target / TERMINAL_CLAIM).exists():
            raise RecursiveChildRunnerError("terminal recursive child has no sealed session")
        claim = _ensure_start_claim(target, loaded, cpu=cpu)
        runtime = target / RUNTIME_ROOT
        if runtime.exists() or runtime.is_symlink():
            config = _load_expected_controller_config(target)
            with _clean_controller_environment():
                state = controller.inspect(runtime, verify_hashes=True).get("state")
            if state == "INITIALIZED":
                with _clean_controller_environment(), _temporary_cpu(cpu), _solver_limits(
                    loaded["policy"]["proof_max_bytes"]
                ):
                    controller.start(runtime)
            elif state != "RUNNING":
                raise RecursiveChildRunnerError("unsealed child transport is not safely recoverable")
            started = _active_start_commit(target, config)
            return _seal_started_session(target, loaded, claim, config=config, started=started)
        with _clean_controller_environment(), _temporary_cpu(cpu), _solver_limits(
            loaded["policy"]["proof_max_bytes"]
        ):
            initialized = controller.initialize(
                target / RUNTIME_ROOT,
                cnf=target / STATIC_CHILD_DIMACS,
                solver=SOLVER,
                dmtcp_prefix=DMTCP_PREFIX,
                solver_args=["-q"],
                runtime_libs=_runtime_libraries(),
                runtime_libs_complete=True,
            )
        config = _load_expected_controller_config(target)
        if config.get("self_sha256") != initialized.get("self_sha256"):
            raise RecursiveChildRunnerError("initialized controller configuration changed")
        with _clean_controller_environment(), _temporary_cpu(cpu), _solver_limits(
            loaded["policy"]["proof_max_bytes"]
        ):
            controller.start(target / RUNTIME_ROOT)
        started = _active_start_commit(target, config)
        return _seal_started_session(target, loaded, claim, config=config, started=started)


def _controller_status(root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any], *, verify_hashes: bool) -> dict[str, Any]:
    with _clean_controller_environment():
        status = controller.inspect(root / RUNTIME_ROOT, verify_hashes=verify_hashes)
    if status.get("config_manifest_sha256") != session["controller_config_sha256"]:
        raise RecursiveChildRunnerError("controller config binding changed")
    state = status.get("state")
    if state not in {"RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED", "POISONED"}:
        raise RecursiveChildRunnerError("controller state is unknown")
    generations = status.get("generations")
    if type(generations) is not list or not generations:
        raise RecursiveChildRunnerError("controller generation history is missing")
    if len(generations) > loaded["policy"]["checkpoint_generation_max"]:
        raise RecursiveChildRunnerError("checkpoint generation cap exceeded")
    summary = generations[-1]
    if type(summary) is not dict:
        raise RecursiveChildRunnerError("latest controller generation is malformed")
    generation = summary.get("generation")
    if type(generation) is not int or generation < 0:
        raise RecursiveChildRunnerError("latest controller generation number is malformed")
    # ``controller.inspect`` intentionally summarizes active commits without
    # exposing their PID fields.  Re-read the immutable active commit to bind
    # PID/start-tick identity before making any affinity or stopped-proof
    # decision.  The summary's authenticated manifest hash must agree.
    active = controller._active_commit(
        controller._generation_dir(root / RUNTIME_ROOT, generation), generation,
    )
    if active.get("self_sha256") != summary.get("active_manifest_sha256"):
        raise RecursiveChildRunnerError("controller summary/active commit mismatch")
    latest = {
        **summary,
        "pid": active.get("pid"),
        "proc_start_ticks": active.get("proc_start_ticks"),
        "active_commit": active,
    }
    status = {**status, "generations": [*generations[:-1], latest]}
    if state == "RUNNING":
        pid = latest.get("pid")
        if type(pid) is not int or latest.get("pid_identity_alive") is not True:
            raise RecursiveChildRunnerError("running controller has no live solver identity")
        _verify_live_affinity(pid, session["expected_single_cpu"])
        _verify_live_limits(pid, loaded["policy"]["proof_max_bytes"])
    return status


def checkpoint_stop_root(root: Path) -> dict[str, Any]:
    target = _safe_root(root)
    with _root_lock(target):
        loaded = _load_static(target)
        session = _load_session(target, loaded)
        if (target / FINAL_COMMIT).exists():
            raise RecursiveChildRunnerError("final recursive child cannot be checkpointed")
        status = _controller_status(target, loaded, session, verify_hashes=False)
        if status["state"] != "RUNNING":
            raise RecursiveChildRunnerError("checkpoint-stop requires a running recursive child")
        with _clean_controller_environment():
            result = controller.checkpoint_stop(target / RUNTIME_ROOT)
        images = result.get("images")
        if type(images) is not list or len(images) != 1:
            raise RecursiveChildRunnerError("checkpoint did not produce one bound image")
        image = images[0]
        if type(image) is not dict or type(image.get("bytes")) is not int:
            raise RecursiveChildRunnerError("checkpoint image record is malformed")
        if image["bytes"] > loaded["policy"]["checkpoint_image_max_bytes"]:
            raise RecursiveChildRunnerError("checkpoint image exceeds recursive child cap")
        _controller_status(target, loaded, session, verify_hashes=True)
        return result


def resume_root(root: Path) -> dict[str, Any]:
    target = _safe_root(root)
    with _root_lock(target):
        loaded = _load_static(target)
        session = _load_session(target, loaded)
        if (target / FINAL_COMMIT).exists() or (target / TERMINAL_CLAIM).exists():
            raise RecursiveChildRunnerError("terminal recursive child cannot resume")
        status = _controller_status(target, loaded, session, verify_hashes=True)
        if status["state"] != "CHECKPOINTED":
            raise RecursiveChildRunnerError("resume requires a checkpointed recursive child")
        with _clean_controller_environment():
            result = controller.resume(target / RUNTIME_ROOT)
        pid = result.get("pid")
        if type(pid) is not int:
            raise RecursiveChildRunnerError("resume did not expose a solver PID")
        _verify_live_affinity(pid, session["expected_single_cpu"])
        _verify_live_limits(pid, loaded["policy"]["proof_max_bytes"])
        return result


def _writable_holders(path: Path) -> list[int]:
    """List processes with a write-capable fd for one exact proof inode."""

    try:
        info = path.stat(follow_symlinks=False)
        canonical = str(path.resolve(strict=True))
    except (OSError, RuntimeError) as exc:
        raise RecursiveChildRunnerError("cannot inspect proof ownership") from exc
    holders: list[int] = []
    for name in os.listdir("/proc"):
        if not name.isdecimal():
            continue
        pid = int(name)
        directory = Path("/proc") / name / "fd"
        try:
            entries = list(directory.iterdir())
        except OSError:
            continue
        for descriptor in entries:
            try:
                target = os.readlink(descriptor)
                fd_info = (Path("/proc") / name / "fdinfo" / descriptor.name).read_text(encoding="ascii")
            except (OSError, UnicodeDecodeError):
                continue
            if target != canonical:
                continue
            flags_line = next((line for line in fd_info.splitlines() if line.startswith("flags:")), None)
            if flags_line is None:
                continue
            try:
                flags = int(flags_line.split()[1], 8)
            except (IndexError, ValueError):
                continue
            if flags & os.O_ACCMODE != os.O_RDONLY:
                holders.append(pid)
                break
    # The inode/path check above matters because a replace/recreate can have
    # the same pathname while a stale writer remains attached to an old inode.
    if path.stat(follow_symlinks=False).st_ino != info.st_ino:
        raise RecursiveChildRunnerError("proof path changed while scanning holders")
    return sorted(set(holders))


def _stopped_snapshot(root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    status = _controller_status(root, loaded, session, verify_hashes=True)
    state = status["state"]
    if state not in {"CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"}:
        raise RecursiveChildRunnerError("proof harvest requires checkpointed or inactive transport")
    latest = status["generations"][-1]
    if latest.get("pid_identity_alive") is not False:
        raise RecursiveChildRunnerError("stopped transport retains a live solver identity")
    proof = root / RUNTIME_ROOT / "proof.drat"
    holders = _writable_holders(proof)
    if holders:
        raise RecursiveChildRunnerError(f"stopped proof has writable holders: {holders}")
    record = v2._physical_record(
        proof, root, "raw-binary-drat", cap=loaded["policy"]["proof_max_bytes"],
    )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-stopped-proof-snapshot-v1",
        "transport_state": state,
        "controller_status_sha256": recursive.canonical_sha256(status),
        "latest_generation": latest.get("generation"),
        "latest_pid": latest.get("pid"),
        "latest_proc_start_ticks": latest.get("proc_start_ticks"),
        "latest_pid_identity_alive": False,
        "proof": record,
        "writable_holders": [],
    }, "snapshot_sha256")


def _checker(
    root: Path, loaded: Mapping[str, Any], *, role: str, proof_path: Path,
    proof_record: Mapping[str, Any], proof_cap: int, output_fd: int | None = None,
) -> tuple[dict[str, Any], bytes, bytes, dict[str, Any]]:
    child = loaded["static"]["child"]
    cube = {
        "cube_dimacs_sha256": child["child_dimacs_sha256"],
        "cube_dimacs_bytes": child["child_dimacs_bytes"],
    }
    if role in {"drat-verify", "drat-to-lrat", "final-drat-replay"}:
        checker_path, checker_sha, marker = DRAT_CHECKER, EXPECTED_DRAT_SHA256, b"s VERIFIED"
    elif role in {"lrat-check", "final-lrat-replay"}:
        checker_path, checker_sha, marker = LRAT_CHECKER, EXPECTED_LRAT_SHA256, b"c VERIFIED"
    else:
        raise RecursiveChildRunnerError("unknown proof checker role")
    return proof_helper._run_checker(
        target=root, cube=cube, role=role, checker_path=checker_path,
        checker_sha256=checker_sha, proof_path=proof_path, proof_record=proof_record,
        proof_cap=proof_cap, marker=marker, output_fd=output_fd,
    )


def _copy_proof(source: Path, destination: Path, *, root: Path, expected: Mapping[str, Any], cap: int) -> dict[str, Any]:
    source_fd = os.open(source, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    output_fd = -1
    try:
        before = os.fstat(source_fd)
        if not stat.S_ISREG(before.st_mode) or before.st_size != expected.get("bytes") or before.st_size > cap:
            raise RecursiveChildRunnerError("stopped DRAT source is invalid")
        output_fd = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source_fd, HASH_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise RecursiveChildRunnerError("DRAT artifact exceeds cap")
            digest.update(chunk)
            _write_all(output_fd, chunk)
        os.fsync(output_fd)
        after = os.fstat(source_fd)
        if _identity(before) != _identity(after) or total != expected.get("bytes") or digest.hexdigest() != expected.get("file_sha256"):
            raise RecursiveChildRunnerError("DRAT source changed while copied")
    finally:
        os.close(source_fd)
        if output_fd >= 0:
            os.close(output_fd)
    return v2._physical_record(destination, root, "raw-binary-drat", cap=cap)


def _new_attempt(root: Path) -> Path:
    parent = root / "artifacts"
    attempt = parent / f"attempt-{uuid.uuid4().hex}"
    os.mkdir(attempt, 0o700)
    _fsync_dir(parent)
    return attempt


def _generate_lrat(
    root: Path, loaded: Mapping[str, Any], *, raw_path: Path,
    raw_record: Mapping[str, Any], attempt: Path,
) -> tuple[dict[str, Any], dict[str, Any], bytes, bytes, dict[str, Any]]:
    name = "child.lrat"
    fd, private = v2._create_private_output(attempt, name)
    try:
        conversion, stdout, stderr, bound = _checker(
            root, loaded, role="drat-to-lrat", proof_path=raw_path,
            proof_record=raw_record, proof_cap=loaded["policy"]["proof_max_bytes"], output_fd=fd,
        )
        os.fsync(fd)
        digest, size, _ = v2._hash_fd_stable(fd, cap=MAX_PROOF_BYTES)
        if conversion.get("verified") is not True or not 0 < size <= MAX_PROOF_BYTES:
            raise RecursiveChildRunnerError("DRAT-to-LRAT conversion failed")
        v2._publish_private_output(
            attempt, private, fd, name, expected_sha256=digest, expected_bytes=size,
        )
        fd = -1
    finally:
        if fd >= 0:
            v2._discard_private(attempt, private, fd)
    lrat_path = attempt / name
    lrat_record = v2._physical_record(lrat_path, root, "converted-lrat", cap=MAX_PROOF_BYTES)
    return conversion, lrat_record, stdout, stderr, bound


def _proof_chain_value(
    *, raw: Mapping[str, Any], lrat: Mapping[str, Any], drat_check: Mapping[str, Any],
    conversion: Mapping[str, Any], lrat_check: Mapping[str, Any],
    fresh_drat: Mapping[str, Any], fresh_lrat: Mapping[str, Any], snapshot: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-child-proof-chain-v1",
        "raw_drat": dict(raw), "converted_lrat": dict(lrat),
        "drat_check_sha256": drat_check["record_sha256"],
        "conversion_sha256": conversion["record_sha256"],
        "lrat_check_sha256": lrat_check["record_sha256"],
        "fresh_drat_sha256": fresh_drat["record_sha256"],
        "fresh_lrat_sha256": fresh_lrat["record_sha256"],
        "stopped_snapshot_sha256": snapshot["snapshot_sha256"],
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
    }, "chain_sha256")


def _terminal_claim_value(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
    *, snapshot: Mapping[str, Any], chain: Mapping[str, Any],
) -> dict[str, Any]:
    child = loaded["static"]["child"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": TERMINAL_CLAIM_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "static_sha256": loaded["static"]["static_sha256"],
        "session_sha256": session["record_sha256"],
        "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
        "leaf_id": child["leaf_id"], "leaf_sha256": child["leaf_sha256"],
        "child_cnf_sha256": child["child_cnf_sha256"],
        "child_dimacs_sha256": child["child_dimacs_sha256"],
        "snapshot": dict(snapshot), "proof_chain": dict(chain),
        "terminal": True, "hardness_only": False, "solver_terminal_claim": True,
    }, "terminal_claim_sha256")


def _certificate_value(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
    claim: Mapping[str, Any],
) -> dict[str, Any]:
    child = loaded["static"]["child"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CERTIFICATE_KIND,
        "gate": GATE,
        "root": str(root),
        "static_sha256": loaded["static"]["static_sha256"],
        "session_sha256": session["record_sha256"],
        "parent_audit_sha256": loaded["audit"]["audit_sha256"],
        "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
        "leaf_id": child["leaf_id"], "leaf_sha256": child["leaf_sha256"],
        "child_cnf_sha256": child["child_cnf_sha256"],
        "child_dimacs_sha256": child["child_dimacs_sha256"],
        "child_num_variables": child["child_num_variables"],
        "child_num_clauses": child["child_num_clauses"],
        "child_dimacs_bytes": child["child_dimacs_bytes"],
        "terminal_claim_sha256": claim["terminal_claim_sha256"],
        "proof_chain": claim["proof_chain"],
        "valid": True, "strict_proof_unsat": True,
        "proof_replay_complete": True, "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "hardness_only": False, "solver_terminal_claim": True,
        "transport_authority": "TEST_ONLY",
        "transport_trusted_for_scientific_proof": False,
        "global_distance_claim": None, "publication_certificate": False,
        "upload_authorized": False,
    }, "certificate_sha256")


def _validation_value(root: Path, certificate: Mapping[str, Any]) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": VALIDATION_KIND,
        "gate": GATE,
        "root": str(root),
        "certificate": dict(certificate),
        "certificate_sha256": certificate["certificate_sha256"],
        "valid": True, "strict_proof_unsat": True,
        "fresh_proof_replay": True, "source_toolchain_fresh": True,
        "failures": [], "global_distance_claim": None,
        "publication_certificate": False, "upload_authorized": False,
    }, "validation_sha256")


def _final_value(root: Path, loaded: Mapping[str, Any], claim: Mapping[str, Any], certificate: Mapping[str, Any], validation: Mapping[str, Any]) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": FINAL_KIND,
        "gate": GATE,
        "root": str(root),
        "static_sha256": loaded["static"]["static_sha256"],
        "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
        "terminal_claim_sha256": claim["terminal_claim_sha256"],
        "certificate_sha256": certificate["certificate_sha256"],
        "validation_sha256": validation["validation_sha256"],
        "strict_proof_unsat": True, "proof_replay_complete": True,
        "fresh_proof_replay": True, "hardness_only": False,
        "solver_terminal_claim": True, "global_distance_claim": None,
        "publication_certificate": False, "upload_authorized": False,
    }, "final_sha256")


def _preflight_value(root: Path, snapshot: Mapping[str, Any], checker: Mapping[str, Any], stdout: bytes, stderr: bytes) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-child-stopped-drat-preflight-v1",
        "root": str(root), "snapshot_sha256": snapshot["snapshot_sha256"],
        "checker": dict(checker),
        "checker_stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "checker_stderr_sha256": hashlib.sha256(stderr).hexdigest(),
        "drat_verified": checker.get("verified") is True,
        "terminal_claim_created": False,
        "resumable": snapshot["transport_state"] == "CHECKPOINTED",
        "hardness_only": True,
    }, "record_sha256")


def _require_snapshot_unchanged(before: Mapping[str, Any], after: Mapping[str, Any]) -> None:
    for key in ("transport_state", "latest_generation", "latest_pid", "latest_proc_start_ticks", "proof", "writable_holders"):
        if not _same(before.get(key), after.get(key)):
            raise RecursiveChildRunnerError("stopped transport changed during proof verification")


def _read_terminal_claim(root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    value = _read_json(root / TERMINAL_CLAIM)
    required = {
        "schema_version", "kind", "gate", "root", "root_identity", "static_sha256",
        "session_sha256", "split_manifest_sha256", "leaf_id", "leaf_sha256",
        "child_cnf_sha256", "child_dimacs_sha256", "snapshot", "proof_chain",
        "terminal", "hardness_only", "solver_terminal_claim", "terminal_claim_sha256",
    }
    child = loaded["static"]["child"]
    if (
        set(value) != required or not recursive.selfhash_valid(value, "terminal_claim_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != TERMINAL_CLAIM_KIND
        or value.get("gate") != GATE or value.get("root") != str(root)
        or not _same(value.get("root_identity"), _root_identity(root))
        or value.get("static_sha256") != loaded["static"]["static_sha256"]
        or value.get("session_sha256") != session["record_sha256"]
        or value.get("split_manifest_sha256") != loaded["manifest"]["manifest_sha256"]
        or value.get("leaf_id") != child["leaf_id"] or value.get("leaf_sha256") != child["leaf_sha256"]
        or value.get("child_cnf_sha256") != child["child_cnf_sha256"]
        or value.get("child_dimacs_sha256") != child["child_dimacs_sha256"]
        or value.get("terminal") is not True or value.get("hardness_only") is not False
        or value.get("solver_terminal_claim") is not True
        or type(value.get("snapshot")) is not dict or type(value.get("proof_chain")) is not dict
    ):
        raise RecursiveChildRunnerError("recursive terminal claim is malformed")
    return value


def _claim_artifact_path(root: Path, record: Mapping[str, Any]) -> Path:
    relative = record.get("relative_path")
    if type(relative) is not str or not relative:
        raise RecursiveChildRunnerError("terminal proof artifact has no relative path")
    path = Path(relative)
    if (
        path.is_absolute() or path.as_posix() != relative or not path.parts
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise RecursiveChildRunnerError("terminal proof artifact path is unsafe")
    target = root / path
    try:
        root_real = root.resolve(strict=True)
        target_real = target.resolve(strict=True)
        target_real.relative_to(root_real)
    except (OSError, RuntimeError, ValueError) as exc:
        raise RecursiveChildRunnerError("terminal proof artifact escapes child root") from exc
    if target_real != target:
        raise RecursiveChildRunnerError("terminal proof artifact path is not a direct owned path")
    return target


def _bound_claim_artifact(
    root: Path, record: Any, *, role: str, cap: int,
) -> tuple[Path, dict[str, Any]]:
    if (
        not isinstance(record, dict) or set(record) != PHYSICAL_RECORD_FIELDS
        or record.get("role") != role
        or type(record.get("relative_path")) is not str
        or not recursive.is_sha256(record.get("file_sha256"))
        or type(record.get("bytes")) is not int or not 0 < record["bytes"] <= cap
        or any(type(record.get(key)) is not int for key in ("mode", "device", "inode", "links"))
        or record["links"] < 1
    ):
        raise RecursiveChildRunnerError("terminal proof artifact record is malformed")
    path = _claim_artifact_path(root, record)
    current = v2._physical_record(path, root, role, cap=cap)
    if not _same(current, record):
        raise RecursiveChildRunnerError("terminal proof artifact binding changed")
    return path, current


def _validate_terminal_claim_shape(claim: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    snapshot = claim["snapshot"]
    chain = claim["proof_chain"]
    snapshot_fields = {
        "schema_version", "kind", "transport_state", "controller_status_sha256",
        "latest_generation", "latest_pid", "latest_proc_start_ticks",
        "latest_pid_identity_alive", "proof", "writable_holders", "snapshot_sha256",
    }
    chain_fields = {
        "schema_version", "kind", "raw_drat", "converted_lrat", "drat_check_sha256",
        "conversion_sha256", "lrat_check_sha256", "fresh_drat_sha256", "fresh_lrat_sha256",
        "stopped_snapshot_sha256", "drat_independently_verified",
        "lrat_independently_verified", "fresh_drat_replay", "fresh_lrat_replay", "chain_sha256",
    }
    if (
        not isinstance(snapshot, dict) or set(snapshot) != snapshot_fields
        or not recursive.selfhash_valid(snapshot, "snapshot_sha256")
        or snapshot.get("schema_version") != SCHEMA_VERSION
        or snapshot.get("kind") != "paper400-dic5-recursive-stopped-proof-snapshot-v1"
        or snapshot.get("transport_state") not in {"CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"}
        or not recursive.is_sha256(snapshot.get("controller_status_sha256"))
        or type(snapshot.get("latest_generation")) is not int or snapshot["latest_generation"] < 0
        or type(snapshot.get("latest_pid")) is not int or snapshot["latest_pid"] <= 0
        or type(snapshot.get("latest_proc_start_ticks")) is not int
        or snapshot["latest_proc_start_ticks"] < 0
        or snapshot.get("latest_pid_identity_alive") is not False
        or not isinstance(snapshot.get("proof"), dict)
        or snapshot.get("writable_holders") != []
        or not isinstance(chain, dict) or set(chain) != chain_fields
        or not recursive.selfhash_valid(chain, "chain_sha256")
        or chain.get("schema_version") != SCHEMA_VERSION
        or chain.get("kind") != "paper400-dic5-recursive-child-proof-chain-v1"
        or chain.get("stopped_snapshot_sha256") != snapshot["snapshot_sha256"]
        or any(
            not recursive.is_sha256(chain.get(key))
            for key in (
                "drat_check_sha256", "conversion_sha256", "lrat_check_sha256",
                "fresh_drat_sha256", "fresh_lrat_sha256", "stopped_snapshot_sha256",
            )
        )
        or any(
            chain.get(key) is not True
            for key in (
                "drat_independently_verified", "lrat_independently_verified",
                "fresh_drat_replay", "fresh_lrat_replay",
            )
        )
    ):
        raise RecursiveChildRunnerError("terminal proof claim evidence is malformed")
    return snapshot, chain


def _revalidate_terminal_claim(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any], claim: Mapping[str, Any],
    *, require_stopped_snapshot: bool, fresh_replay: bool,
) -> dict[str, Any]:
    """Bind a persisted terminal claim to still-quiescent proof evidence.

    The claim is immutable, but a crash can leave it present before the
    certificate/commit files.  Recovery must not merely trust its historical
    hashes: it compares the stopped transport snapshot and both copied proof
    artifacts again, then independently replays DRAT and LRAT before sealing.
    """

    snapshot, chain = _validate_terminal_claim_shape(claim)
    if require_stopped_snapshot:
        current_snapshot = _stopped_snapshot(root, loaded, session)
        if not _same(current_snapshot, snapshot):
            raise RecursiveChildRunnerError("stopped transport changed after terminal claim")
    raw_path, raw = _bound_claim_artifact(
        root, chain.get("raw_drat"), role="raw-binary-drat",
        cap=loaded["policy"]["proof_max_bytes"],
    )
    lrat_path, lrat = _bound_claim_artifact(
        root, chain.get("converted_lrat"), role="converted-lrat", cap=MAX_PROOF_BYTES,
    )
    result: dict[str, Any] = {
        "raw_path": raw_path, "raw": raw, "lrat_path": lrat, "lrat": lrat,
    }
    if fresh_replay:
        fresh_drat, _out_a, _err_a, _bound_a = _checker(
            root, loaded, role="final-drat-replay", proof_path=raw_path,
            proof_record=raw, proof_cap=loaded["policy"]["proof_max_bytes"],
        )
        fresh_lrat, _out_b, _err_b, _bound_b = _checker(
            root, loaded, role="final-lrat-replay", proof_path=lrat_path,
            proof_record=lrat, proof_cap=MAX_PROOF_BYTES,
        )
        if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
            raise RecursiveChildRunnerError("fresh terminal proof replay failed")
        result["fresh_drat"] = fresh_drat
        result["fresh_lrat"] = fresh_lrat
    return result


def _complete_terminal(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any], claim: Mapping[str, Any],
    *, recovering: bool = False,
) -> dict[str, Any]:
    """Seal/recover certificate files after a fully evidence-carrying claim."""

    if recovering:
        _revalidate_terminal_claim(
            root, loaded, session, claim,
            require_stopped_snapshot=True, fresh_replay=True,
        )

    certificate_path = root / CERTIFICATE
    validation_path = root / VALIDATION
    final_path = root / FINAL_COMMIT
    if certificate_path.exists():
        certificate = _read_json(certificate_path)
        if not recursive.selfhash_valid(certificate, "certificate_sha256"):
            raise RecursiveChildRunnerError("existing recursive certificate is malformed")
    else:
        certificate = _certificate_value(root, loaded, session, claim)
        _publish_json(certificate_path, certificate)
    expected = _certificate_value(root, loaded, session, claim)
    if not _same(certificate, expected):
        raise RecursiveChildRunnerError("existing recursive certificate does not bind terminal claim")
    if validation_path.exists():
        validation = _read_json(validation_path)
        if not recursive.selfhash_valid(validation, "validation_sha256"):
            raise RecursiveChildRunnerError("existing recursive validation is malformed")
    else:
        validation = _validation_value(root, certificate)
        _publish_json(validation_path, validation)
    expected_validation = _validation_value(root, certificate)
    if not _same(validation, expected_validation):
        raise RecursiveChildRunnerError("existing recursive validation does not bind certificate")
    expected_final = _final_value(root, loaded, claim, certificate, validation)
    if final_path.exists():
        final = _read_json(final_path)
        if not _same(final, expected_final):
            raise RecursiveChildRunnerError("existing recursive final commit is malformed")
        return final
    _publish_json(final_path, expected_final)
    return expected_final


def harvest_stopped_root(root: Path) -> dict[str, Any]:
    """Certify a quiescent child only after DRAT/LRAT and fresh replay checks."""

    target = _safe_root(root)
    with _root_lock(target):
        loaded = _load_static(target)
        session = _load_session(target, loaded)
        if (target / FINAL_COMMIT).exists():
            return _complete_terminal(
                target, loaded, session, _read_terminal_claim(target, loaded, session),
                recovering=True,
            )
        if (target / TERMINAL_CLAIM).exists():
            # This is an intentional crash-recovery path: no solver is
            # resumed.  The immutable claim is re-bound to a still-stopped
            # transport and freshly replayed proof artifacts before any
            # certificate or final commit is published.
            return _complete_terminal(
                target, loaded, session, _read_terminal_claim(target, loaded, session),
                recovering=True,
            )
        snapshot = _stopped_snapshot(target, loaded, session)
        direct = snapshot["proof"]
        if direct["bytes"] <= 0:
            return seal({
                "schema_version": SCHEMA_VERSION,
                "kind": "paper400-dic5-recursive-child-stopped-drat-preflight-v1",
                "root": str(target), "snapshot_sha256": snapshot["snapshot_sha256"],
                "drat_verified": False, "terminal_claim_created": False,
                "resumable": snapshot["transport_state"] == "CHECKPOINTED",
                "hardness_only": True, "failure": "stopped DRAT source is empty",
            }, "record_sha256")
        drat, drat_out, drat_err, _bound = _checker(
            target, loaded, role="drat-verify", proof_path=target / RUNTIME_ROOT / "proof.drat",
            proof_record=direct, proof_cap=loaded["policy"]["proof_max_bytes"],
        )
        if drat.get("verified") is not True:
            return _preflight_value(target, snapshot, drat, drat_out, drat_err)
        after_drat = _stopped_snapshot(target, loaded, session)
        _require_snapshot_unchanged(snapshot, after_drat)
        attempt = _new_attempt(target)
        raw_path = attempt / "child.drat"
        raw = _copy_proof(
            target / RUNTIME_ROOT / "proof.drat", raw_path, root=target,
            expected=direct, cap=loaded["policy"]["proof_max_bytes"],
        )
        conversion, lrat, _conversion_out, _conversion_err, _conversion_bound = _generate_lrat(
            target, loaded, raw_path=raw_path, raw_record=raw, attempt=attempt,
        )
        lrat_path = target / lrat["relative_path"]
        lrat_check, _lrat_out, _lrat_err, _lrat_bound = _checker(
            target, loaded, role="lrat-check", proof_path=lrat_path,
            proof_record=lrat, proof_cap=MAX_PROOF_BYTES,
        )
        if lrat_check.get("verified") is not True:
            raise RecursiveChildRunnerError("converted LRAT verification failed")
        fresh_drat, _fresh_drat_out, _fresh_drat_err, _fresh_drat_bound = _checker(
            target, loaded, role="final-drat-replay", proof_path=raw_path,
            proof_record=raw, proof_cap=loaded["policy"]["proof_max_bytes"],
        )
        fresh_lrat, _fresh_lrat_out, _fresh_lrat_err, _fresh_lrat_bound = _checker(
            target, loaded, role="final-lrat-replay", proof_path=lrat_path,
            proof_record=lrat, proof_cap=MAX_PROOF_BYTES,
        )
        if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
            raise RecursiveChildRunnerError("fresh DRAT/LRAT replay failed")
        after_all = _stopped_snapshot(target, loaded, session)
        _require_snapshot_unchanged(snapshot, after_all)
        # Replay immutable static/source/tool inputs one final time before
        # terminal sealing.  This does not assign scientific authority to
        # DMTCP; the proof artifacts and fresh checkers do that work.
        final_loaded = _load_static(target)
        final_session = _load_session(target, final_loaded)
        if (
            final_loaded["static"]["static_sha256"] != loaded["static"]["static_sha256"]
            or final_session["record_sha256"] != session["record_sha256"]
        ):
            raise RecursiveChildRunnerError("static/session binding changed before terminal claim")
        chain = _proof_chain_value(
            raw=raw, lrat=lrat, drat_check=drat, conversion=conversion,
            lrat_check=lrat_check, fresh_drat=fresh_drat, fresh_lrat=fresh_lrat,
            snapshot=snapshot,
        )
        claim = _terminal_claim_value(target, final_loaded, final_session, snapshot=snapshot, chain=chain)
        _publish_json(target / TERMINAL_CLAIM, claim)
        return _complete_terminal(target, final_loaded, final_session, claim)


def _validated_certificate(root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    claim = _read_terminal_claim(root, loaded, session)
    certificate = _read_json(root / CERTIFICATE)
    validation = _read_json(root / VALIDATION)
    expected_certificate = _certificate_value(root, loaded, session, claim)
    if not _same(certificate, expected_certificate):
        raise RecursiveChildRunnerError("certificate does not replay terminal claim")
    expected_validation = _validation_value(root, certificate)
    if not _same(validation, expected_validation):
        raise RecursiveChildRunnerError("validation does not replay certificate")
    expected_final = _final_value(root, loaded, claim, certificate, validation)
    final = _read_json(root / FINAL_COMMIT)
    if not _same(final, expected_final):
        raise RecursiveChildRunnerError("final commit does not replay recursive evidence")
    return claim, certificate, validation


def verify_final_root(root: Path) -> dict[str, Any]:
    """Freshly replay both final proof artifacts without mutating the root."""

    target = _safe_root(root)
    with _root_lock(target, exclusive=False):
        loaded = _load_static(target)
        session = _load_session(target, loaded)
        claim, certificate, _validation = _validated_certificate(target, loaded, session)
        replay = _revalidate_terminal_claim(
            target, loaded, session, claim,
            require_stopped_snapshot=True, fresh_replay=True,
        )
        fresh_drat = replay["fresh_drat"]
        fresh_lrat = replay["fresh_lrat"]
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-child-fresh-final-validation-v1",
            "root": str(target),
            "certificate": certificate,
            "certificate_sha256": certificate["certificate_sha256"],
            "validation_sha256": _validation["validation_sha256"],
            "fresh_drat": fresh_drat, "fresh_lrat": fresh_lrat,
            "valid": True, "strict_proof_unsat": True,
            "fresh_proof_replay": True, "source_toolchain_fresh": True,
            "failures": [], "global_distance_claim": None,
            "publication_certificate": False, "upload_authorized": False,
        }, "validation_sha256")


def status_root(root: Path, *, verify_hashes: bool = False) -> dict[str, Any]:
    target = _safe_root(root)
    with _root_lock(target, exclusive=False):
        loaded = _load_static(target)
        if not (target / SESSION_COMMIT).exists():
            if (target / FINAL_COMMIT).exists() or (target / TERMINAL_CLAIM).exists():
                raise RecursiveChildRunnerError("terminal recursive child has no sealed session")
            if (target / START_CLAIM).exists():
                claim = _read_start_claim(target, loaded)
                return seal({
                    "schema_version": SCHEMA_VERSION,
                    "kind": "paper400-dic5-recursive-child-status-v1",
                    "root": str(target), "state": "START_RECOVERY_REQUIRED", "terminal": False,
                    "static_sha256": loaded["static"]["static_sha256"],
                    "start_claim_sha256": claim["record_sha256"],
                    "expected_single_cpu": claim["expected_single_cpu"],
                }, "record_sha256")
            if (target / RUNTIME_ROOT).exists() or (target / RUNTIME_ROOT).is_symlink():
                raise RecursiveChildRunnerError("unclaimed recursive child transport is unresolved")
            return seal({
                "schema_version": SCHEMA_VERSION,
                "kind": "paper400-dic5-recursive-child-status-v1",
                "root": str(target), "state": "PREPARED", "terminal": False,
                "static_sha256": loaded["static"]["static_sha256"],
            }, "record_sha256")
        session = _load_session(target, loaded)
        if (target / FINAL_COMMIT).exists():
            _validated_certificate(target, loaded, session)
            state = "PROOF_CARRYING_CHILD_UNSAT"
            terminal = True
            controller_status: dict[str, Any] | None = None
        else:
            controller_status = _controller_status(target, loaded, session, verify_hashes=verify_hashes)
            state = controller_status["state"]
            terminal = (target / TERMINAL_CLAIM).exists()
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-child-status-v1",
            "root": str(target), "state": state, "terminal": terminal,
            "static_sha256": loaded["static"]["static_sha256"],
            "session_sha256": session["record_sha256"],
            "controller_status": controller_status,
        }, "record_sha256")


def _read_cli_json(path: Path) -> dict[str, Any]:
    return _read_json(Path(path))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    prepare = sub.add_parser("prepare", allow_abbrev=False)
    prepare.add_argument("--root", type=Path, required=True)
    prepare.add_argument("--parent-cnf", type=Path, required=True)
    prepare.add_argument("--split-manifest", type=Path, required=True)
    prepare.add_argument("--parent-audit", type=Path, required=True)
    prepare.add_argument("--leaf-path", required=True)
    prepare.add_argument("--proof-max-bytes", type=int, default=DEFAULT_PROOF_MAX_BYTES)
    prepare.add_argument("--checkpoint-image-max-bytes", type=int, default=DEFAULT_CHECKPOINT_IMAGE_MAX_BYTES)
    prepare.add_argument("--checkpoint-generation-max", type=int, default=DEFAULT_CHECKPOINT_GENERATION_MAX)
    start = sub.add_parser("start", allow_abbrev=False)
    start.add_argument("--root", type=Path, required=True)
    start.add_argument("--cpu", type=int, required=True)
    for action in ("checkpoint-stop", "resume", "harvest", "verify-final", "status"):
        command = sub.add_parser(action, allow_abbrev=False)
        command.add_argument("--root", type=Path, required=True)
    parser.add_argument("--version", action="version", version=GATE)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "prepare":
        parent_payload = _stable_bytes(args.parent_cnf, cap=MAX_DIMACS_BYTES, executable=False)
        result = prepare_root_from_material(
            args.root, parent_dimacs=parent_payload,
            split_manifest=_read_cli_json(args.split_manifest), leaf_path=args.leaf_path,
            parent_audit=_read_cli_json(args.parent_audit),
            proof_max_bytes=args.proof_max_bytes,
            checkpoint_image_max_bytes=args.checkpoint_image_max_bytes,
            checkpoint_generation_max=args.checkpoint_generation_max,
        )
    elif args.action == "start":
        result = start_root(args.root, cpu=args.cpu)
    elif args.action == "checkpoint-stop":
        result = checkpoint_stop_root(args.root)
    elif args.action == "resume":
        result = resume_root(args.root)
    elif args.action == "harvest":
        result = harvest_stopped_root(args.root)
    elif args.action == "verify-final":
        result = verify_final_root(args.root)
    elif args.action == "status":
        result = status_root(args.root)
    else:  # pragma: no cover - argparse makes this unreachable.
        raise RecursiveChildRunnerError("unknown action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        RecursiveChildRunnerError, recursive.RecursiveSplitError,
        controller.ResumeControllerError, proof_helper.CubeProofRunnerError,
        OSError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
