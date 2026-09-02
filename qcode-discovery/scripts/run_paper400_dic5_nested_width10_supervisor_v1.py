#!/usr/bin/env python3
"""Crash-safe host supervisor for the paper400 width-ten batch campaign.

The four-lane coordinator remains the only component that mutates leaf roots.
This module only schedules its public commands, observes durable process
identities, and keeps a bounded set of CPUs occupied.  A low-disk pause always
checkpoint-stops live lanes and never starts, resumes, or harvests more work.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import datetime as _datetime
import fcntl
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from scripts import run_paper400_dic5_nested_width10_four_lane_v1 as four_lane


child = four_lane.child_runner

SCHEMA_VERSION = 1
KIND = "paper400-dic5-nested-width10-host-supervisor-v1"
STATUS_KIND = "paper400-dic5-nested-width10-host-status-v1"
PAUSE_KIND = "paper400-dic5-nested-width10-low-disk-pause-v1"
CONTROL_DIR_PREFIX = ".paper400-supervisor-v1-"
CONFIG_NAME = "config.json"
LOCK_NAME = "supervisor.lock"
STATUS_NAME = "status.json"
PAUSE_NAME = "low-disk-pause.json"
LOG_DIR_NAME = "logs"
LANES_PER_BATCH = four_lane.LANES_PER_BATCH
MAX_JSON_BYTES = 64 << 20
DEFAULT_STOP_FREE_BYTES = 5 << 40
DEFAULT_RESUME_FREE_BYTES = 6 << 40
DEFAULT_POLL_SECONDS = 60
DEFAULT_ACTION_WORKERS = 8
TAG_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$")

INPUT_HASHES = {
    "parent_manifest": (
        "parent-manifest.json",
        "2c5b188a6d7417fd2f56694c6da990ac0221adeb34f2417f5384925d7bb6debb",
    ),
    "width6_campaign": (
        "width6-campaign.json",
        "887371a9c9839edf268e86901050ccf31ddd13d97788c03cc63158bcafb35c0b",
    ),
    "width10_campaign": (
        "width10-campaign.json",
        "d416c6515156b443f128f36ca885dd8ee855726fe71a990097e71be7a3a12569",
    ),
}

TOOL_FILES = {
    "cadical": (
        Path("/home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical"),
        "6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21",
        True,
    ),
    "cadical_audit": (
        Path(
            "/home/jing/paper400-toolchain/audit/"
            "standalone-audit-manifest.json"
        ),
        "e274b8e5ab4e9456096243ad5ce3a3a8248374590a0ebf49ce36653357294e6a",
        False,
    ),
    "dmtcp_launch": (
        Path("/home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_launch"),
        "2036e98a96ca701425a4d47d86b82d0b4657cf39cbac90cd22770dc9d65480ab",
        True,
    ),
    "dmtcp_command": (
        Path("/home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_command"),
        "aa4eebcbdaa62abde9af5e849f93423de22ce4415871c678095613598d3c4c98",
        True,
    ),
    "dmtcp_restart": (
        Path("/home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_restart"),
        "b1e72dd345660cdcb3688accb4888542df3c8d1ed97e08ebbbfc46e783da32ae",
        True,
    ),
    "dmtcp_coordinator": (
        Path("/home/jing/paper400-toolchain/dmtcp-4.2.0/bin/dmtcp_coordinator"),
        "ed76910fe215c1507ca08814a4e2f94943b44027a7410f1aa5eb17f5b6ff8e77",
        True,
    ),
    "mtcp_restart": (
        Path("/home/jing/paper400-toolchain/dmtcp-4.2.0/bin/mtcp_restart"),
        "acfb3108fd9e42cf59ebfbb2f1a59e6a2df9b066ed73f1abd97d852a2467da69",
        True,
    ),
    "drat_trim": (
        Path("/home/jing/paper400-toolchain/proof-checkers/bin/drat-trim"),
        "8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394",
        True,
    ),
    "lrat_check": (
        Path("/home/jing/paper400-toolchain/proof-checkers/bin/lrat-check"),
        "c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79",
        True,
    ),
    "trusted_checker_policy": (
        Path("/home/jing/paper400-toolchain/audit/trusted-checker-policy.json"),
        "af3a2089ebf0df9b1120e1cfd3164cc6a2e9bf07bb35c057f3f85890d0f854e2",
        False,
    ),
    "science_python": (
        Path(
            "/home/jing/science-mango/qcode-discovery/.venv/bin/python"
        ),
        "f7c6210eb40fadcd3c2889dddd24a15fc2c9f926aec5a03bf9da66e12d581526",
        True,
    ),
}

RESOURCE_DEFAULTS = {
    "proof_max_bytes": 68_719_476_736,
    "checkpoint_image_max_bytes": 17_179_869_184,
    "checkpoint_images_per_generation_max": 1,
    "checkpoint_generation_max_count": 64,
    "checkpoint_generation_metadata_max_bytes": 67_108_864,
}

LANE_STATES = frozenset({
    "PREPARED", "RUNNING", "CHECKPOINTED", "INACTIVE",
    "FINAL", "PRUNE_INCOMPLETE", "PRUNED", "START_INCOMPLETE",
    "TERMINAL_INCOMPLETE", "POISONED",
})
TERMINAL_LANE_STATES = frozenset({"PRUNED"})


class SupervisorError(RuntimeError):
    """The campaign configuration or observed durable state is unsafe."""


def _utc_now() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace(
        "+00:00", "Z"
    )


def _canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise SupervisorError(f"value is not canonical JSON: {exc}") from exc


def _seal(value: Mapping[str, Any]) -> dict[str, Any]:
    if type(value) is not dict or "record_sha256" in value:
        raise SupervisorError("invalid value passed to seal")
    result = dict(value)
    result["record_sha256"] = hashlib.sha256(
        _canonical_bytes(result)
    ).hexdigest()
    return result


def _selfhash_valid(value: Any) -> bool:
    if type(value) is not dict:
        return False
    digest = value.get("record_sha256")
    if type(digest) is not str or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        return False
    unsigned = dict(value)
    unsigned.pop("record_sha256")
    return hashlib.sha256(_canonical_bytes(unsigned)).hexdigest() == digest


def _read_json(path: Path) -> dict[str, Any]:
    target = Path(path)
    try:
        info = target.lstat()
    except OSError as exc:
        raise SupervisorError(f"cannot stat JSON file: {target}") from exc
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise SupervisorError(f"JSON path is not a regular file: {target}")
    if info.st_size > MAX_JSON_BYTES:
        raise SupervisorError(f"JSON file exceeds size cap: {target}")
    try:
        payload = target.read_bytes()
        value = json.loads(payload.decode("ascii"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SupervisorError(f"cannot decode JSON file: {target}") from exc
    if type(value) is not dict or payload != _canonical_bytes(value) + b"\n":
        raise SupervisorError(f"JSON file is not canonical: {target}")
    return value


def _write_once(path: Path, value: Mapping[str, Any]) -> None:
    payload = _canonical_bytes(dict(value)) + b"\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise SupervisorError(f"short write while publishing: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _fsync_directory(path.parent)


def _atomic_replace(path: Path, value: Mapping[str, Any]) -> None:
    payload = _canonical_bytes(dict(value)) + b"\n"
    temporary = path.parent / (
        f".{path.name}.{os.getpid()}.{time.monotonic_ns()}.tmp"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise SupervisorError(f"short write while publishing: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    try:
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _sha256_file(path: Path, *, cap: int = 1 << 30) -> tuple[str, int]:
    target = Path(path)
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise SupervisorError(f"missing required file: {target}") from exc
    if stat.S_ISLNK(lexical.st_mode):
        target = resolved
        lexical = target.lstat()
    if not stat.S_ISREG(lexical.st_mode) or lexical.st_size > cap:
        raise SupervisorError(f"required file is not bounded and regular: {path}")
    descriptor = os.open(target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        digest = hashlib.sha256()
        observed = 0
        while True:
            chunk = os.read(descriptor, 8 << 20)
            if not chunk:
                break
            observed += len(chunk)
            if observed > cap:
                raise SupervisorError(f"required file exceeds cap: {path}")
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_size,
        item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or observed != before.st_size:
        raise SupervisorError(f"required file changed while hashing: {path}")
    return digest.hexdigest(), observed


def _plain_absolute_directory(path: Path, *, owned: bool = True) -> Path:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise SupervisorError(f"directory is not normalized absolute: {target}")
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise SupervisorError(f"directory is unavailable: {target}") from exc
    if (
        resolved != target or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode)
        or (owned and lexical.st_uid != os.geteuid())
    ):
        raise SupervisorError(f"directory is aliased, non-directory, or unowned: {target}")
    return target


def _input_records(input_dir: Path) -> dict[str, Any]:
    root = _plain_absolute_directory(input_dir)
    records: dict[str, Any] = {}
    for role, (name, expected) in INPUT_HASHES.items():
        path = root / name
        digest, size = _sha256_file(path, cap=MAX_JSON_BYTES)
        if digest != expected:
            raise SupervisorError(
                f"authenticated input hash mismatch for {name}: {digest}"
            )
        value = _read_json(path)
        info = path.stat()
        records[role] = {
            "path": str(path),
            "sha256": digest,
            "bytes": size,
            "device": int(info.st_dev),
            "inode": int(info.st_ino),
            "manifest_sha256": value.get("manifest_sha256"),
        }
    return records


def preflight_toolchain() -> dict[str, Any]:
    """Verify every README pin plus the complete DMTCP and ELF closures."""

    files: dict[str, Any] = {}
    failures: list[str] = []
    for role, (path, expected, executable) in TOOL_FILES.items():
        try:
            digest, size = _sha256_file(path)
            if digest != expected:
                raise SupervisorError(
                    f"SHA-256 mismatch: expected {expected}, observed {digest}"
                )
            resolved = path.resolve(strict=True)
            if executable and not os.access(resolved, os.X_OK):
                raise SupervisorError("file is not executable")
            files[role] = {
                "path": str(path), "realpath": str(resolved),
                "sha256": digest, "bytes": size,
            }
        except (OSError, SupervisorError) as exc:
            failures.append(f"{role}: {exc}")
    coordinator_path = Path(four_lane.__file__).resolve()
    try:
        coordinator_sha, _ = _sha256_file(coordinator_path, cap=16 << 20)
        if coordinator_sha != child.EXPECTED_FOUR_LANE_SHA256:
            failures.append("four-lane coordinator source pin mismatch")
    except SupervisorError as exc:
        failures.append(f"four-lane coordinator: {exc}")
    if not failures:
        try:
            child.controller.build_dmtcp_binding(child.DMTCP_PREFIX)
        except Exception as exc:
            failures.append(f"DMTCP prefix replay failed: {type(exc).__name__}: {exc}")
        try:
            child.v2._toolchain_binding()
        except Exception as exc:
            failures.append(f"proof toolchain replay failed: {type(exc).__name__}: {exc}")
        try:
            child.v2._python_binding()
        except Exception as exc:
            failures.append(f"science Python replay failed: {type(exc).__name__}: {exc}")
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-nested-width10-host-preflight-v1",
        "valid": not failures,
        "failures": failures,
        "files": files,
        "four_lane_coordinator_sha256": (
            coordinator_sha if "coordinator_sha" in locals() else None
        ),
    })


def _validate_cpus(values: Iterable[int]) -> list[int]:
    cpus = list(values)
    allowed = os.sched_getaffinity(0)
    if (
        not cpus or len(cpus) % LANES_PER_BATCH
        or len(set(cpus)) != len(cpus)
        or any(type(cpu) is not int or cpu not in allowed for cpu in cpus)
    ):
        raise SupervisorError(
            "CPUs must be distinct allowed integers in a non-empty multiple of four"
        )
    return cpus


def _config_value(
    *, control_root: Path, run_parent: Path, input_dir: Path, tag: str,
    batch_first: int, batch_last: int, cpus: Sequence[int],
    stop_free_bytes: int, resume_free_bytes: int, poll_seconds: int,
    action_workers: int, resource_caps: Mapping[str, int],
) -> dict[str, Any]:
    if not TAG_RE.fullmatch(tag):
        raise SupervisorError("tag must contain only letters, digits, dot, dash, underscore")
    if not (0 <= batch_first <= batch_last < four_lane.BATCH_COUNT):
        raise SupervisorError("batch range is outside 0..255")
    if (
        type(stop_free_bytes) is not int or stop_free_bytes <= 0
        or type(resume_free_bytes) is not int
        or resume_free_bytes <= stop_free_bytes
    ):
        raise SupervisorError("disk resume threshold must exceed a positive stop threshold")
    if type(poll_seconds) is not int or poll_seconds < 1:
        raise SupervisorError("poll interval must be a positive integer")
    if type(action_workers) is not int or not 1 <= action_workers <= 64:
        raise SupervisorError("action worker count must be in 1..64")
    checked_cpus = _validate_cpus(cpus)
    normalized_caps = four_lane.static_v1.normalize_resource_caps(resource_caps)
    raw_caps = {
        key: normalized_caps[key] for key in four_lane.static_v1.CAP_INPUT_FIELDS
    }
    coordinator_path = Path(four_lane.__file__).resolve()
    coordinator_sha, _ = _sha256_file(coordinator_path, cap=16 << 20)
    if coordinator_sha != child.EXPECTED_FOUR_LANE_SHA256:
        raise SupervisorError("four-lane coordinator source pin mismatch")
    supervisor_path = Path(__file__).resolve()
    supervisor_sha, _ = _sha256_file(supervisor_path, cap=16 << 20)
    python_path = Path(sys.executable)
    python_sha, _ = _sha256_file(python_path, cap=256 << 20)
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "created_utc": _utc_now(),
        "control_root": str(control_root),
        "run_parent": str(run_parent),
        "tag": tag,
        "batch_first": batch_first,
        "batch_last": batch_last,
        "parent_cube_index": 0,
        "cpus": checked_cpus,
        "max_active_lanes": len(checked_cpus),
        "input_files": _input_records(input_dir),
        "resource_caps": raw_caps,
        "disk_policy": {
            "stop_free_bytes": stop_free_bytes,
            "resume_free_bytes": resume_free_bytes,
            "checkpoint_reserve_formula": (
                "stop before free bytes fall below the configured bound; "
                "default bound exceeds 224 times the 16-GiB image cap"
            ),
        },
        "poll_seconds": poll_seconds,
        "action_workers": action_workers,
        "four_lane_coordinator_sha256": coordinator_sha,
        "supervisor_source": {
            "path": str(supervisor_path),
            "sha256": supervisor_sha,
        },
        "python": {
            "invocation_path": str(python_path),
            "realpath": str(python_path.resolve(strict=True)),
            "sha256": python_sha,
        },
        "scheduling_policy": {
            "batch_order": "ascending",
            "lanes_per_batch": LANES_PER_BATCH,
            "reuse_cpu_only_after_transport_pruned": True,
            "harvest_then_fresh_verify_then_prune": True,
            "low_disk_starts_or_resumes": False,
            "low_disk_checkpoint_stops_all_running_lanes": True,
        },
        "scientific_claim": False,
    })


def initialize(
    *, run_parent: Path, input_dir: Path, tag: str, batch_first: int,
    batch_last: int, cpus: Sequence[int], stop_free_bytes: int,
    resume_free_bytes: int, poll_seconds: int, action_workers: int,
    resource_caps: Mapping[str, int],
) -> dict[str, Any]:
    parent = _plain_absolute_directory(run_parent)
    control = parent / f"{CONTROL_DIR_PREFIX}{tag}"
    if os.path.lexists(control):
        raise SupervisorError(f"control root already exists: {control}")
    for batch_index in range(batch_first, batch_last + 1):
        candidate = parent / f"paper400-batch-{batch_index:04d}-{tag}"
        if os.path.lexists(candidate):
            raise SupervisorError(f"batch root predates supervisor config: {candidate}")
    os.mkdir(control, 0o700)
    try:
        os.mkdir(control / LOG_DIR_NAME, 0o700)
        config = _config_value(
            control_root=control, run_parent=parent, input_dir=input_dir,
            tag=tag, batch_first=batch_first, batch_last=batch_last,
            cpus=cpus, stop_free_bytes=stop_free_bytes,
            resume_free_bytes=resume_free_bytes, poll_seconds=poll_seconds,
            action_workers=action_workers, resource_caps=resource_caps,
        )
        _write_once(control / CONFIG_NAME, config)
        descriptor = os.open(
            control / LOCK_NAME,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        os.close(descriptor)
        _fsync_directory(control)
    except BaseException:
        # A failed initialization is intentionally visible and must be inspected.
        raise
    return config


def _load_config(control_root: Path) -> dict[str, Any]:
    root = _plain_absolute_directory(control_root)
    config = _read_json(root / CONFIG_NAME)
    expected_fields = {
        "schema_version", "kind", "created_utc", "control_root", "run_parent",
        "tag", "batch_first", "batch_last", "parent_cube_index", "cpus",
        "max_active_lanes", "input_files", "resource_caps", "disk_policy",
        "poll_seconds", "action_workers", "four_lane_coordinator_sha256",
        "supervisor_source", "python", "scheduling_policy",
        "scientific_claim", "record_sha256",
    }
    if (
        set(config) != expected_fields or not _selfhash_valid(config)
        or config.get("schema_version") != SCHEMA_VERSION
        or config.get("kind") != KIND
        or config.get("control_root") != str(root)
        or config.get("parent_cube_index") != 0
        or config.get("scientific_claim") is not False
    ):
        raise SupervisorError("supervisor config schema/self-hash mismatch")
    run_parent = _plain_absolute_directory(Path(config.get("run_parent", "")))
    if root.parent != run_parent:
        raise SupervisorError("control root is outside its configured run parent")
    if not TAG_RE.fullmatch(config.get("tag", "")):
        raise SupervisorError("configured tag is malformed")
    first, last = config.get("batch_first"), config.get("batch_last")
    if type(first) is not int or type(last) is not int or not 0 <= first <= last < 256:
        raise SupervisorError("configured batch range is malformed")
    cpus = _validate_cpus(config.get("cpus", []))
    if config.get("max_active_lanes") != len(cpus):
        raise SupervisorError("configured CPU count mismatch")
    current_inputs = _input_records(
        Path(config.get("input_files", {}).get("parent_manifest", {}).get("path", "")).parent
    )
    if current_inputs != config.get("input_files"):
        raise SupervisorError("authenticated input identity changed")
    coordinator_sha, _ = _sha256_file(Path(four_lane.__file__).resolve(), cap=16 << 20)
    if (
        coordinator_sha != config.get("four_lane_coordinator_sha256")
        or coordinator_sha != child.EXPECTED_FOUR_LANE_SHA256
    ):
        raise SupervisorError("four-lane coordinator changed after initialization")
    supervisor_binding = config.get("supervisor_source")
    supervisor_path = Path(__file__).resolve()
    supervisor_sha, _ = _sha256_file(supervisor_path, cap=16 << 20)
    if supervisor_binding != {
        "path": str(supervisor_path), "sha256": supervisor_sha,
    }:
        raise SupervisorError("supervisor source changed after initialization")
    python_binding = config.get("python")
    python_path = Path(sys.executable)
    python_sha, _ = _sha256_file(python_path, cap=256 << 20)
    if python_binding != {
        "invocation_path": str(python_path),
        "realpath": str(python_path.resolve(strict=True)),
        "sha256": python_sha,
    }:
        raise SupervisorError("supervisor Python changed after initialization")
    normalized = four_lane.static_v1.normalize_resource_caps(
        config.get("resource_caps", {})
    )
    if any(
        normalized[key] != config["resource_caps"].get(key)
        for key in four_lane.static_v1.CAP_INPUT_FIELDS
    ):
        raise SupervisorError("configured resource caps changed")
    disk = config.get("disk_policy")
    if (
        type(disk) is not dict
        or type(disk.get("stop_free_bytes")) is not int
        or type(disk.get("resume_free_bytes")) is not int
        or disk["stop_free_bytes"] <= 0
        or disk["resume_free_bytes"] <= disk["stop_free_bytes"]
    ):
        raise SupervisorError("configured disk policy is malformed")
    if type(config.get("poll_seconds")) is not int or config["poll_seconds"] < 1:
        raise SupervisorError("configured poll interval is malformed")
    if (
        type(config.get("action_workers")) is not int
        or not 1 <= config["action_workers"] <= 64
    ):
        raise SupervisorError("configured action worker count is malformed")
    if config.get("scheduling_policy") != {
        "batch_order": "ascending",
        "lanes_per_batch": LANES_PER_BATCH,
        "reuse_cpu_only_after_transport_pruned": True,
        "harvest_then_fresh_verify_then_prune": True,
        "low_disk_starts_or_resumes": False,
        "low_disk_checkpoint_stops_all_running_lanes": True,
    }:
        raise SupervisorError("configured scheduling policy is malformed")
    return config


@contextlib.contextmanager
def _supervisor_lock(control_root: Path):
    path = control_root / LOCK_NAME
    descriptor = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise SupervisorError("another supervisor holds the campaign lock") from exc
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _batch_root(config: Mapping[str, Any], batch_index: int) -> Path:
    return Path(config["run_parent"]) / (
        f"paper400-batch-{batch_index:04d}-{config['tag']}"
    )


def _pid_identity(pid: Any, start_ticks: Any) -> bool:
    if type(pid) is not int or type(start_ticks) is not int or pid <= 0:
        return False
    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        close = payload.rfind(")")
        fields = payload[close + 2:].split()
        return close > 0 and len(fields) > 19 and fields[0] != "Z" and int(fields[19]) == start_ticks
    except (OSError, UnicodeDecodeError, ValueError):
        return False


def _controller_manifest(path: Path) -> dict[str, Any]:
    value = _read_json(path)
    if not child.controller.selfhash_valid(value):
        raise SupervisorError(f"controller manifest self-hash mismatch: {path}")
    return value


def _observe_lane(lane_root: Path) -> str:
    if (lane_root / child.TRANSPORT_PRUNE_COMMIT).exists():
        child._read_transport_prune_commit(lane_root)
        return "PRUNED"
    if (lane_root / child.TRANSPORT_PRUNE_CLAIM).exists():
        return "PRUNE_INCOMPLETE"
    if (lane_root / child.FINAL_COMMIT).exists():
        return "FINAL"
    if (lane_root / child.TERMINAL_CLAIM).exists():
        return "TERMINAL_INCOMPLETE"
    if not (lane_root / child.SESSION_COMMIT).exists():
        return (
            "START_INCOMPLETE"
            if (lane_root / child.START_CLAIM).exists() else "PREPARED"
        )
    runtime = lane_root / child.RUNTIME_ROOT
    generations = runtime / "generations"
    if not generations.is_dir() or generations.is_symlink():
        return "POISONED"
    entries = sorted(
        path for path in generations.iterdir()
        if path.is_dir() and not path.is_symlink() and re.fullmatch(r"[0-9]{6}", path.name)
    )
    if not entries:
        return "POISONED"
    latest = entries[-1]
    for claim_name, commit_name in (
        ("start.claim.json", "start.commit.json"),
        ("resume.claim.json", "resume.commit.json"),
        ("checkpoint.claim.json", "checkpoint.commit.json"),
    ):
        if (latest / claim_name).exists() and not (latest / commit_name).exists():
            return "POISONED"
    active_paths = [
        path for path in (latest / "start.commit.json", latest / "resume.commit.json")
        if path.exists()
    ]
    if len(active_paths) != 1:
        return "POISONED"
    active = _controller_manifest(active_paths[0])
    if active.get("generation") != int(latest.name):
        return "POISONED"
    if (latest / "checkpoint.commit.json").exists():
        _controller_manifest(latest / "checkpoint.commit.json")
        return "CHECKPOINTED"
    return (
        "RUNNING"
        if _pid_identity(active.get("pid"), active.get("proc_start_ticks"))
        else "INACTIVE"
    )


def _incomplete_action(root: Path) -> str | None:
    actions = root / four_lane.ACTIONS
    if not actions.is_dir() or actions.is_symlink():
        raise SupervisorError(f"batch actions directory is unavailable: {actions}")
    entries = sorted(actions.iterdir(), key=lambda path: path.name)
    for index, path in enumerate(entries):
        if path.name != f"{index:06d}" or not path.is_dir() or path.is_symlink():
            raise SupervisorError(f"batch action history is malformed: {root}")
        result = path / "result.json"
        if result.exists():
            if index == len(entries) - 1:
                return None
            continue
        if index != len(entries) - 1:
            raise SupervisorError(f"non-final batch action is incomplete: {root}")
        claim_path = path / "claim.json"
        if not claim_path.exists():
            if any(path.iterdir()):
                raise SupervisorError(f"claimless action has residual files: {root}")
            return ""
        claim = _read_json(claim_path)
        action = claim.get("action")
        if action not in four_lane.ACTION_NAMES:
            raise SupervisorError(f"incomplete action name is invalid: {root}")
        return action
    return None


def _observe_batch(config: Mapping[str, Any], batch_index: int) -> dict[str, Any]:
    root = _batch_root(config, batch_index)
    if not os.path.lexists(root):
        return {
            "batch_index": batch_index, "root": str(root), "state": "MISSING",
            "cpus": [], "lanes": [], "incomplete_action": None,
        }
    if root.is_symlink() or not root.is_dir():
        raise SupervisorError(f"batch root is not a plain directory: {root}")
    four_lane._root_identity(root)
    four_lane._lock_identity(root)
    manifest_path = root / four_lane.BATCH_COMMIT
    if not manifest_path.exists():
        raise SupervisorError(f"batch prepare is incomplete and fail-closed: {root}")
    manifest = _read_json(manifest_path)
    if not four_lane.selfhash_valid(manifest):
        raise SupervisorError(f"batch manifest self-hash mismatch: {root}")
    batch = manifest.get("batch")
    cpus = manifest.get("cpu_policy", {}).get("cpus")
    lanes = manifest.get("lanes")
    if (
        manifest.get("root") != str(root)
        or type(batch) is not dict or batch.get("batch_index") != batch_index
        or type(cpus) is not list or len(cpus) != LANES_PER_BATCH
        or any(cpu not in config["cpus"] for cpu in cpus)
        or len(set(cpus)) != LANES_PER_BATCH
        or type(lanes) is not list or len(lanes) != LANES_PER_BATCH
    ):
        raise SupervisorError(f"batch manifest scheduler binding mismatch: {root}")
    observed_lanes = []
    for lane_index, lane in enumerate(lanes):
        lane_root = root / four_lane.LANES / f"lane-{lane_index}"
        if (
            type(lane) is not dict or lane.get("lane_index") != lane_index
            or lane.get("cpu") != cpus[lane_index]
            or lane.get("child_root") != str(lane_root)
        ):
            raise SupervisorError(f"batch lane binding mismatch: {root}")
        state = _observe_lane(lane_root)
        if state not in LANE_STATES:
            raise SupervisorError(f"unknown lane state: {state}")
        observed_lanes.append({
            "lane_index": lane_index,
            "global_leaf_index": lane.get("global_leaf_index"),
            "cpu": lane.get("cpu"),
            "state": state,
        })
    return {
        "batch_index": batch_index,
        "root": str(root),
        "state": "PRESENT",
        "cpus": list(cpus),
        "lanes": observed_lanes,
        "incomplete_action": _incomplete_action(root),
    }


def observe_campaign(config: Mapping[str, Any]) -> list[dict[str, Any]]:
    batches = [
        _observe_batch(config, index)
        for index in range(config["batch_first"], config["batch_last"] + 1)
    ]
    occupied: dict[int, tuple[int, int]] = {}
    for batch in batches:
        for lane in batch["lanes"]:
            if lane["state"] in TERMINAL_LANE_STATES:
                continue
            cpu = lane["cpu"]
            if cpu in occupied:
                raise SupervisorError(
                    f"CPU {cpu} is assigned to two unfinished lanes: "
                    f"{occupied[cpu]} and {(batch['batch_index'], lane['lane_index'])}"
                )
            occupied[cpu] = (batch["batch_index"], lane["lane_index"])
    return batches


def _pause_state(config: Mapping[str, Any], free_bytes: int) -> bool:
    path = Path(config["control_root"]) / PAUSE_NAME
    stop = config["disk_policy"]["stop_free_bytes"]
    resume = config["disk_policy"]["resume_free_bytes"]
    if free_bytes < stop:
        if not path.exists():
            _write_once(path, _seal({
                "schema_version": SCHEMA_VERSION,
                "kind": PAUSE_KIND,
                "created_utc": _utc_now(),
                "free_bytes": free_bytes,
                "stop_free_bytes": stop,
                "resume_free_bytes": resume,
                "reason": "LOW_DISK",
            }))
        return True
    if path.exists():
        pause = _read_json(path)
        if not _selfhash_valid(pause) or pause.get("kind") != PAUSE_KIND:
            raise SupervisorError("low-disk pause record is malformed")
        if free_bytes < resume:
            return True
        path.unlink()
        _fsync_directory(path.parent)
    return False


def plan_actions(
    batches: Sequence[Mapping[str, Any]], *, paused: bool,
) -> list[tuple[int, str]]:
    """Choose at most one idempotent coordinator action per existing batch."""

    planned: list[tuple[int, str]] = []
    for batch in batches:
        if batch.get("state") == "MISSING":
            continue
        states = [lane.get("state") for lane in batch.get("lanes", [])]
        incomplete = batch.get("incomplete_action")
        if incomplete:
            planned.append((batch["batch_index"], incomplete))
            continue
        bad = [
            state for state in states
            if state in {"POISONED", "START_INCOMPLETE", "TERMINAL_INCOMPLETE"}
        ]
        if bad:
            raise SupervisorError(
                f"batch {batch['batch_index']} contains fail-closed lane state {bad[0]}"
            )
        if paused:
            if "RUNNING" in states:
                planned.append((batch["batch_index"], "checkpoint-stop"))
            elif any(state in {"FINAL", "PRUNE_INCOMPLETE"} for state in states):
                planned.append((batch["batch_index"], "prune-transport"))
            continue
        if any(state in {"FINAL", "PRUNE_INCOMPLETE"} for state in states):
            planned.append((batch["batch_index"], "prune-transport"))
            continue
        if "INACTIVE" in states:
            planned.append((batch["batch_index"], "harvest-inactive"))
        elif "CHECKPOINTED" in states:
            planned.append((batch["batch_index"], "resume"))
        elif "PREPARED" in states:
            planned.append((batch["batch_index"], "start"))
    return planned


def plan_preparations(
    config: Mapping[str, Any], batches: Sequence[Mapping[str, Any]],
    *, paused: bool,
) -> list[tuple[int, list[int]]]:
    if paused:
        return []
    occupied = {
        lane["cpu"]
        for batch in batches for lane in batch.get("lanes", [])
        if lane.get("state") not in TERMINAL_LANE_STATES
    }
    free = [cpu for cpu in config["cpus"] if cpu not in occupied]
    missing = [
        batch["batch_index"] for batch in batches if batch.get("state") == "MISSING"
    ]
    count = min(len(missing), len(free) // LANES_PER_BATCH)
    return [
        (missing[index], free[index * 4:(index + 1) * 4])
        for index in range(count)
    ]


def _run_command(argv: Sequence[str], log_path: Path) -> dict[str, Any]:
    started = _utc_now()
    result = subprocess.run(
        list(argv), stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False,
    )
    record = {
        "started_utc": started,
        "finished_utc": _utc_now(),
        "argv": list(argv),
        "returncode": result.returncode,
        "stdout": result.stdout.decode("utf-8", "replace"),
        "stderr": result.stderr.decode("utf-8", "replace"),
    }
    _atomic_replace(log_path, record)
    output: dict[str, Any] | None = None
    try:
        decoded = json.loads(result.stdout.decode("ascii"))
        output = decoded if type(decoded) is dict else None
    except (UnicodeDecodeError, json.JSONDecodeError):
        pass
    if result.returncode not in {0, 3} or output is None:
        raise SupervisorError(
            f"command failed rc={result.returncode}: {' '.join(argv)}; "
            f"stderr={record['stderr'][-2000:]}"
        )
    if output.get("hard_failed_lane_count", 0) != 0:
        raise SupervisorError(
            f"batch action has hard-failed lanes: {' '.join(argv)}"
        )
    return output


def _action_command(config: Mapping[str, Any], batch_index: int, action: str) -> list[str]:
    return [
        config["python"]["invocation_path"],
        str(Path(four_lane.__file__).resolve()), action,
        "--root", str(_batch_root(config, batch_index)),
    ]


def _prepare_command(
    config: Mapping[str, Any], batch_index: int, cpus: Sequence[int],
) -> list[str]:
    inputs = config["input_files"]
    caps = config["resource_caps"]
    return [
        config["python"]["invocation_path"],
        str(Path(four_lane.__file__).resolve()), "prepare",
        "--root", str(_batch_root(config, batch_index)),
        "--parent-manifest", inputs["parent_manifest"]["path"],
        "--width6-campaign", inputs["width6_campaign"]["path"],
        "--width10-campaign", inputs["width10_campaign"]["path"],
        "--parent-cube-index", "0", "--batch-index", str(batch_index),
        "--cpus", *(str(cpu) for cpu in cpus),
        "--proof-max-bytes", str(caps["proof_max_bytes"]),
        "--checkpoint-image-max-bytes", str(caps["checkpoint_image_max_bytes"]),
        "--checkpoint-images-per-generation-max",
        str(caps["checkpoint_images_per_generation_max"]),
        "--checkpoint-generation-max-count",
        str(caps["checkpoint_generation_max_count"]),
        "--checkpoint-generation-metadata-max-bytes",
        str(caps["checkpoint_generation_metadata_max_bytes"]),
    ]


def _log_path(config: Mapping[str, Any], batch_index: int, operation: str) -> Path:
    safe = operation.replace("-", "_")
    return Path(config["control_root"]) / LOG_DIR_NAME / (
        f"batch-{batch_index:04d}-{safe}.json"
    )


def _invoke_actions(
    config: Mapping[str, Any], actions: Sequence[tuple[int, str]],
) -> None:
    if not actions:
        return
    failures: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(
        max_workers=min(config["action_workers"], len(actions))
    ) as executor:
        futures = {
            executor.submit(
                _run_command, _action_command(config, batch_index, action),
                _log_path(config, batch_index, action),
            ): (batch_index, action)
            for batch_index, action in actions
        }
        for future in concurrent.futures.as_completed(futures):
            batch_index, action = futures[future]
            try:
                future.result()
            except Exception as exc:
                failures.append(
                    f"batch {batch_index} {action}: {type(exc).__name__}: {exc}"
                )
    if failures:
        raise SupervisorError("; ".join(failures))


def _prepare_and_maybe_start(
    config: Mapping[str, Any], batch_index: int, cpus: Sequence[int],
) -> None:
    prepared = _run_command(
        _prepare_command(config, batch_index, cpus),
        _log_path(config, batch_index, "prepare"),
    )
    if (
        prepared.get("all_lanes_succeeded") is not True
        or prepared.get("batch_committed") is not True
    ):
        raise SupervisorError(
            f"batch {batch_index} prepare did not commit all four lanes"
        )
    free = shutil.disk_usage(config["run_parent"]).free
    if free >= config["disk_policy"]["stop_free_bytes"]:
        _run_command(
            _action_command(config, batch_index, "start"),
            _log_path(config, batch_index, "start"),
        )


def _invoke_preparations(
    config: Mapping[str, Any], plans: Sequence[tuple[int, Sequence[int]]],
) -> None:
    if not plans:
        return
    failures: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(
        max_workers=min(config["action_workers"], len(plans))
    ) as executor:
        futures = {
            executor.submit(_prepare_and_maybe_start, config, index, cpus): index
            for index, cpus in plans
        }
        for future in concurrent.futures.as_completed(futures):
            index = futures[future]
            try:
                future.result()
            except Exception as exc:
                failures.append(f"batch {index} prepare/start: {type(exc).__name__}: {exc}")
    if failures:
        raise SupervisorError("; ".join(failures))


def campaign_status(
    config: Mapping[str, Any], batches: Sequence[Mapping[str, Any]],
    *, paused: bool, free_bytes: int,
) -> dict[str, Any]:
    counts = {state: 0 for state in sorted(LANE_STATES)}
    missing_batches = 0
    for batch in batches:
        if batch["state"] == "MISSING":
            missing_batches += 1
        for lane in batch["lanes"]:
            counts[lane["state"]] += 1
    expected_batches = config["batch_last"] - config["batch_first"] + 1
    expected_lanes = expected_batches * LANES_PER_BATCH
    observed_lanes = sum(counts.values())
    completed = counts["PRUNED"]
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "kind": STATUS_KIND,
        "observed_utc": _utc_now(),
        "config_sha256": config["record_sha256"],
        "run_parent": config["run_parent"],
        "batch_first": config["batch_first"],
        "batch_last": config["batch_last"],
        "expected_batch_count": expected_batches,
        "missing_batch_count": missing_batches,
        "expected_lane_count": expected_lanes,
        "observed_lane_count": observed_lanes,
        "lane_state_counts": counts,
        "running_lane_count": counts["RUNNING"],
        "locally_completed_pruned_lane_count": completed,
        "free_cpu_slots": max(0, config["max_active_lanes"] - (
            observed_lanes - completed
        )),
        "filesystem_free_bytes": free_bytes,
        "low_disk_paused": paused,
        "locally_complete": completed == expected_lanes,
        "parent_cube_aggregate_complete": False,
        "scientific_claim": False,
    })


def reconcile_once(config: Mapping[str, Any]) -> dict[str, Any]:
    free = shutil.disk_usage(config["run_parent"]).free
    paused = _pause_state(config, free)
    if paused:
        return checkpoint_all(config)
    batches = observe_campaign(config)
    actions = plan_actions(batches, paused=paused)
    _invoke_actions(config, actions)
    batches = observe_campaign(config)
    plans = plan_preparations(config, batches, paused=paused)
    _invoke_preparations(config, plans)
    if plans:
        batches = observe_campaign(config)
    free = shutil.disk_usage(config["run_parent"]).free
    paused = _pause_state(config, free)
    status = campaign_status(config, batches, paused=paused, free_bytes=free)
    _atomic_replace(Path(config["control_root"]) / STATUS_NAME, status)
    return status


def checkpoint_all(config: Mapping[str, Any]) -> dict[str, Any]:
    batches = observe_campaign(config)
    failures: list[str] = []
    incomplete = [
        (batch["batch_index"], batch["incomplete_action"])
        for batch in batches if batch.get("incomplete_action")
    ]
    try:
        _invoke_actions(config, incomplete)
    except SupervisorError as exc:
        failures.append(str(exc))
    if incomplete:
        batches = observe_campaign(config)
    actions = [
        (batch["batch_index"], "checkpoint-stop")
        for batch in batches
        if batch.get("incomplete_action") is None
        if "RUNNING" in [lane["state"] for lane in batch["lanes"]]
    ]
    try:
        _invoke_actions(config, actions)
    except SupervisorError as exc:
        failures.append(str(exc))
    batches = observe_campaign(config)
    free = shutil.disk_usage(config["run_parent"]).free
    paused = (Path(config["control_root"]) / PAUSE_NAME).exists()
    status = campaign_status(config, batches, paused=paused, free_bytes=free)
    _atomic_replace(Path(config["control_root"]) / STATUS_NAME, status)
    if failures:
        raise SupervisorError(
            "checkpoint-stop completed with failures: " + "; ".join(failures)
        )
    return status


def run_forever(config: Mapping[str, Any], *, once: bool) -> dict[str, Any]:
    preflight = preflight_toolchain()
    if preflight["valid"] is not True:
        raise SupervisorError(
            "strict toolchain preflight failed: " + "; ".join(preflight["failures"])
        )
    stop_requested = False

    def request_stop(_signum: int, _frame: Any) -> None:
        nonlocal stop_requested
        stop_requested = True

    previous_handlers = {
        signum: signal.signal(signum, request_stop)
        for signum in (signal.SIGINT, signal.SIGTERM)
    }
    try:
        status: dict[str, Any] = {}
        while True:
            status = reconcile_once(config)
            sys.stdout.buffer.write(_canonical_bytes(status) + b"\n")
            sys.stdout.buffer.flush()
            if once or status["locally_complete"]:
                return status
            if stop_requested:
                return checkpoint_all(config)
            deadline = time.monotonic() + config["poll_seconds"]
            while time.monotonic() < deadline:
                if stop_requested:
                    return checkpoint_all(config)
                time.sleep(min(1.0, deadline - time.monotonic()))
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)


def _caps_from_args(args: argparse.Namespace) -> dict[str, int]:
    return {
        key: getattr(args, key) for key in four_lane.static_v1.CAP_INPUT_FIELDS
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init", allow_abbrev=False)
    init.add_argument("--run-parent", type=Path, required=True)
    init.add_argument("--input", type=Path, required=True)
    init.add_argument("--tag", required=True)
    init.add_argument("--batch-first", type=int, default=12)
    init.add_argument("--batch-last", type=int, default=255)
    init.add_argument("--cpus", type=int, nargs="+")
    init.add_argument("--stop-free-bytes", type=int, default=DEFAULT_STOP_FREE_BYTES)
    init.add_argument("--resume-free-bytes", type=int, default=DEFAULT_RESUME_FREE_BYTES)
    init.add_argument("--poll-seconds", type=int, default=DEFAULT_POLL_SECONDS)
    init.add_argument("--action-workers", type=int, default=DEFAULT_ACTION_WORKERS)
    for key, value in RESOURCE_DEFAULTS.items():
        init.add_argument("--" + key.replace("_", "-"), type=int, default=value)
    for name in ("run", "status", "checkpoint-stop"):
        action = sub.add_parser(name, allow_abbrev=False)
        action.add_argument("--root", type=Path, required=True)
        if name == "run":
            action.add_argument("--once", action="store_true")
    preflight = sub.add_parser("preflight", allow_abbrev=False)
    preflight.add_argument("--input", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "preflight":
        _input_records(args.input)
        result = preflight_toolchain()
        sys.stdout.buffer.write(_canonical_bytes(result) + b"\n")
        return 0 if result["valid"] else 2
    if args.command == "init":
        run_parent = _plain_absolute_directory(args.run_parent)
        cpus = (
            sorted(os.sched_getaffinity(0)) if args.cpus is None else args.cpus
        )
        result = initialize(
            run_parent=run_parent, input_dir=args.input, tag=args.tag,
            batch_first=args.batch_first, batch_last=args.batch_last,
            cpus=cpus, stop_free_bytes=args.stop_free_bytes,
            resume_free_bytes=args.resume_free_bytes,
            poll_seconds=args.poll_seconds, action_workers=args.action_workers,
            resource_caps=_caps_from_args(args),
        )
        sys.stdout.buffer.write(_canonical_bytes(result) + b"\n")
        return 0
    config = _load_config(args.root)
    with _supervisor_lock(Path(config["control_root"])):
        if args.command == "run":
            result = run_forever(config, once=args.once)
        elif args.command == "checkpoint-stop":
            result = checkpoint_all(config)
        elif args.command == "status":
            batches = observe_campaign(config)
            free = shutil.disk_usage(config["run_parent"]).free
            paused = (Path(config["control_root"]) / PAUSE_NAME).exists()
            result = campaign_status(config, batches, paused=paused, free_bytes=free)
        else:  # pragma: no cover
            raise SupervisorError("unreachable command")
    sys.stdout.buffer.write(_canonical_bytes(result) + b"\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (SupervisorError, OSError, ValueError, TypeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)


__all__ = [
    "INPUT_HASHES", "LANE_STATES", "RESOURCE_DEFAULTS", "SupervisorError",
    "campaign_status", "checkpoint_all", "initialize", "main",
    "observe_campaign", "plan_actions", "plan_preparations",
    "preflight_toolchain", "reconcile_once", "run_forever",
]
