#!/usr/bin/env python3
"""Fail-closed four-lane dispatcher for one nested width-ten paper400 batch.

This coordinator authenticates one immutable batch of four exact leaves and
delegates every solver/checkpoint/proof action to the hierarchical child
runner.  It never calls the DMTCP controller directly.  Batch and checkpoint
records are transport/coverage evidence only; they do not make an UNSAT or
distance claim.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import stat
import sys
from pathlib import Path
from typing import Any, Callable, Iterator, Mapping, Sequence


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_nested_width10_campaign_v1 as nested
from scripts import paper400_dic5_nested_width10_resume_static_v1 as static_v1
from scripts import run_paper400_dic5_nested_width10_child_resume_proof_v1 as child_runner


SCHEMA_VERSION = 1
KIND = "paper400-dic5-nested-width10-four-lane-batch-v1"
GATE = "paper400-dic5-nested-width10-four-lane-v1"
AUTHORITY_COVER_TRANSPORT = "COVER_ONLY_TRANSPORT"
AUTHORITY_SYNTHETIC = "SYNTHETIC_COVER_ONLY_TRANSPORT"
LANES_PER_BATCH = 4
BATCH_COUNT = nested.LEAF_COUNT // LANES_PER_BATCH

STATIC_PARENT = Path("static/parent-manifest.json")
STATIC_WIDTH6_CAMPAIGN = Path("static/width6-campaign.json")
STATIC_WIDTH10_CAMPAIGN = Path("static/width10-campaign.json")
BATCH_COMMIT = Path("batch.json")
LOCK_FILE = Path(".batch.lock")
ACTIONS = Path("actions")
LANES = Path("lanes")

MAX_INPUT_BYTES = 64 << 20
ACTION_NAMES = frozenset({
    "start", "checkpoint-stop", "resume", "status", "verify-checkpoint",
    "harvest-inactive",
})
AFFINITY_ACTIONS = frozenset({"start", "checkpoint-stop", "resume"})
TRANSPORT_STATES = frozenset({
    "RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
})
LANE_DISPOSITIONS = frozenset({
    "OBSERVED", "APPLIED", "SKIPPED", "PENDING", "UNRESOLVED", "FAILED",
})
GOAL_DISPOSITIONS = frozenset({"OBSERVED", "APPLIED", "SKIPPED"})
ACTION_RECORD_NAMES = frozenset({
    "claim.json", "result.json",
    *{f"lane-{lane_index}.json" for lane_index in range(4)},
})

BATCH_FIELDS = frozenset({
    "schema_version", "kind", "gate", "authority", "test_only",
    "production_eligible", "scientific_claim", "root", "root_identity",
    "width6_campaign_binding", "width10_campaign_binding",
    "parent_binding", "batch", "lanes",
    "cpu_policy", "resource_policy", "source_binding", "action_policy",
    "claim_scope", "record_sha256",
})


class FourLaneBatchError(RuntimeError):
    """A campaign, lane, root, source, CPU, or action binding failed."""


def canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise FourLaneBatchError(f"value is not canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any]) -> dict[str, Any]:
    if type(value) is not dict or "record_sha256" in value:
        raise FourLaneBatchError("invalid value passed to seal")
    result = dict(value)
    result["record_sha256"] = canonical_sha256(result)
    return result


def selfhash_valid(value: Any) -> bool:
    if type(value) is not dict:
        return False
    stored = value.get("record_sha256")
    if type(stored) is not str or len(stored) != 64:
        return False
    unsigned = dict(value)
    unsigned.pop("record_sha256", None)
    try:
        return stored == canonical_sha256(unsigned)
    except FourLaneBatchError:
        return False


def _file_sha256(path: Path, *, cap: int = MAX_INPUT_BYTES) -> str:
    candidate = Path(path)
    try:
        raw = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise FourLaneBatchError(f"cannot resolve bound file: {candidate}") from exc
    if stat.S_ISLNK(raw.st_mode) or not stat.S_ISREG(raw.st_mode):
        raise FourLaneBatchError(f"bound file is not plain: {candidate}")
    fd = os.open(resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        if before.st_size > cap:
            raise FourLaneBatchError(f"bound file exceeds cap: {candidate}")
        digest = hashlib.sha256()
        observed = 0
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            observed += len(chunk)
            if observed > cap:
                raise FourLaneBatchError(f"bound file exceeds cap: {candidate}")
            digest.update(chunk)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_size,
        item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or observed != before.st_size:
        raise FourLaneBatchError(f"bound file changed while hashing: {candidate}")
    return digest.hexdigest()


def _source_binding() -> dict[str, Any]:
    paths = {
        "nested_width10_campaign_source": Path(nested.__file__).resolve(),
        "width6_campaign_source": Path(nested.width6.__file__).resolve(),
        "hierarchical_refiner_source": Path(nested.hierarchy.__file__).resolve(),
        "resume_static_source": Path(static_v1.__file__).resolve(),
        "nested_width10_proof_records_source": Path(
            child_runner.proof_v1.__file__
        ).resolve(),
        "nested_width10_child_runner_source": Path(child_runner.__file__).resolve(),
        "four_lane_coordinator_source": Path(__file__).resolve(),
    }
    records = []
    for role, path in sorted(paths.items()):
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise FourLaneBatchError(f"source escapes project: {role}") from exc
        records.append({
            "role": role,
            "relative_path": relative,
            "sha256": _file_sha256(path, cap=16 << 20),
        })
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "fresh-current-source-sha256-width10-v1",
        "sources": records,
        "source_role_sequence_sha256": canonical_sha256([
            item["role"] for item in records
        ]),
    })


def _root_identity(root: Path) -> dict[str, Any]:
    target = Path(root)
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise FourLaneBatchError(f"cannot resolve batch root: {target}") from exc
    if (
        not target.is_absolute()
        or str(target) != os.path.abspath(str(target))
        or resolved != target
        or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise FourLaneBatchError("batch root is not canonical owned mode-0700")
    return {
        "path": str(target), "device": int(lexical.st_dev),
        "inode": int(lexical.st_ino), "uid": int(lexical.st_uid),
        "mode": stat.S_IMODE(lexical.st_mode),
    }


def _new_root(root: Path) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise FourLaneBatchError("root must be normalized absolute")
    if target.exists() or target.is_symlink():
        raise FourLaneBatchError("new batch root already exists")
    parent = target.parent.resolve(strict=True)
    if parent != target.parent or target.parent.is_symlink():
        raise FourLaneBatchError("batch root parent is aliased")
    os.mkdir(target, 0o700)
    os.chmod(target, 0o700, follow_symlinks=False)
    parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)
    _root_identity(target)
    return target


def _mkdir(parent: Path, name: str) -> Path:
    if not name or "/" in name or name in {".", ".."}:
        raise FourLaneBatchError("invalid directory component")
    try:
        parent_info = parent.lstat()
        parent_resolved = parent.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise FourLaneBatchError("cannot resolve directory parent") from exc
    if (
        parent_resolved != parent or stat.S_ISLNK(parent_info.st_mode)
        or not stat.S_ISDIR(parent_info.st_mode)
        or parent_info.st_uid != os.geteuid()
        or stat.S_IMODE(parent_info.st_mode) != 0o700
    ):
        raise FourLaneBatchError(
            "directory parent is not canonical owned mode-0700"
        )
    target = parent / name
    os.mkdir(target, 0o700)
    os.chmod(target, 0o700, follow_symlinks=False)
    info = target.lstat()
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise FourLaneBatchError("new directory is not plain")
    return target


def _publish_bytes(path: Path, payload: bytes) -> None:
    if type(payload) is not bytes:
        raise FourLaneBatchError("published payload must be bytes")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    fd = os.open(path, flags, 0o600)
    try:
        view = memoryview(payload)
        offset = 0
        while offset < len(view):
            offset += os.write(fd, view[offset:])
        os.fsync(fd)
    finally:
        os.close(fd)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    _publish_bytes(path, canonical_bytes(dict(value)) + b"\n")


def _fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _action_temp_target(name: str) -> str | None:
    for target_name in ACTION_RECORD_NAMES:
        prefix = f".{target_name}.publish-"
        if not name.startswith(prefix) or not name.endswith(".tmp"):
            continue
        marker = name[len(prefix):-4]
        pid_text, separator, nonce = marker.partition("-")
        if (
            separator
            and pid_text.isdigit()
            and int(pid_text) > 0
            and len(nonce) == 32
            and all(character in "0123456789abcdef" for character in nonce)
        ):
            return target_name
    return None


def _remove_exact_action_temp(
    path: Path, *, device: int, inode: int,
) -> None:
    try:
        info = path.lstat()
    except FileNotFoundError:
        return
    if (
        stat.S_ISLNK(info.st_mode)
        or not stat.S_ISREG(info.st_mode)
        or info.st_dev != device
        or info.st_ino != inode
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != 0o600
    ):
        raise FourLaneBatchError("action publish temporary changed identity")
    os.unlink(path)


def _publish_action_json(path: Path, value: Mapping[str, Any]) -> None:
    if path.name not in ACTION_RECORD_NAMES:
        raise FourLaneBatchError("invalid action record publication target")
    payload = canonical_bytes(dict(value)) + b"\n"
    nonce = os.urandom(16).hex()
    temporary = path.parent / (
        f".{path.name}.publish-{os.getpid()}-{nonce}.tmp"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    fd = os.open(temporary, flags, 0o600)
    info = os.fstat(fd)
    if (
        not stat.S_ISREG(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != 0o600
        or info.st_nlink != 1
    ):
        os.close(fd)
        raise FourLaneBatchError("new action publish temporary is unsafe")
    try:
        view = memoryview(payload)
        offset = 0
        while offset < len(view):
            written = os.write(fd, view[offset:])
            if written <= 0:
                raise FourLaneBatchError("short action record publication")
            offset += written
        os.fsync(fd)
    except Exception:
        os.close(fd)
        _remove_exact_action_temp(
            temporary, device=info.st_dev, inode=info.st_ino,
        )
        _fsync_directory(path.parent)
        raise
    os.close(fd)
    try:
        os.link(temporary, path, follow_symlinks=False)
        _fsync_directory(path.parent)
    except Exception:
        _remove_exact_action_temp(
            temporary, device=info.st_dev, inode=info.st_ino,
        )
        _fsync_directory(path.parent)
        raise
    _remove_exact_action_temp(
        temporary, device=info.st_dev, inode=info.st_ino,
    )
    _fsync_directory(path.parent)


def _recover_action_publish_temps(action_dir: Path) -> None:
    removed = False
    for candidate in list(action_dir.iterdir()):
        target_name = _action_temp_target(candidate.name)
        if target_name is None:
            continue
        info = candidate.lstat()
        if (
            stat.S_ISLNK(info.st_mode)
            or not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink not in {1, 2}
        ):
            raise FourLaneBatchError("unsafe action publish temporary")
        target = action_dir / target_name
        try:
            target_info = target.lstat()
        except FileNotFoundError:
            if info.st_nlink != 1:
                raise FourLaneBatchError(
                    "unbound action publish temporary has extra links"
                )
        else:
            if (
                stat.S_ISLNK(target_info.st_mode)
                or not stat.S_ISREG(target_info.st_mode)
            ):
                raise FourLaneBatchError(
                    "action publish target is not a plain file"
                )
            same_inode = (
                info.st_dev == target_info.st_dev
                and info.st_ino == target_info.st_ino
            )
            if info.st_nlink == 2 and not same_inode:
                raise FourLaneBatchError(
                    "linked action publish temporary has the wrong target"
                )
            if info.st_nlink == 1 and same_inode:
                raise FourLaneBatchError(
                    "action publish link count is internally inconsistent"
                )
        _remove_exact_action_temp(
            candidate, device=info.st_dev, inode=info.st_ino,
        )
        removed = True
    if removed:
        _fsync_directory(action_dir)


def _read_canonical_json(path: Path) -> tuple[dict[str, Any], bytes]:
    candidate = Path(path)
    try:
        raw = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise FourLaneBatchError(f"cannot resolve JSON input: {candidate}") from exc
    if stat.S_ISLNK(raw.st_mode) or not stat.S_ISREG(raw.st_mode):
        raise FourLaneBatchError("JSON input must be a plain file")
    fd = os.open(resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        if before.st_size > MAX_INPUT_BYTES:
            raise FourLaneBatchError("JSON input exceeds cap")
        payload = bytearray()
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            payload.extend(chunk)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_size,
        item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(payload) != before.st_size:
        raise FourLaneBatchError("JSON input changed while reading")
    try:
        value = json.loads(payload)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise FourLaneBatchError("JSON input cannot be decoded") from exc
    if type(value) is not dict:
        raise FourLaneBatchError("JSON input is not an object")
    canonical = canonical_bytes(value)
    if bytes(payload) not in {canonical, canonical + b"\n"}:
        raise FourLaneBatchError("JSON input is not canonical bytes")
    return value, bytes(payload)


def _lock_identity(root: Path) -> dict[str, Any]:
    path = root / LOCK_FILE
    try:
        info = path.lstat()
    except OSError as exc:
        raise FourLaneBatchError("batch lock is missing") from exc
    if (
        stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode)
        or info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) != 0o600
    ):
        raise FourLaneBatchError("batch lock is not a plain owned mode-0600 file")
    return {
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "uid": int(info.st_uid), "mode": stat.S_IMODE(info.st_mode),
    }


def _create_lock(root: Path) -> None:
    fd = os.open(
        root / LOCK_FILE,
        os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
    _lock_identity(root)


@contextlib.contextmanager
def _batch_lock(root: Path) -> Iterator[dict[str, Any]]:
    root_before = _root_identity(root)
    lock_before = _lock_identity(root)
    fd = os.open(root / LOCK_FILE, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        observed = os.fstat(fd)
        if (
            observed.st_dev != lock_before["device"]
            or observed.st_ino != lock_before["inode"]
        ):
            raise FourLaneBatchError("batch lock changed before acquisition")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise FourLaneBatchError("batch root is busy") from exc
        yield lock_before
        if (
            _root_identity(root) != root_before
            or _lock_identity(root) != lock_before
        ):
            raise FourLaneBatchError("batch root or lock changed while held")
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _validate_cpus(cpus: Sequence[int]) -> list[int]:
    result = list(cpus)
    if (
        len(result) != LANES_PER_BATCH
        or any(type(cpu) is not int or cpu < 0 for cpu in result)
        or len(set(result)) != LANES_PER_BATCH
    ):
        raise FourLaneBatchError("exactly four distinct integer CPUs are required")
    allowed = os.sched_getaffinity(0)
    if any(cpu not in allowed for cpu in result):
        raise FourLaneBatchError("requested CPU is outside current affinity")
    return result


@contextlib.contextmanager
def _singleton_affinity(cpu: int) -> Iterator[None]:
    previous = os.sched_getaffinity(0)
    if cpu not in previous:
        raise FourLaneBatchError("lane CPU is outside current affinity")
    try:
        os.sched_setaffinity(0, {cpu})
        if os.sched_getaffinity(0) != {cpu}:
            raise FourLaneBatchError("failed to establish singleton affinity")
        yield
    finally:
        os.sched_setaffinity(0, previous)
        if os.sched_getaffinity(0) != previous:
            raise FourLaneBatchError("failed to restore coordinator affinity")


def _current_instance(strict_base: bool, instance: Any | None) -> Any:
    if type(strict_base) is not bool:
        raise FourLaneBatchError("strict_base must be a strict boolean")
    if strict_base:
        if instance is not None:
            raise FourLaneBatchError("production replay must build the current instance")
        return nested.cube16.optimized.build_optimized_instance()
    if instance is None:
        raise FourLaneBatchError("synthetic replay requires an explicit instance")
    return instance


def _selected_parent_index(campaign: Mapping[str, Any]) -> int:
    selected = campaign.get("selected_parent")
    index = selected.get("parent_cube_index") if type(selected) is dict else None
    if index != nested.TARGET_PARENT_CUBE_INDEX:
        raise FourLaneBatchError("campaign is not exactly parent000")
    return index


def _selected_batch(campaign: Mapping[str, Any], batch_index: int) -> dict[str, Any]:
    if (
        type(batch_index) is not int
        or not 0 <= batch_index < BATCH_COUNT
        or BATCH_COUNT != 256
        or nested.LEAF_COUNT != 1024
        or nested.WIDTH6_LEAF_COUNT != 64
        or nested.LOCAL_CHILD_COUNT != 16
    ):
        raise FourLaneBatchError("batch index is outside 0..255")
    leaves = campaign.get("leaves")
    if type(leaves) is not list or len(leaves) != nested.LEAF_COUNT:
        raise FourLaneBatchError("campaign does not contain exactly 1024 leaves")

    # Preserve the frozen width-six interleave: hold the old two-bit suffix
    # and the new four-bit suffix fixed while crossing four old width-four
    # prefixes.  Batch zero is therefore [0, 64, 128, 192].
    groups_per_old_suffix = nested.LOCAL_CHILD_COUNT
    batches_per_prefix_group = 4 * groups_per_old_suffix
    width4_prefix_group_start = (
        batch_index // batches_per_prefix_group
    ) * LANES_PER_BATCH
    within_group = batch_index % batches_per_prefix_group
    width6_old_suffix_index = within_group // nested.LOCAL_CHILD_COUNT
    extension_suffix_index = within_group % nested.LOCAL_CHILD_COUNT
    expected_width6_indices = [
        (width4_prefix_group_start + lane_index) * 4
        + width6_old_suffix_index
        for lane_index in range(LANES_PER_BATCH)
    ]
    expected_indices = [
        width6_leaf_index * nested.LOCAL_CHILD_COUNT
        + extension_suffix_index
        for width6_leaf_index in expected_width6_indices
    ]
    lanes = []
    for lane_index, (width6_leaf_index, global_leaf_index) in enumerate(
        zip(expected_width6_indices, expected_indices, strict=True)
    ):
        leaf = leaves[global_leaf_index]
        if (
            type(leaf) is not dict
            or not nested.selfhash_valid(leaf, "leaf_sha256")
            or leaf.get("global_leaf_index") != global_leaf_index
            or leaf.get("width6_leaf_index") != width6_leaf_index
            or leaf.get("local_child_index") != extension_suffix_index
        ):
            raise FourLaneBatchError(
                "interleaved batch leaf is missing, substituted, or reordered"
            )
        lanes.append({
            "lane_index": lane_index,
            "global_leaf_index": global_leaf_index,
            "leaf_sha256": leaf["leaf_sha256"],
            "width6_leaf_index": width6_leaf_index,
            "local_child_index": extension_suffix_index,
        })
    unsigned = {
        "schema_version": SCHEMA_VERSION,
        "batch_index": batch_index,
        "lane_count": LANES_PER_BATCH,
        "width4_prefix_group_start": width4_prefix_group_start,
        "width6_old_suffix_index": width6_old_suffix_index,
        "extension_suffix_index": extension_suffix_index,
        "leaf_indices": expected_indices,
        "lanes": lanes,
    }
    return {**unsigned, "batch_sha256": canonical_sha256(unsigned)}


def _manifest_binding(value: Mapping[str, Any], payload: bytes, role: str) -> dict[str, Any]:
    return {
        "role": role,
        "manifest_sha256": value.get("manifest_sha256"),
        "canonical_json_bytes": len(payload),
        "canonical_json_sha256": hashlib.sha256(payload).hexdigest(),
    }


def _coordinator_tool_binding_valid(record: Mapping[str, Any]) -> bool:
    tool = record.get("toolchain_binding", {}).get("tools", {}).get(
        "four_lane_coordinator_source"
    )
    return bool(
        type(tool) is dict
        and tool.get("path") == str(Path(__file__).resolve())
        and tool.get("sha256") == _file_sha256(Path(__file__).resolve(), cap=16 << 20)
    )


def _lane_record(
    root: Path, campaign: Mapping[str, Any], batch: Mapping[str, Any],
    lane_index: int, cpu: int, static_record: Mapping[str, Any],
) -> dict[str, Any]:
    planned = batch["lanes"][lane_index]
    global_leaf_index = planned["global_leaf_index"]
    leaf = campaign["leaves"][global_leaf_index]
    lane_root = root / LANES / f"lane-{lane_index}"
    if (
        planned.get("leaf_sha256") != leaf.get("leaf_sha256")
        or planned.get("width6_leaf_index") != leaf.get("width6_leaf_index")
        or planned.get("local_child_index") != leaf.get("local_child_index")
        or leaf.get("global_leaf_index") != global_leaf_index
    ):
        raise FourLaneBatchError("batch lane/width-ten leaf binding mismatch")
    child = static_record.get("child", {})
    if (
        child.get("global_leaf_index") != global_leaf_index
        or child.get("child_index") != global_leaf_index
        or child.get("parent_cube_index") != leaf.get("parent_cube_index")
        or child.get("leaf_sha256") != leaf.get("leaf_sha256")
        or child.get("child_sha256") != leaf.get("leaf_sha256")
        or child.get("child_dimacs_sha256") != leaf.get("child_dimacs_sha256")
        or not _coordinator_tool_binding_valid(static_record)
    ):
        raise FourLaneBatchError("child static does not bind the exact width-ten leaf")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "lane_index": lane_index,
        "cpu": cpu,
        "global_leaf_index": global_leaf_index,
        "leaf_sha256": leaf["leaf_sha256"],
        "width6_leaf_index": leaf["width6_leaf_index"],
        "local_child_index": leaf["local_child_index"],
        "parent_cube_index": leaf["parent_cube_index"],
        "child_index": global_leaf_index,
        "child_sha256": leaf["leaf_sha256"],
        "child_dimacs_sha256": leaf["child_dimacs_sha256"],
        "child_root": str(lane_root),
        "child_root_identity": child_runner._root_identity(lane_root),
        "resume_static_sha256": static_record["record_sha256"],
    })


def _batch_manifest(
    root: Path, campaign: Mapping[str, Any], campaign_payload: bytes,
    width6_campaign: Mapping[str, Any], width6_payload: bytes,
    parent: Mapping[str, Any], parent_payload: bytes, batch_index: int,
    cpus: Sequence[int], caps: Mapping[str, Any],
    static_records: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    batch = _selected_batch(campaign, batch_index)
    normalized_caps = static_v1.normalize_resource_caps(caps)
    lanes = [
        _lane_record(root, campaign, batch, index, cpus[index], static_records[index])
        for index in range(LANES_PER_BATCH)
    ]
    flags = (
        campaign.get("test_only"),
        width6_campaign.get("test_only"),
        parent.get("test_only"),
    )
    if any(type(value) is not bool for value in flags) or len(set(flags)) != 1:
        raise FourLaneBatchError("campaign/parent authority mismatch")
    test_only = flags[0]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "gate": GATE,
        "authority": AUTHORITY_SYNTHETIC if test_only else AUTHORITY_COVER_TRANSPORT,
        "test_only": test_only,
        "production_eligible": False,
        "scientific_claim": False,
        "root": str(root),
        "root_identity": _root_identity(root),
        "width6_campaign_binding": _manifest_binding(
            width6_campaign, width6_payload, "paper400-parent000-width6-campaign"
        ),
        "width10_campaign_binding": _manifest_binding(
            campaign, campaign_payload, "paper400-parent000-width10-campaign"
        ),
        "parent_binding": _manifest_binding(
            parent, parent_payload, "paper400-root-cover"
        ),
        "batch": {
            "batch_index": batch_index,
            "parent_cube_index": _selected_parent_index(campaign),
            "batch_sha256": batch["batch_sha256"],
            "lane_count": LANES_PER_BATCH,
            "leaf_indices": list(batch["leaf_indices"]),
            "width4_prefix_group_start": batch["width4_prefix_group_start"],
            "width6_old_suffix_index": batch["width6_old_suffix_index"],
            "extension_suffix_index": batch["extension_suffix_index"],
            "leaf_sha256_sequence_sha256": canonical_sha256([
                lane["leaf_sha256"] for lane in lanes
            ]),
        },
        "lanes": lanes,
        "cpu_policy": {
            "workers": LANES_PER_BATCH,
            "cpus": list(cpus),
            "all_distinct": len(set(cpus)) == LANES_PER_BATCH,
            "singleton_affinity_for_start_checkpoint_resume": True,
        },
        "resource_policy": normalized_caps,
        "source_binding": _source_binding(),
        "action_policy": {
            "child_runner_only": True,
            "direct_inner_controller_calls_forbidden": True,
            "batch_actions_are_not_atomic": True,
            "per_lane_partial_outcomes_persisted": True,
            "incomplete_prior_action_blocks_next_action": False,
            "incomplete_prior_action_requires_same_action_resume": True,
            "empty_final_action_directory_is_recoverable": True,
        },
        "claim_scope": {
            "exact_four_leaf_batch_binding": True,
            "parent_cover_width6_and_width10_campaign_replayed": True,
            "checkpoint_or_batch_record_is_scientific_evidence": False,
            "batch_success_alone_proves_parent_or_global_unsat": False,
            "all_1024_authenticated_leaf_proofs_still_required": True,
        },
    })


def _static_kwargs(
    instance: Any, strict_base: bool, caps: Mapping[str, Any],
    campaign_verification_record: Mapping[str, Any],
) -> dict[str, Any]:
    raw_caps = {key: caps.get(key) for key in static_v1.CAP_INPUT_FIELDS}
    return {
        "instance": None if strict_base else instance,
        "strict_base": strict_base,
        "tool_paths": child_runner._default_tool_paths(),
        "expected_tool_sha256": child_runner._default_tool_hashes(),
        "resource_caps": raw_caps,
        "campaign_verification_record": dict(campaign_verification_record),
    }


def _load_batch(
    root: Path, *, instance: Any | None = None, strict_base: bool | None = None,
) -> dict[str, Any]:
    target = Path(root)
    _root_identity(target)
    manifest, _manifest_payload = _read_canonical_json(target / BATCH_COMMIT)
    parent, parent_payload = _read_canonical_json(target / STATIC_PARENT)
    width6_campaign, width6_payload = _read_canonical_json(
        target / STATIC_WIDTH6_CAMPAIGN
    )
    campaign, campaign_payload = _read_canonical_json(
        target / STATIC_WIDTH10_CAMPAIGN
    )
    if set(manifest) != BATCH_FIELDS or not selfhash_valid(manifest):
        raise FourLaneBatchError("batch manifest schema/self-hash mismatch")
    recorded_test_only = manifest.get("test_only")
    expected_strict = not recorded_test_only if type(recorded_test_only) is bool else None
    if expected_strict is None or (
        strict_base is not None and strict_base is not expected_strict
    ):
        raise FourLaneBatchError("batch strict-base mode mismatch")
    replay_instance = _current_instance(expected_strict, instance)
    parent_cube_index = _selected_parent_index(campaign)
    if manifest.get("batch", {}).get("parent_cube_index") != parent_cube_index:
        raise FourLaneBatchError("batch selected-parent binding mismatch")
    replay = nested.verify_campaign_manifest(
        campaign,
        width6_campaign,
        parent,
        replay_instance,
        parent_cube_index=parent_cube_index,
        strict_base=expected_strict,
    )
    if replay.get("valid") is not True:
        raise FourLaneBatchError(
            f"width-ten campaign fresh replay failed: {replay.get('binding_failures')}"
        )
    batch_index = manifest.get("batch", {}).get("batch_index")
    batch = _selected_batch(campaign, batch_index)
    recorded_lanes = manifest.get("lanes")
    cpus = manifest.get("cpu_policy", {}).get("cpus")
    if type(recorded_lanes) is not list or len(recorded_lanes) != LANES_PER_BATCH:
        raise FourLaneBatchError("batch has fewer, duplicate, or extra lanes")
    if [lane.get("lane_index") for lane in recorded_lanes] != list(
        range(LANES_PER_BATCH)
    ):
        raise FourLaneBatchError("batch lanes are missing, duplicated, or reordered")
    checked_cpus = _validate_cpus(cpus if type(cpus) is list else [])
    caps = manifest.get("resource_policy")
    if type(caps) is not dict:
        raise FourLaneBatchError("batch resource policy is missing")
    raw_caps = {key: caps.get(key) for key in static_v1.CAP_INPUT_FIELDS}
    static_records = []
    kwargs = _static_kwargs(
        replay_instance, expected_strict, caps, replay,
    )
    for lane_index in range(LANES_PER_BATCH):
        lane = recorded_lanes[lane_index]
        planned = batch["lanes"][lane_index]
        if (
            lane.get("global_leaf_index") != planned["global_leaf_index"]
            or lane.get("leaf_sha256") != planned["leaf_sha256"]
        ):
            raise FourLaneBatchError("lane crosses or substitutes the fixed batch")
        lane_root = target / LANES / f"lane-{lane_index}"
        loaded = child_runner._load_static(lane_root, **kwargs)
        static_record = loaded["record"]
        if static_record.get("record_sha256") != lane.get("resume_static_sha256"):
            raise FourLaneBatchError("lane static SHA does not match batch")
        static_records.append(static_record)
    expected = _batch_manifest(
        target, campaign, campaign_payload, width6_campaign, width6_payload,
        parent, parent_payload, batch_index, checked_cpus, raw_caps,
        static_records,
    )
    if not static_v1.json_type_equal(manifest, expected):
        raise FourLaneBatchError("batch manifest is not exact current-source replay")
    return {
        "manifest": manifest,
        "parent": parent,
        "width6_campaign": width6_campaign,
        "campaign": campaign,
        "instance": replay_instance,
        "strict_base": expected_strict,
        "resource_caps": caps,
        "static_kwargs": kwargs,
    }


def _prepare_claim(
    root: Path, parent_cube_index: int, batch_index: int, cpus: Sequence[int],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-four-lane-prepare-claim-v1",
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "parent_cube_index": parent_cube_index,
        "batch_index": batch_index,
        "cpus": list(cpus),
        "nonce_hex": os.urandom(32).hex(),
        "pid": os.getpid(),
        "atomic": False,
        "scientific_claim": False,
    })


def prepare_batch(
    root: Path, *, width10_campaign_manifest_path: Path,
    width6_campaign_manifest_path: Path, parent_manifest_path: Path,
    parent_cube_index: int, batch_index: int, cpus: Sequence[int],
    resource_caps: Mapping[str, Any], strict_base: bool = True,
    instance: Any | None = None,
) -> dict[str, Any]:
    if parent_cube_index != nested.TARGET_PARENT_CUBE_INDEX:
        raise FourLaneBatchError("width-ten campaign is restricted to parent000")
    checked_cpus = _validate_cpus(cpus)
    replay_instance = _current_instance(strict_base, instance)
    campaign, source_campaign_payload = _read_canonical_json(
        width10_campaign_manifest_path
    )
    width6_campaign, source_width6_payload = _read_canonical_json(
        width6_campaign_manifest_path
    )
    parent, source_parent_payload = _read_canonical_json(parent_manifest_path)
    if _selected_parent_index(campaign) != parent_cube_index:
        raise FourLaneBatchError("campaign does not match requested parent")
    replay = nested.verify_campaign_manifest(
        campaign,
        width6_campaign,
        parent,
        replay_instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if replay.get("valid") is not True:
        raise FourLaneBatchError(
            f"width-ten campaign fresh replay failed: {replay.get('binding_failures')}"
        )
    batch = _selected_batch(campaign, batch_index)
    caps = static_v1.normalize_resource_caps(resource_caps)
    raw_caps = {key: caps[key] for key in static_v1.CAP_INPUT_FIELDS}
    tool_paths = child_runner._default_tool_paths()
    tool_hashes = child_runner._default_tool_hashes()
    coordinator = Path(__file__).resolve()
    if (
        Path(tool_paths.get("four_lane_coordinator_source", Path("/invalid"))).resolve()
        != coordinator
        or tool_hashes.get("four_lane_coordinator_source")
        != _file_sha256(coordinator, cap=16 << 20)
    ):
        raise FourLaneBatchError("child runner is not pinned to this coordinator")

    verified_child_payloads = [
        nested.verified_child_dimacs_from_verification(
            campaign,
            width6_campaign,
            parent,
            replay_instance,
            verification_record=replay,
            global_leaf_index=planned["global_leaf_index"],
            parent_cube_index=parent_cube_index,
            strict_base=strict_base,
        )
        for planned in batch["lanes"]
    ]
    if len(verified_child_payloads) != LANES_PER_BATCH:
        raise FourLaneBatchError("targeted child reconstruction count mismatch")

    target = _new_root(root)
    _create_lock(target)
    with _batch_lock(target):
        static_dir = _mkdir(target, "static")
        lanes_dir = _mkdir(target, LANES.name)
        _mkdir(target, ACTIONS.name)
        _publish_bytes(
            static_dir / STATIC_PARENT.name, canonical_bytes(parent) + b"\n"
        )
        _publish_bytes(
            static_dir / STATIC_WIDTH6_CAMPAIGN.name,
            canonical_bytes(width6_campaign) + b"\n",
        )
        _publish_bytes(
            static_dir / STATIC_WIDTH10_CAMPAIGN.name,
            canonical_bytes(campaign) + b"\n",
        )
        campaign_payload = canonical_bytes(campaign) + b"\n"
        width6_payload = canonical_bytes(width6_campaign) + b"\n"
        parent_payload = canonical_bytes(parent) + b"\n"
        claim = _prepare_claim(target, parent_cube_index, batch_index, checked_cpus)
        _publish_json(target / "prepare.claim.json", claim)
        outcomes: list[dict[str, Any]] = []
        static_records: list[dict[str, Any] | None] = [None] * LANES_PER_BATCH
        for lane_index in range(LANES_PER_BATCH):
            planned = batch["lanes"][lane_index]
            global_leaf_index = planned["global_leaf_index"]
            leaf = campaign["leaves"][global_leaf_index]
            if leaf.get("parent_cube_index") != parent_cube_index:
                raise FourLaneBatchError("leaf crosses the selected parent")
            lane_root = lanes_dir / f"lane-{lane_index}"
            try:
                record = child_runner.prepare_root_from_material(
                    lane_root,
                    parent_manifest=parent,
                    width6_campaign_manifest=width6_campaign,
                    width10_campaign_manifest=campaign,
                    instance=None if strict_base else replay_instance,
                    parent_cube_index=parent_cube_index,
                    global_leaf_index=global_leaf_index,
                    campaign_verification_record=replay,
                    verified_child_dimacs=verified_child_payloads[lane_index],
                    resource_caps=raw_caps,
                    strict_base=strict_base,
                    tool_paths=tool_paths,
                    expected_tool_sha256=tool_hashes,
                )
                static_records[lane_index] = record
                outcome = seal({
                    "schema_version": SCHEMA_VERSION,
                    "lane_index": lane_index,
                    "global_leaf_index": global_leaf_index,
                    "success": True,
                    "resume_static_sha256": record["record_sha256"],
                    "error_type": None,
                    "error_message": None,
                    "scientific_claim": False,
                })
            except Exception as exc:
                outcome = seal({
                    "schema_version": SCHEMA_VERSION,
                    "lane_index": lane_index,
                    "global_leaf_index": global_leaf_index,
                    "success": False,
                    "resume_static_sha256": None,
                    "error_type": type(exc).__name__,
                    "error_message": str(exc)[:4096],
                    "scientific_claim": False,
                })
            _publish_json(target / f"prepare-lane-{lane_index}.json", outcome)
            outcomes.append(outcome)
        all_succeeded = all(item["success"] is True for item in outcomes)
        result = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-nested-width10-four-lane-prepare-result-v1",
            "gate": GATE,
            "root": str(target),
            "batch_index": batch_index,
            "prepare_claim_sha256": claim["record_sha256"],
            "lane_outcome_sha256s": [item["record_sha256"] for item in outcomes],
            "all_lanes_succeeded": all_succeeded,
            "batch_committed": all_succeeded,
            "scientific_claim": False,
        })
        _publish_json(target / "prepare-result.json", result)
        if not all_succeeded:
            return result
        complete_records = [
            item for item in static_records if type(item) is dict
        ]
        if len(complete_records) != LANES_PER_BATCH:
            raise FourLaneBatchError("successful prepare lost a lane static record")
        manifest = _batch_manifest(
            target, campaign, campaign_payload, width6_campaign, width6_payload,
            parent, parent_payload, batch_index, checked_cpus, raw_caps,
            complete_records,
        )
        _publish_json(target / BATCH_COMMIT, manifest)
        return result


def _action_claim(
    root: Path, manifest: Mapping[str, Any], *, sequence: int,
    action: str, previous_sha: str | None,
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-four-lane-action-claim-v1",
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "batch_manifest_sha256": manifest["record_sha256"],
        "batch_index": manifest["batch"]["batch_index"],
        "action_sequence": sequence,
        "action": action,
        "previous_action_result_sha256": previous_sha,
        "nonce_hex": os.urandom(32).hex(),
        "pid": os.getpid(),
        "atomic": False,
        "scientific_claim": False,
    })


def _read_action_claim(
    path: Path, *, root: Path, manifest: Mapping[str, Any],
    sequence: int, previous_sha: str | None,
) -> dict[str, Any]:
    claim, _ = _read_canonical_json(path)
    fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "batch_manifest_sha256", "batch_index", "action_sequence", "action",
        "previous_action_result_sha256", "nonce_hex", "pid", "atomic",
        "scientific_claim", "record_sha256",
    }
    nonce = claim.get("nonce_hex")
    if (
        set(claim) != fields
        or not selfhash_valid(claim)
        or claim.get("schema_version") != SCHEMA_VERSION
        or claim.get("kind")
        != "paper400-nested-width10-four-lane-action-claim-v1"
        or claim.get("gate") != GATE
        or claim.get("root") != str(root)
        or not static_v1.json_type_equal(
            claim.get("root_identity"), _root_identity(root)
        )
        or claim.get("batch_manifest_sha256") != manifest["record_sha256"]
        or claim.get("batch_index") != manifest["batch"]["batch_index"]
        or claim.get("action_sequence") != sequence
        or claim.get("action") not in ACTION_NAMES
        or claim.get("previous_action_result_sha256") != previous_sha
        or type(nonce) is not str
        or len(nonce) != 64
        or any(character not in "0123456789abcdef" for character in nonce)
        or type(claim.get("pid")) is not int
        or claim.get("pid") <= 0
        or claim.get("atomic") is not False
        or claim.get("scientific_claim") is not False
    ):
        raise FourLaneBatchError("action claim schema or chain mismatch")
    return claim


def _normalized_status(value: Any) -> dict[str, Any]:
    if type(value) is not dict:
        raise FourLaneBatchError("child status returned a non-object")
    chain = value.get("chain")
    state = chain.get("state") if type(chain) is dict else None
    claimed = value.get("terminal_claimed")
    committed = value.get("terminal_committed")
    if (
        state not in TRANSPORT_STATES
        or type(claimed) is not bool
        or type(committed) is not bool
        or committed and not claimed
    ):
        raise FourLaneBatchError("child status truth table is malformed")
    return {
        "value": value,
        "state": state,
        "terminal_claimed": claimed,
        "terminal_committed": committed,
    }


def _make_lane_outcome(
    *, lane: Mapping[str, Any], action: str, sequence: int,
    claim_sha256: str, disposition: str, reason: str,
    goal_satisfied: bool, before: Mapping[str, Any] | None,
    after: Mapping[str, Any] | None, child_result: Mapping[str, Any] | None,
    error_type: str | None = None, error_message: str | None = None,
) -> dict[str, Any]:
    if disposition not in LANE_DISPOSITIONS:
        raise FourLaneBatchError("unknown lane disposition")
    if type(goal_satisfied) is not bool or type(reason) is not str or not reason:
        raise FourLaneBatchError("invalid lane outcome semantics")
    if type(child_result) not in {dict, type(None)}:
        raise FourLaneBatchError("lane child result is not an object or null")
    before_state = None if before is None else before["state"]
    after_state = None if after is None else after["state"]
    before_claimed = None if before is None else before["terminal_claimed"]
    before_committed = None if before is None else before["terminal_committed"]
    after_claimed = None if after is None else after["terminal_claimed"]
    after_committed = None if after is None else after["terminal_committed"]
    normalized_state = after_state if after_state is not None else before_state
    if normalized_state is None and type(child_result) is dict:
        candidate = child_result.get("state")
        normalized_state = candidate if candidate in TRANSPORT_STATES else None
    child_sha = (
        None if child_result is None else canonical_sha256(child_result)
    )
    success = bool(
        goal_satisfied and disposition in GOAL_DISPOSITIONS
        and error_type is None and error_message is None
    )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "lane_index": lane["lane_index"],
        "global_leaf_index": lane["global_leaf_index"],
        "cpu": lane["cpu"],
        "action_sequence": sequence,
        "claim_sha256": claim_sha256,
        "action": action,
        "success": success,
        "disposition": disposition,
        "disposition_reason": reason,
        "goal_satisfied": goal_satisfied,
        "transport_state_before": before_state,
        "transport_state_after": after_state,
        "terminal_claimed_before": before_claimed,
        "terminal_committed_before": before_committed,
        "terminal_claimed_after": after_claimed,
        "terminal_committed_after": after_committed,
        "child_result": child_result,
        "child_result_kind": (
            None if child_result is None else child_result.get("kind")
        ),
        "child_result_state": normalized_state,
        "child_result_sha256": child_sha,
        "error_type": error_type,
        "error_message": error_message,
        "scientific_claim": False,
    })


def _read_lane_outcome(
    path: Path, *, lane: Mapping[str, Any], action: str,
    sequence: int, claim_sha256: str,
) -> dict[str, Any]:
    outcome, _ = _read_canonical_json(path)
    fields = {
        "schema_version", "lane_index", "global_leaf_index", "cpu",
        "action_sequence", "claim_sha256", "action", "success",
        "disposition", "disposition_reason", "goal_satisfied",
        "transport_state_before", "transport_state_after",
        "terminal_claimed_before", "terminal_committed_before",
        "terminal_claimed_after", "terminal_committed_after",
        "child_result", "child_result_kind", "child_result_state",
        "child_result_sha256", "error_type", "error_message",
        "scientific_claim", "record_sha256",
    }
    child_result = outcome.get("child_result")
    child_sha = (
        None if child_result is None
        else canonical_sha256(child_result) if type(child_result) is dict
        else ""
    )
    disposition = outcome.get("disposition")
    goal = outcome.get("goal_satisfied")
    expected_success = bool(
        goal is True and disposition in GOAL_DISPOSITIONS
        and outcome.get("error_type") is None
        and outcome.get("error_message") is None
    )
    states = {
        outcome.get("transport_state_before"),
        outcome.get("transport_state_after"),
        outcome.get("child_result_state"),
    }
    if (
        set(outcome) != fields
        or not selfhash_valid(outcome)
        or outcome.get("schema_version") != SCHEMA_VERSION
        or outcome.get("lane_index") != lane["lane_index"]
        or outcome.get("global_leaf_index") != lane["global_leaf_index"]
        or outcome.get("cpu") != lane["cpu"]
        or outcome.get("action_sequence") != sequence
        or outcome.get("claim_sha256") != claim_sha256
        or outcome.get("action") != action
        or disposition not in LANE_DISPOSITIONS
        or type(outcome.get("disposition_reason")) is not str
        or not outcome["disposition_reason"]
        or type(goal) is not bool
        or goal is not (disposition in GOAL_DISPOSITIONS)
        or outcome.get("success") is not expected_success
        or (
            disposition == "FAILED"
            and (
                type(outcome.get("error_type")) is not str
                or not outcome["error_type"]
                or type(outcome.get("error_message")) is not str
                or not outcome["error_message"]
            )
        )
        or (
            disposition != "FAILED"
            and (
                outcome.get("error_type") is not None
                or outcome.get("error_message") is not None
            )
        )
        or any(state is not None and state not in TRANSPORT_STATES for state in states)
        or any(
            value is not None and type(value) is not bool
            for value in (
                outcome.get("terminal_claimed_before"),
                outcome.get("terminal_committed_before"),
                outcome.get("terminal_claimed_after"),
                outcome.get("terminal_committed_after"),
            )
        )
        or type(child_result) not in {dict, type(None)}
        or outcome.get("child_result_sha256") != child_sha
        or outcome.get("child_result_kind")
        != (None if child_result is None else child_result.get("kind"))
        or outcome.get("scientific_claim") is not False
    ):
        raise FourLaneBatchError("lane action outcome schema or binding mismatch")
    return outcome


def _disposition_counts(outcomes: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {
        disposition: sum(
            item.get("disposition") == disposition for item in outcomes
        )
        for disposition in sorted(LANE_DISPOSITIONS)
    }


def _action_result(
    root: Path, manifest: Mapping[str, Any], claim: Mapping[str, Any],
    outcomes: Sequence[Mapping[str, Any]], *, resumed_incomplete_action: bool,
) -> dict[str, Any]:
    dispositions = _disposition_counts(outcomes)
    goal_count = sum(item.get("goal_satisfied") is True for item in outcomes)
    all_goal = len(outcomes) == LANES_PER_BATCH and goal_count == len(outcomes)
    all_succeeded = all(item.get("success") is True for item in outcomes)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-four-lane-action-result-v1",
        "gate": GATE,
        "root": str(root),
        "batch_manifest_sha256": manifest["record_sha256"],
        "batch_index": manifest["batch"]["batch_index"],
        "action_sequence": claim["action_sequence"],
        "action": claim["action"],
        "claim_sha256": claim["record_sha256"],
        "previous_action_result_sha256": claim[
            "previous_action_result_sha256"
        ],
        "lane_outcome_sha256s": [
            item["record_sha256"] for item in outcomes
        ],
        "succeeded_lane_count": sum(
            item.get("success") is True for item in outcomes
        ),
        "failed_lane_count": sum(
            item.get("success") is False for item in outcomes
        ),
        "all_lanes_succeeded": all_succeeded,
        "goal_satisfied_lane_count": goal_count,
        "pending_lane_count": dispositions["PENDING"],
        "skipped_lane_count": dispositions["SKIPPED"],
        "unresolved_lane_count": dispositions["UNRESOLVED"],
        "hard_failed_lane_count": dispositions["FAILED"],
        "disposition_counts": dispositions,
        "all_lanes_goal_satisfied": all_goal,
        "resumed_incomplete_action": resumed_incomplete_action,
        "action_history_complete": True,
        "atomic": False,
        "authority": manifest["authority"],
        "production_eligible": False,
        "scientific_claim": False,
    })


def _read_action_result(
    path: Path, *, root: Path, manifest: Mapping[str, Any],
    claim: Mapping[str, Any], outcomes: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    result, _ = _read_canonical_json(path)
    resumed = result.get("resumed_incomplete_action")
    if type(resumed) is not bool:
        raise FourLaneBatchError("action result resume marker is invalid")
    expected = _action_result(
        root, manifest, claim, outcomes,
        resumed_incomplete_action=resumed,
    )
    if not static_v1.json_type_equal(result, expected):
        raise FourLaneBatchError("action result schema or outcome chain mismatch")
    return result


def _action_directories(
    root: Path, manifest: Mapping[str, Any],
) -> tuple[list[Path], Path | None]:
    entries = sorted((root / ACTIONS).iterdir(), key=lambda path: path.name)
    completed: list[Path] = []
    incomplete: Path | None = None
    previous_sha: str | None = None
    for index, path in enumerate(entries):
        if path.name != f"{index:06d}" or path.is_symlink() or not path.is_dir():
            raise FourLaneBatchError(
                "action history is missing, duplicated, or reordered"
            )
        _recover_action_publish_temps(path)
        contents = list(path.iterdir())
        if any(item.name not in ACTION_RECORD_NAMES for item in contents):
            raise FourLaneBatchError("action directory contains an unknown entry")
        if not contents:
            if index != len(entries) - 1 or incomplete is not None:
                raise FourLaneBatchError(
                    "only the unique final action may be incomplete"
                )
            incomplete = path
            continue
        claim = _read_action_claim(
            path / "claim.json", root=root, manifest=manifest,
            sequence=index, previous_sha=previous_sha,
        )
        outcomes: list[dict[str, Any]] = []
        for lane in manifest["lanes"]:
            lane_index = lane["lane_index"]
            outcome_path = path / f"lane-{lane_index}.json"
            if outcome_path.exists():
                outcomes.append(_read_lane_outcome(
                    outcome_path, lane=lane, action=claim["action"],
                    sequence=index, claim_sha256=claim["record_sha256"],
                ))
        result_path = path / "result.json"
        if result_path.exists():
            if len(outcomes) != LANES_PER_BATCH:
                raise FourLaneBatchError(
                    "completed action is missing a lane outcome"
                )
            result = _read_action_result(
                result_path, root=root, manifest=manifest,
                claim=claim, outcomes=outcomes,
            )
            completed.append(path)
            previous_sha = result["record_sha256"]
            continue
        if index != len(entries) - 1 or incomplete is not None:
            raise FourLaneBatchError(
                "only the unique final action may be incomplete"
            )
        incomplete = path
    return completed, incomplete


def _action_callable(action: str) -> Callable[..., dict[str, Any]]:
    mapping = {
        "start": child_runner.start_root,
        "checkpoint-stop": child_runner.checkpoint_stop_root,
        "resume": child_runner.resume_root,
        "status": child_runner.status_root,
        "verify-checkpoint": child_runner.verify_checkpoint_root,
        "harvest-inactive": child_runner.harvest_inactive_root,
    }
    try:
        return mapping[action]
    except KeyError as exc:
        raise FourLaneBatchError(f"unsupported batch action: {action}") from exc


def _invoke_lane_action(
    action: str, action_function: Callable[..., dict[str, Any]],
    lane_root: Path, cpu: int, static_kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    if action in AFFINITY_ACTIONS:
        with _singleton_affinity(cpu):
            value = action_function(lane_root, **dict(static_kwargs))
    else:
        value = action_function(lane_root, **dict(static_kwargs))
    if type(value) is not dict:
        raise FourLaneBatchError("child runner returned a non-object")
    return value


def _lane_status(
    lane_root: Path, static_kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    return _normalized_status(
        child_runner.status_root(lane_root, **dict(static_kwargs))
    )


def _verified_final_root(
    lane_root: Path, static_kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    value = child_runner.verify_final_root(
        lane_root, **dict(static_kwargs)
    )
    if (
        type(value) is not dict
        or set(value) != child_runner.FINAL_ROOT_ATTESTATION_FIELDS
        or not selfhash_valid(value)
        or value.get("schema_version")
        != child_runner.FINAL_ROOT_ATTESTATION_SCHEMA_VERSION
        or value.get("kind") != child_runner.FINAL_ROOT_ATTESTATION_KIND
        or value.get("root") != str(lane_root)
        or value.get("valid") is not True
        or value.get("failures") != []
        or value.get("proof_replay_decision_complete") is not True
        or value.get("strict_proof_unsat") is not True
    ):
        raise FourLaneBatchError("fresh final-root attestation is invalid")
    return value


def _dispatch_lane_action(
    *, lane: Mapping[str, Any], action: str, sequence: int,
    claim_sha256: str, action_function: Callable[..., dict[str, Any]],
    static_kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    lane_root = Path(lane["child_root"])
    cpu = lane["cpu"]
    if action == "start":
        session_exists = (lane_root / child_runner.SESSION_COMMIT).exists()
        start_claim_exists = (lane_root / child_runner.START_CLAIM).exists()
        if session_exists:
            observed = _lane_status(lane_root, static_kwargs)
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="SKIPPED",
                reason="ALREADY_STARTED", goal_satisfied=True,
                before=observed, after=observed,
                child_result=observed["value"],
            )
        if start_claim_exists:
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="FAILED",
                reason="START_STAGE_INCOMPLETE", goal_satisfied=False,
                before=None, after=None, child_result=None,
                error_type="StartStageIncomplete",
                error_message="start claim exists without a session commit",
            )
        value = _invoke_lane_action(
            action, action_function, lane_root, cpu, static_kwargs,
        )
        after = _lane_status(lane_root, static_kwargs)
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="APPLIED",
            reason="START_APPLIED", goal_satisfied=True,
            before=None, after=after, child_result=value,
        )

    before = _lane_status(lane_root, static_kwargs)
    if action == "status":
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="OBSERVED",
            reason="STATUS_OBSERVED", goal_satisfied=True,
            before=before, after=before, child_result=before["value"],
        )
    if before["terminal_claimed"] and not before["terminal_committed"]:
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="FAILED",
            reason="TERMINAL_STAGE_INCOMPLETE", goal_satisfied=False,
            before=before, after=before, child_result=before["value"],
            error_type="TerminalStageIncomplete",
            error_message="terminal claim exists without a final commit",
        )
    if before["terminal_committed"]:
        attestation = _verified_final_root(lane_root, static_kwargs)
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="SKIPPED",
            reason="ALREADY_FINAL", goal_satisfied=True,
            before=before, after=before, child_result=attestation,
        )

    state = before["state"]
    if action == "harvest-inactive" and state != "INACTIVE_UNCHECKPOINTED":
        reason = (
            "WAITING_FOR_INACTIVE"
            if state == "RUNNING"
            else "CHECKPOINTED_REQUIRES_VERIFY_CHECKPOINT"
        )
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="PENDING",
            reason=reason, goal_satisfied=False,
            before=before, after=before, child_result=before["value"],
        )
    if action == "verify-checkpoint" and state != "CHECKPOINTED":
        reason = (
            "WAITING_FOR_CHECKPOINT"
            if state == "RUNNING"
            else "INACTIVE_REQUIRES_HARVEST"
        )
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="PENDING",
            reason=reason, goal_satisfied=False,
            before=before, after=before, child_result=before["value"],
        )
    if action == "checkpoint-stop":
        if state == "CHECKPOINTED":
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="SKIPPED",
                reason="ALREADY_CHECKPOINTED", goal_satisfied=True,
                before=before, after=before, child_result=before["value"],
            )
        if state == "INACTIVE_UNCHECKPOINTED":
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="UNRESOLVED",
                reason="INACTIVE_NOT_CHECKPOINTABLE", goal_satisfied=False,
                before=before, after=before, child_result=before["value"],
            )
    if action == "resume":
        if state == "RUNNING":
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="SKIPPED",
                reason="ALREADY_RUNNING", goal_satisfied=True,
                before=before, after=before, child_result=before["value"],
            )
        if state == "INACTIVE_UNCHECKPOINTED":
            return _make_lane_outcome(
                lane=lane, action=action, sequence=sequence,
                claim_sha256=claim_sha256, disposition="UNRESOLVED",
                reason="INACTIVE_NOT_RESUMABLE", goal_satisfied=False,
                before=before, after=before, child_result=before["value"],
            )

    value = _invoke_lane_action(
        action, action_function, lane_root, cpu, static_kwargs,
    )
    after = _lane_status(lane_root, static_kwargs)
    if action == "checkpoint-stop":
        satisfied = after["state"] == "CHECKPOINTED"
    elif action == "resume":
        satisfied = after["state"] == "RUNNING"
    elif action in {"verify-checkpoint", "harvest-inactive"}:
        satisfied = after["terminal_committed"]
    else:
        satisfied = False
    if satisfied:
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="APPLIED",
            reason=f"{action.upper().replace(chr(45), chr(95))}_APPLIED",
            goal_satisfied=True, before=before, after=after,
            child_result=value,
        )
    if (
        action in {"verify-checkpoint", "harvest-inactive"}
        and value.get("drat_verified") is False
        and not after["terminal_claimed"]
        and not after["terminal_committed"]
    ):
        return _make_lane_outcome(
            lane=lane, action=action, sequence=sequence,
            claim_sha256=claim_sha256, disposition="UNRESOLVED",
            reason="DRAT_PREFLIGHT_UNRESOLVED", goal_satisfied=False,
            before=before, after=after, child_result=value,
        )
    return _make_lane_outcome(
        lane=lane, action=action, sequence=sequence,
        claim_sha256=claim_sha256, disposition="FAILED",
        reason="ACTION_POSTCONDITION_FAILED", goal_satisfied=False,
        before=before, after=after, child_result=value,
        error_type="ActionPostconditionFailed",
        error_message="child action returned without reaching its required state",
    )


def run_batch_action(
    root: Path, action: str, *, instance: Any | None = None,
    strict_base: bool | None = None,
) -> dict[str, Any]:
    if action not in ACTION_NAMES:
        raise FourLaneBatchError(f"unsupported batch action: {action}")
    target = Path(root)
    with _batch_lock(target):
        loaded = _load_batch(target, instance=instance, strict_base=strict_base)
        manifest = loaded["manifest"]
        history, incomplete = _action_directories(target, manifest)
        previous_sha = None
        if history:
            previous, _ = _read_canonical_json(history[-1] / "result.json")
            previous_sha = previous["record_sha256"]
        resumed_incomplete = incomplete is not None
        if incomplete is None:
            sequence = len(history)
            action_dir = _mkdir(target / ACTIONS, f"{sequence:06d}")
            claim = _action_claim(
                target, manifest, sequence=sequence,
                action=action, previous_sha=previous_sha,
            )
            _publish_action_json(action_dir / "claim.json", claim)
        else:
            action_dir = incomplete
            sequence = int(action_dir.name)
            claim_path = action_dir / "claim.json"
            if not claim_path.exists():
                if any(action_dir.iterdir()):
                    raise FourLaneBatchError(
                        "claimless incomplete action contains residual state"
                    )
                claim = _action_claim(
                    target, manifest, sequence=sequence,
                    action=action, previous_sha=previous_sha,
                )
                _publish_action_json(claim_path, claim)
            else:
                claim = _read_action_claim(
                    claim_path, root=target, manifest=manifest,
                    sequence=sequence, previous_sha=previous_sha,
                )
                if claim["action"] != action:
                    raise FourLaneBatchError(
                        "incomplete action {} must be resumed first".format(
                            claim["action"]
                        )
                    )

        action_function = _action_callable(action)
        outcomes: list[dict[str, Any]] = []
        for lane in manifest["lanes"]:
            lane_index = lane["lane_index"]
            outcome_path = action_dir / f"lane-{lane_index}.json"
            if outcome_path.exists():
                outcome = _read_lane_outcome(
                    outcome_path, lane=lane, action=action,
                    sequence=sequence, claim_sha256=claim["record_sha256"],
                )
                outcomes.append(outcome)
                continue
            try:
                outcome = _dispatch_lane_action(
                    lane=lane, action=action, sequence=sequence,
                    claim_sha256=claim["record_sha256"],
                    action_function=action_function,
                    static_kwargs=loaded["static_kwargs"],
                )
            except Exception as exc:
                outcome = _make_lane_outcome(
                    lane=lane, action=action, sequence=sequence,
                    claim_sha256=claim["record_sha256"],
                    disposition="FAILED", reason="CHILD_ACTION_EXCEPTION",
                    goal_satisfied=False, before=None, after=None,
                    child_result=None, error_type=type(exc).__name__,
                    error_message=str(exc)[:4096],
                )
            _publish_action_json(outcome_path, outcome)
            outcomes.append(outcome)

        result = _action_result(
            target, manifest, claim, outcomes,
            resumed_incomplete_action=resumed_incomplete,
        )
        _publish_action_json(action_dir / "result.json", result)
        return result


def _caps_from_args(args: argparse.Namespace) -> dict[str, int]:
    return {
        "proof_max_bytes": args.proof_max_bytes,
        "checkpoint_image_max_bytes": args.checkpoint_image_max_bytes,
        "checkpoint_images_per_generation_max": args.checkpoint_images_per_generation_max,
        "checkpoint_generation_max_count": args.checkpoint_generation_max_count,
        "checkpoint_generation_metadata_max_bytes": args.checkpoint_generation_metadata_max_bytes,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    prepare = sub.add_parser("prepare", allow_abbrev=False)
    prepare.add_argument("--root", type=Path, required=True)
    prepare.add_argument("--width10-campaign", type=Path, required=True)
    prepare.add_argument("--width6-campaign", type=Path, required=True)
    prepare.add_argument("--parent-manifest", type=Path, required=True)
    prepare.add_argument("--parent-cube-index", type=int, required=True)
    prepare.add_argument("--batch-index", type=int, required=True)
    prepare.add_argument("--cpus", type=int, nargs=LANES_PER_BATCH, required=True)
    prepare.add_argument("--proof-max-bytes", type=int, required=True)
    prepare.add_argument("--checkpoint-image-max-bytes", type=int, required=True)
    prepare.add_argument("--checkpoint-images-per-generation-max", type=int, required=True)
    prepare.add_argument("--checkpoint-generation-max-count", type=int, required=True)
    prepare.add_argument("--checkpoint-generation-metadata-max-bytes", type=int, required=True)
    for action in sorted(ACTION_NAMES):
        child = sub.add_parser(action, allow_abbrev=False)
        child.add_argument("--root", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "prepare":
        result = prepare_batch(
            args.root,
            width10_campaign_manifest_path=args.width10_campaign,
            width6_campaign_manifest_path=args.width6_campaign,
            parent_manifest_path=args.parent_manifest,
            parent_cube_index=args.parent_cube_index,
            batch_index=args.batch_index,
            cpus=args.cpus,
            resource_caps=_caps_from_args(args),
            strict_base=True,
        )
    else:
        result = run_batch_action(args.root, args.action, strict_base=True)
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0 if result.get("all_lanes_succeeded", True) is True else 3


if __name__ == "__main__":
    try:
        _exit = main()
    except (
        FourLaneBatchError, nested.NestedWidth10CampaignError,
        nested.width6.WidenedParentCampaignError,
        nested.hierarchy.HierarchicalCubeError, static_v1.ResumeStaticError,
        child_runner.HierarchicalResumeRunnerError, OSError, ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        _exit = 2
    raise SystemExit(_exit)


__all__ = [
    "ACTION_NAMES", "AFFINITY_ACTIONS", "AUTHORITY_COVER_TRANSPORT",
    "AUTHORITY_SYNTHETIC", "BATCH_FIELDS", "FourLaneBatchError", "GATE",
    "KIND", "SCHEMA_VERSION", "build_parser", "canonical_bytes",
    "canonical_sha256", "main", "prepare_batch", "run_batch_action",
    "seal", "selfhash_valid",
]
