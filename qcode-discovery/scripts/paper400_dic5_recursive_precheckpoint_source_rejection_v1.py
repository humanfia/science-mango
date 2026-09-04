#!/usr/bin/env python3
"""Reject a pristine recursive admission with an inexact legacy-source bind.

``create-bundle`` reserves child CPU leases before it asks the frozen legacy
runner to checkpoint the parent.  That ordering is intentional: no parent is
stopped until its exact split, queue, and CPU leases are durable.  It also
means a source-path mismatch discovered at checkpoint time must not silently
strand leases forever.

This narrowly scoped recovery never deletes a bundle or touches a parent
solver.  It applies only when the bundle is still pristine (no checkpoint,
workers, child roots, or queue transition), the parent is provably still its
original live r5 generation, and the bundle recorded the r4 legacy runner
despite the parent's r5 absolute tool-path binding.  It first seals a durable
rejection receipt, then releases only that bundle's scheduler leases.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import os
import stat
import sys
import time
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_r5_legacy_adapter_v1 as adapter
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-precheckpoint-source-rejection-v1"
REJECTION_KIND = "paper400-dic5-recursive-precheckpoint-source-rejection-v1"
REASON = "R5_STATIC_TOOLCHAIN_PATH_REJECTS_R4_LEGACY_RUNNER"
SIDECAR = Path("precheckpoint-source-rejection-v1")
REJECTION = SIDECAR / "000000-rejection.json"
LOCK = Path(".precheckpoint-source-rejection-v1.lock")


class PrecheckpointSourceRejectionError(RuntimeError):
    """The bundle is not eligible for the narrow no-delete rejection path."""


def _script_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "rejection_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "r5_adapter": adapter.adapter_source_binding(),
        "frozen_supervisor": supervisor._legacy_source_binding(),
    }


@contextlib.contextmanager
def _bundle_lock(bundle: Path) -> Iterator[None]:
    path = bundle / LOCK
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise PrecheckpointSourceRejectionError("cannot open source-rejection lock") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise PrecheckpointSourceRejectionError("source-rejection lock metadata is unsafe")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise PrecheckpointSourceRejectionError("another source-rejection action is active") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


@contextlib.contextmanager
def _legacy_shared_lock(root: Path) -> Iterator[None]:
    path = root / ".hierarchical-resume.lock"
    try:
        fd = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise PrecheckpointSourceRejectionError("legacy root lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise PrecheckpointSourceRejectionError("legacy root lock metadata is unsafe")
        try:
            fcntl.flock(fd, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise PrecheckpointSourceRejectionError("legacy root is busy; defer source rejection") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _safe_sidecar(bundle: Path) -> Path:
    target = bundle / SIDECAR
    if target.exists() or target.is_symlink():
        return supervisor._safe_directory(target, require_mode_0700=True)
    try:
        os.mkdir(target, 0o700)
        supervisor._fsync_dir(bundle)
    except OSError as exc:
        raise PrecheckpointSourceRejectionError("cannot create source-rejection sidecar") from exc
    return supervisor._safe_directory(target, require_mode_0700=True)


def _require_pristine_queue(loaded: Mapping[str, Any]) -> None:
    bundle = Path(loaded["root"])
    queue = loaded["queue"]
    committed = loaded["bundle"]
    if (
        queue.get("queue_sha256") != committed.get("queue_sha256")
        or queue.get("status") != recursive.QUEUE_STATUS_OPEN
        or queue.get("event_sequence") != 0
        or type(queue.get("items")) is not list
    ):
        raise PrecheckpointSourceRejectionError("recursive queue is no longer pristine")
    for item in queue["items"]:
        if (
            type(item) is not dict
            or item.get("state") != "PENDING"
            or item.get("claim") is not None
            or item.get("attempts") != 0
            or item.get("cpu_ids") != []
        ):
            raise PrecheckpointSourceRejectionError("recursive queue has a child transition")
    for name in (supervisor.WORKERS_DIR, supervisor.CHILDREN_DIR):
        directory = supervisor._safe_directory(bundle / name, require_mode_0700=True)
        if any(directory.iterdir()):
            raise PrecheckpointSourceRejectionError("child evidence exists before source rejection")
    forbidden = (
        supervisor.PARENT_CHECKPOINT,
        supervisor.PARENT_AGGREGATE,
        Path("initial-batch-dispatch-v1"),
        Path("queue-progress"),
    )
    present = [str(path) for path in forbidden if (bundle / path).exists() or (bundle / path).is_symlink()]
    if present:
        raise PrecheckpointSourceRejectionError(
            f"bundle has post-admission evidence: {present}"
        )


def _require_recorded_r4_for_r5_parent(loaded: Mapping[str, Any]) -> None:
    binding = loaded["bundle"].get("source_binding")
    if not supervisor._same(binding, supervisor._legacy_source_binding()):
        raise PrecheckpointSourceRejectionError("bundle source binding is not the exact frozen r4 binding")
    sources = binding.get("sources") if type(binding) is dict else None
    legacy = sources.get("legacy_runner") if type(sources) is dict else None
    if (
        type(legacy) is not dict
        or legacy.get("path") != str(supervisor.LEGACY_RUNNER)
        or legacy.get("sha256") != supervisor.LEGACY_RUNNER_SHA256
    ):
        raise PrecheckpointSourceRejectionError("bundle does not record the frozen r4 legacy runner")
    adapter.validate_r5_static_root(Path(loaded["audit"]["parent_root"]))


def _require_reserved_catalog_leases(loaded: Mapping[str, Any]) -> None:
    reservation = loaded["reservation"]
    cpus = reservation.get("cpus")
    if type(cpus) is not list or any(type(cpu) is not int for cpu in cpus):
        raise PrecheckpointSourceRejectionError("reservation CPU list is malformed")
    catalog = supervisor._load_catalog(Path(loaded["control_root"]))
    matches = [
        entry for entry in catalog["leases"]
        if entry.get("reservation_sha256") == reservation.get("reservation_sha256")
    ]
    if (
        len(matches) != len(cpus)
        or {entry.get("cpu") for entry in matches} != set(cpus)
        or any(entry.get("state") != "RESERVED" for entry in matches)
    ):
        raise PrecheckpointSourceRejectionError("bundle no longer owns its exact reserved CPU leases")


def _verify_original_live_r5_parent(loaded: Mapping[str, Any]) -> dict[str, Any]:
    audit = loaded["audit"]
    root = Path(audit["parent_root"])
    with _legacy_shared_lock(root), adapter.r5_legacy_context():
        supervisor._legacy_terminal_absent(root)
        static, session, payload, status, proc = supervisor._legacy_parent_material(root)
    if (
        static.get("record_sha256") != audit.get("parent_static_sha256")
        or session.get("record_sha256") != audit.get("parent_session_sha256")
        or hashlib.sha256(payload).hexdigest() != audit.get("parent_dimacs_sha256")
        or len(payload) != audit.get("parent_dimacs_bytes")
        or proc.get("pid") != audit.get("parent_pid")
        or proc.get("proc_start_ticks") != audit.get("parent_proc_start_ticks")
    ):
        raise PrecheckpointSourceRejectionError("r5 parent identity changed after invalid admission")
    return {
        "controller_status_sha256": recursive.canonical_sha256(status),
        "pid": proc["pid"],
        "proc_start_ticks": proc["proc_start_ticks"],
        "cpu_seconds": proc["cpu_seconds"],
        "state": proc["state"],
    }


def _rejection_value(loaded: Mapping[str, Any], parent: Mapping[str, Any]) -> dict[str, Any]:
    audit = loaded["audit"]
    reservation = loaded["reservation"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": REJECTION_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "parent_root": audit["parent_root"],
            "parent_static_sha256": audit["parent_static_sha256"],
            "parent_session_sha256": audit["parent_session_sha256"],
            "parent_pid": audit["parent_pid"],
            "parent_proc_start_ticks": audit["parent_proc_start_ticks"],
            "parent_observation": dict(parent),
            "queue_sha256": loaded["queue"]["queue_sha256"],
            "reservation_sha256": reservation["reservation_sha256"],
            "reserved_cpus": list(reservation["cpus"]),
            "reason": REASON,
            "checkpoint_not_attempted_again": True,
            "children_started": False,
            "parent_checkpoint_exists": False,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _script_binding(),
            "created_at": time.time(),
        },
        "record_sha256",
    )


def _validate_existing_rejection(value: Mapping[str, Any], loaded: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "schema_version", "kind", "gate", "bundle_sha256", "parent_root",
        "parent_static_sha256", "parent_session_sha256", "parent_pid",
        "parent_proc_start_ticks", "parent_observation", "queue_sha256",
        "reservation_sha256", "reserved_cpus", "reason",
        "checkpoint_not_attempted_again", "children_started", "parent_checkpoint_exists",
        "hardness_only", "solver_terminal_claim", "source_binding", "created_at",
        "record_sha256",
    }
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != REJECTION_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("queue_sha256") != loaded["queue"].get("queue_sha256")
        or value.get("reservation_sha256") != loaded["reservation"].get("reservation_sha256")
        or value.get("reserved_cpus") != loaded["reservation"].get("cpus")
        or value.get("reason") != REASON
        or value.get("checkpoint_not_attempted_again") is not True
        or value.get("children_started") is not False
        or value.get("parent_checkpoint_exists") is not False
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
    ):
        raise PrecheckpointSourceRejectionError("existing rejection receipt is malformed")
    return dict(value)


def reject_precheckpoint_source_mismatch(
    bundle: Path | str, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Seal a narrow rejection receipt, then idempotently release its leases."""

    target = Path(bundle)
    control = Path(control_root)
    with _bundle_lock(target):
        loaded = supervisor._load_bundle(target, control_root=control)
        sidecar = _safe_sidecar(Path(loaded["root"]))
        receipt_path = sidecar / REJECTION.name
        if receipt_path.exists() or receipt_path.is_symlink():
            receipt = _validate_existing_rejection(supervisor._read_json(receipt_path), loaded)
        else:
            _require_pristine_queue(loaded)
            _require_recorded_r4_for_r5_parent(loaded)
            _require_reserved_catalog_leases(loaded)
            parent = _verify_original_live_r5_parent(loaded)
            receipt = _rejection_value(loaded, parent)
            supervisor._publish_json(receipt_path, receipt)
        supervisor._release_cpus(Path(loaded["control_root"]), loaded["reservation"])
        return receipt


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    reject = sub.add_parser("reject", allow_abbrev=False)
    reject.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action != "reject":  # pragma: no cover - argparse guards this
        raise PrecheckpointSourceRejectionError("unsupported action")
    value = reject_precheckpoint_source_mismatch(
        args.bundle, control_root=args.control_root,
    )
    sys.stdout.buffer.write(supervisor.canonical_bytes(value) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        PrecheckpointSourceRejectionError,
        adapter.R5LegacyAdapterError,
        supervisor.RecursiveSplitSupervisorError,
        recursive.RecursiveSplitError,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
