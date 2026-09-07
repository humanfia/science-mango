#!/usr/bin/env python3
"""Source-bound fanout-4 recovery adapter for inactive legacy c0084.

The frozen recursive supervisor admits only a live/checkpointed timeout
parent.  c0084 is a different, narrow state: its generation-zero solver is
gone, no checkpoint exists, and the same complete DRAT has crashed the pinned
checker at least 58 times.  This adapter leaves every frozen module unchanged
and supplies a process-local schema bridge for that one reviewed incident.

The bridge:

* holds the c0084 shared guard for every audit/publication/dispatch/tick;
* records checker crashes only as a nonterminal hardness trigger;
* builds and replays the ordinary complementary fanout-4 structural cover;
* reserves ordinary scheduler CPU leases and creates the ordinary queue;
* starts children through the trusted simultaneous initial-batch dispatcher;
* advances them through the trusted v3 lifecycle and fresh proof replay.

The old DRAT is never copied into a child, certified, aggregated, deleted, or
used as an UNSAT claim.  Only four fresh child certificates can make the
recursive aggregate terminal.  Merely importing or auditing this module does
not write, launch, signal, stop, deploy, or reserve anything.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import subprocess
import sys
import time
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_c0084_inactive_checker_crash_guard_v1 as root_guard
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as checkpoint_recovery
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial_dispatch
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v3 as lifecycle
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-c0084-inactive-checker-crash-recursive-split-v1"
AUDIT_KIND = "paper400-c0084-inactive-checker-crash-parent-audit-v1"
LEDGER_KIND = "paper400-c0084-checker-crash-hardness-ledger-v1"
EVIDENCE_KIND = "paper400-c0084-checker-crash-hardness-evidence-v1"
TRIGGER_KIND = "paper400-c0084-checker-crash-recursive-trigger-v1"
RETIREMENT_KIND = "paper400-c0084-inactive-parent-retirement-v1"
RESULT_KIND = "paper400-c0084-recursive-bundle-admission-v1"
TRIGGER_REASON = "DETERMINISTIC_PINNED_DRAT_CHECKER_SIGSEGV_THRESHOLD"
PARENT_ID = "paper400-p00-w10-c0084-g000000-crash-recovery-v1"
FANOUT = 4
DEFAULT_INTERVAL_SECONDS = 60.0


class C0084RecursiveSplitError(RuntimeError):
    """The incident admission, structural cover, or trusted bridge changed."""


_ACTIVE_ADMISSION: tuple[Path, str, str] | None = None
_FROZEN_INITIAL_SOURCE_BINDING = initial_dispatch._source_binding


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _same(left: Any, right: Any) -> bool:
    return type(left) is type(right) and _canonical(left) == _canonical(right)


def _binding(path: Path) -> dict[str, Any]:
    target = Path(path).resolve(strict=True)
    payload = supervisor._stable_bytes(
        target, cap=32 << 20, executable=False,
    )
    return {
        "path": str(target), "bytes": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def _source_binding(
    admission_path: Path, admission_file_sha256: str,
    admission_record_sha256: str,
) -> dict[str, Any]:
    return {
        "method": "exact-source-sha256-replay-v1",
        "adapter": _binding(Path(__file__)),
        "root_guard": _binding(Path(root_guard.__file__)),
        "recursive_split": _binding(Path(recursive.__file__)),
        "recursive_supervisor": _binding(Path(supervisor.__file__)),
        "recursive_child_runner": _binding(Path(supervisor.child_runner.__file__)),
        "initial_batch_dispatch": _binding(Path(initial_dispatch.__file__)),
        "initial_batch_lifecycle_v3": _binding(Path(lifecycle.__file__)),
        "checkpoint_recovery": _binding(Path(checkpoint_recovery.__file__)),
        "admission": {
            "path": str(Path(admission_path)),
            "file_sha256": admission_file_sha256,
            "record_sha256": admission_record_sha256,
        },
    }


def _active() -> tuple[Path, str, str]:
    if _ACTIVE_ADMISSION is None:
        raise C0084RecursiveSplitError("c0084 adapter runtime is not active")
    return _ACTIVE_ADMISSION


def _active_source_binding() -> dict[str, Any]:
    path, file_sha, record_sha = _active()
    return _source_binding(path, file_sha, record_sha)


def _initial_source_binding() -> dict[str, Any]:
    """Bind the frozen initial transaction plus our external-start wrapper."""

    return {
        "method": "exact-source-sha256-replay-v1",
        "c0084_adapter": _active_source_binding(),
        "frozen_initial_batch_dispatch": _FROZEN_INITIAL_SOURCE_BINDING(),
        "child_start_transport": "c0084-adapter-child-start-subprocess-v1",
    }


def _spawn_adapter_child_start(
    child_root: Path, *, cpu: int,
) -> subprocess.Popen[bytes]:
    admission_path, admission_sha, _record_sha = _active()
    script = Path(__file__).resolve(strict=True)
    return subprocess.Popen(
        [
            str(Path(sys.executable).resolve(strict=True)), str(script),
            "child-start", "--admission", str(admission_path),
            "--admission-sha256", admission_sha,
            "--root", str(child_root), "--cpu", str(cpu),
        ],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        close_fds=True,
    )


def _load_admission_identity(path: Path, file_sha256: str) -> dict[str, Any]:
    held = None
    try:
        held, value = root_guard._load_admission(path, file_sha256)
        return dict(value)
    finally:
        root_guard.quarantine._close_path(held)


def _normalize_crash_trigger(trigger: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(trigger)
    fields = {
        "kind", "reason", "observed_state", "minimum_attempts",
        "total_attempts", "signal", "same_proof_cube_checker",
        "proof_sha256", "cube_sha256", "checker_sha256",
        "admission_record_sha256", "evidence_sha256", "hardness_only",
        "solver_terminal_claim", "unsat_claim", "old_proof_certified",
        "trigger_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "trigger_sha256")
        or value.get("kind") != TRIGGER_KIND
        or value.get("reason") != TRIGGER_REASON
        or value.get("observed_state") != "INACTIVE"
        or value.get("minimum_attempts") != root_guard.MINIMUM_SIGSEGV_ATTEMPTS
        or type(value.get("total_attempts")) is not int
        or value["total_attempts"] < value["minimum_attempts"]
        or value.get("signal") != 11
        or value.get("same_proof_cube_checker") is not True
        or any(
            not recursive.is_sha256(value.get(field))
            for field in (
                "proof_sha256", "cube_sha256", "checker_sha256",
                "admission_record_sha256", "evidence_sha256",
            )
        )
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("unsat_claim") is not False
        or value.get("old_proof_certified") is not False
    ):
        raise C0084RecursiveSplitError(
            "recursive manifest trigger is not exact nonterminal crash evidence"
        )
    return value


def _validate_parent_audit(audit: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(audit)
    required = {
        "schema_version", "kind", "parent_root", "parent_root_identity",
        "parent_static_sha256", "parent_session_sha256",
        "parent_dimacs_sha256", "parent_dimacs_bytes", "parent_generation",
        "parent_pid", "parent_proc_start_ticks", "observed_state",
        "timing_ledger", "timing_evidence", "timing_trigger",
        "split_allowed", "hardness_only", "solver_terminal_claim",
        "source_binding", "audit_sha256",
    }
    ledger = value.get("timing_ledger")
    evidence = value.get("timing_evidence")
    trigger = value.get("timing_trigger")
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "audit_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != AUDIT_KIND
        or value.get("parent_root") != str(root_guard.EXPECTED_ROOT)
        or not _same(
            value.get("parent_root_identity"),
            supervisor._root_identity(root_guard.EXPECTED_ROOT),
        )
        or any(
            not recursive.is_sha256(value.get(field))
            for field in (
                "parent_static_sha256", "parent_session_sha256",
                "parent_dimacs_sha256",
            )
        )
        or type(value.get("parent_dimacs_bytes")) is not int
        or value["parent_dimacs_bytes"] <= 0
        or value.get("parent_generation") != 0
        or type(value.get("parent_pid")) is not int
        or value["parent_pid"] <= 0
        or type(value.get("parent_proc_start_ticks")) is not int
        or value["parent_proc_start_ticks"] < 0
        or value.get("observed_state") != "INACTIVE"
        or value.get("split_allowed") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or not _same(value.get("source_binding"), _active_source_binding())
        or type(ledger) is not dict
        or not recursive.selfhash_valid(ledger, "ledger_sha256")
        or ledger.get("kind") != LEDGER_KIND
        or ledger.get("hardness_only") is not True
        or ledger.get("solver_terminal_claim") is not False
        or ledger.get("unsat_claim") is not False
        or type(evidence) is not dict
        or not recursive.selfhash_valid(evidence, "evidence_sha256")
        or evidence.get("kind") != EVIDENCE_KIND
        or evidence.get("ledger_sha256") != ledger.get("ledger_sha256")
        or evidence.get("admission_threshold_met") is not True
        or evidence.get("hardness_only") is not True
        or evidence.get("solver_terminal_claim") is not False
        or evidence.get("unsat_claim") is not False
        or type(trigger) is not dict
    ):
        raise C0084RecursiveSplitError("c0084 inactive parent audit is malformed")
    normalized = _normalize_crash_trigger(trigger)
    if (
        normalized.get("evidence_sha256") != evidence.get("evidence_sha256")
        or normalized.get("admission_record_sha256")
        != _active()[2]
        or ledger.get("total_attempts") != normalized.get("total_attempts")
    ):
        raise C0084RecursiveSplitError("c0084 audit crash chain is inconsistent")
    return value


def _validate_retirement(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any],
) -> dict[str, Any]:
    audit = loaded["audit"]
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "parent_root",
        "parent_static_sha256", "parent_session_sha256", "parent_pid",
        "parent_proc_start_ticks", "parent_state",
        "admission_record_sha256", "checkpoint_created",
        "old_proof_certified", "hardness_only", "solver_terminal_claim",
        "source_binding", "record_sha256",
    }
    if (
        set(receipt) != fields
        or not recursive.selfhash_valid(receipt, "record_sha256")
        or receipt.get("schema_version") != SCHEMA_VERSION
        or receipt.get("kind") != RETIREMENT_KIND
        or receipt.get("gate") != GATE
        or receipt.get("bundle_sha256")
        != loaded["bundle"].get("bundle_sha256")
        or receipt.get("parent_root") != audit.get("parent_root")
        or receipt.get("parent_static_sha256")
        != audit.get("parent_static_sha256")
        or receipt.get("parent_session_sha256")
        != audit.get("parent_session_sha256")
        or receipt.get("parent_pid") != audit.get("parent_pid")
        or receipt.get("parent_proc_start_ticks")
        != audit.get("parent_proc_start_ticks")
        or receipt.get("parent_state")
        != "INACTIVE_CHECKER_CRASH_GUARDED"
        or receipt.get("admission_record_sha256") != _active()[2]
        or receipt.get("checkpoint_created") is not False
        or receipt.get("old_proof_certified") is not False
        or receipt.get("hardness_only") is not True
        or receipt.get("solver_terminal_claim") is not False
        or not _same(receipt.get("source_binding"), _active_source_binding())
    ):
        raise C0084RecursiveSplitError("inactive parent retirement receipt is malformed")
    return dict(receipt)


def _require_retirement(loaded: Mapping[str, Any]) -> dict[str, Any]:
    path = Path(loaded["root"]) / supervisor.PARENT_CHECKPOINT
    if not path.exists() or path.is_symlink():
        raise C0084RecursiveSplitError("inactive parent retirement receipt is absent")
    return _validate_retirement(loaded, supervisor._read_json(path))


def _checked_inactive_parent(
    loaded: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    receipt = _require_retirement(loaded)
    path, file_sha, _record_sha = _active()
    held = root_guard.acquire(path, file_sha)
    root_guard.close(held)
    observation = supervisor.seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-c0084-inactive-parent-observation-v1",
        "parent_root": str(root_guard.EXPECTED_ROOT),
        "state": "INACTIVE_CHECKER_CRASH_GUARDED",
        "pid_identity_alive": False,
        "checkpoint_created": False,
        "old_proof_certified": False,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "admission_record_sha256": _active()[2],
    }, "record_sha256")
    # The initial-batch code requires an immutable predecessor-chain digest.
    # For this adapter it is explicitly the retirement receipt, never a fake
    # DMTCP checkpoint manifest.
    chain = {
        "kind": "paper400-c0084-inactive-parent-chain-v1",
        "latest_checkpoint_sha256": receipt["record_sha256"],
        "checkpoint_created": False,
        "total_checkpoint_image_bytes": 0,
        "admission_record_sha256": _active()[2],
    }
    return observation, chain


def _inactive_parent_still_eligible(audit: Mapping[str, Any]) -> None:
    checked = _validate_parent_audit(audit)
    path, file_sha, _record_sha = _active()
    held = root_guard.acquire(path, file_sha)
    try:
        admission = root_guard._read_held_json(held.admission)
        if admission.get("record_sha256") != checked["source_binding"][
            "admission"
        ]["record_sha256"]:
            raise C0084RecursiveSplitError("inactive admission changed")
    finally:
        root_guard.close(held)


@contextlib.contextmanager
def _adapter_runtime(
    admission_path: Path, admission_file_sha256: str,
) -> Iterator[dict[str, Any]]:
    """Install a process-local schema bridge and restore every frozen symbol."""

    global _ACTIVE_ADMISSION
    if _ACTIVE_ADMISSION is not None:
        raise C0084RecursiveSplitError("nested c0084 adapter runtime is forbidden")
    admission = _load_admission_identity(
        admission_path, admission_file_sha256,
    )
    active = (
        Path(admission_path), admission_file_sha256,
        admission["record_sha256"],
    )
    replacements = (
        (recursive, "_normalize_trigger", _normalize_crash_trigger),
        (supervisor.child_runner, "_validate_parent_audit", _validate_parent_audit),
        (supervisor, "_legacy_source_binding", _active_source_binding),
        (supervisor, "_legacy_parent_still_split_eligible", _inactive_parent_still_eligible),
        (supervisor, "GATE", GATE),
        (checkpoint_recovery, "_require_checkpoint_receipt", _require_retirement),
        (checkpoint_recovery, "_checked_checkpointed_parent", _checked_inactive_parent),
        (initial_dispatch, "_source_binding", _initial_source_binding),
        (initial_dispatch.batch, "_spawn_child_start", _spawn_adapter_child_start),
    )
    saved = [(module, name, getattr(module, name)) for module, name, _ in replacements]
    _ACTIVE_ADMISSION = active
    try:
        for module, name, replacement in replacements:
            setattr(module, name, replacement)
        yield admission
    finally:
        for module, name, original in reversed(saved):
            setattr(module, name, original)
        _ACTIVE_ADMISSION = None


def _held_bytes(held: root_guard.quarantine.HeldPath, *, cap: int) -> bytes:
    size = held.expected.size
    if type(size) is not int or not 1 <= size <= cap:
        raise C0084RecursiveSplitError("held parent material exceeds its cap")
    position = os.lseek(held.descriptor, 0, os.SEEK_CUR)
    try:
        os.lseek(held.descriptor, 0, os.SEEK_SET)
        chunks: list[bytes] = []
        remaining = size
        while remaining:
            chunk = os.read(held.descriptor, min(1 << 20, remaining))
            if not chunk:
                raise C0084RecursiveSplitError("held parent material was truncated")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(held.descriptor, 1):
            raise C0084RecursiveSplitError("held parent material grew")
        return b"".join(chunks)
    finally:
        os.lseek(held.descriptor, position, os.SEEK_SET)


def _material_from_guard(
    held: root_guard.HeldRecoveryGuard,
) -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], bytes,
]:
    admission = root_guard._read_held_json(held.admission)
    static = root_guard._read_held_json(held.records["static"])
    session = root_guard._read_held_json(held.records["session"])
    started = root_guard._read_held_json(held.records["controller_start"])
    parent = _held_bytes(
        held.quarantine_guard.cube, cap=supervisor.MAX_DIMACS_BYTES,
    )
    return admission, static, session, started, parent


def _build_recovery_material(
    admission: Mapping[str, Any], static: Mapping[str, Any],
    session: Mapping[str, Any], started: Mapping[str, Any], parent: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    incident = admission["incident"]
    source = _active_source_binding()
    ledger = recursive.seal({
        "schema_version": SCHEMA_VERSION,
        "kind": LEDGER_KIND,
        "leaf_id": root_guard.EXPECTED_CHILD_ID,
        "observed_state": "INACTIVE",
        "minimum_attempts": root_guard.MINIMUM_SIGSEGV_ATTEMPTS,
        "total_attempts": incident["total_attempts"],
        "signal": 11,
        "same_proof_cube_checker": True,
        "proof_sha256": incident["proof_sha256"],
        "cube_sha256": incident["cube_sha256"],
        "checker_sha256": incident["checker_sha256"],
        "admission_record_sha256": admission["record_sha256"],
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
    }, "ledger_sha256")
    evidence = recursive.seal({
        "schema_version": SCHEMA_VERSION,
        "kind": EVIDENCE_KIND,
        "ledger_sha256": ledger["ledger_sha256"],
        "admission_record_sha256": admission["record_sha256"],
        "observed_state": "INACTIVE",
        "minimum_attempts": root_guard.MINIMUM_SIGSEGV_ATTEMPTS,
        "total_attempts": incident["total_attempts"],
        "admission_threshold_met": True,
        "old_proof_certified": False,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
    }, "evidence_sha256")
    trigger = recursive.seal({
        "kind": TRIGGER_KIND,
        "reason": TRIGGER_REASON,
        "observed_state": "INACTIVE",
        "minimum_attempts": root_guard.MINIMUM_SIGSEGV_ATTEMPTS,
        "total_attempts": incident["total_attempts"],
        "signal": 11,
        "same_proof_cube_checker": True,
        "proof_sha256": incident["proof_sha256"],
        "cube_sha256": incident["cube_sha256"],
        "checker_sha256": incident["checker_sha256"],
        "admission_record_sha256": admission["record_sha256"],
        "evidence_sha256": evidence["evidence_sha256"],
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
        "old_proof_certified": False,
    }, "trigger_sha256")
    _normalize_crash_trigger(trigger)
    manifest, _payloads = recursive.build_binary_cover(
        parent,
        parent_id=PARENT_ID,
        fanout=FANOUT,
        ancestry_sha256=admission["record_sha256"],
    )
    unsigned_manifest = dict(manifest)
    unsigned_manifest.pop("manifest_sha256")
    unsigned_manifest["trigger"] = trigger
    unsigned_manifest["claim_scope"] = {
        **dict(unsigned_manifest["claim_scope"]),
        "trigger_is_hardness_evidence_only": True,
        "checker_crash_is_not_unsat": True,
        "old_proof_is_not_a_certificate": True,
        "fresh_descendant_certificates_required": FANOUT,
    }
    manifest = recursive.seal(unsigned_manifest, "manifest_sha256")
    recursive.verify_cover(manifest, parent)
    root_info = root_guard.EXPECTED_ROOT.stat(follow_symlinks=False)
    audit = supervisor.seal({
        "schema_version": SCHEMA_VERSION,
        "kind": AUDIT_KIND,
        "parent_root": str(root_guard.EXPECTED_ROOT),
        "parent_root_identity": {
            "path": str(root_guard.EXPECTED_ROOT),
            "device": int(root_info.st_dev), "inode": int(root_info.st_ino),
            "mode": int(root_info.st_mode & 0o7777), "uid": int(root_info.st_uid),
        },
        "parent_static_sha256": static["record_sha256"],
        "parent_session_sha256": session["record_sha256"],
        "parent_dimacs_sha256": hashlib.sha256(parent).hexdigest(),
        "parent_dimacs_bytes": len(parent),
        "parent_generation": 0,
        "parent_pid": started["pid"],
        "parent_proc_start_ticks": started["proc_start_ticks"],
        "observed_state": "INACTIVE",
        "timing_ledger": ledger,
        "timing_evidence": evidence,
        "timing_trigger": trigger,
        "split_allowed": True,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "source_binding": source,
    }, "audit_sha256")
    _validate_parent_audit(audit)
    if manifest.get("trigger") != audit.get("timing_trigger"):
        raise C0084RecursiveSplitError("cover and parent audit triggers differ")
    return audit, manifest


def audit_recovery(
    admission_path: Path, admission_file_sha256: str,
) -> dict[str, Any]:
    held = root_guard.acquire(admission_path, admission_file_sha256)
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            admission, static, session, started, parent = _material_from_guard(held)
            audit, manifest = _build_recovery_material(
                admission, static, session, started, parent,
            )
            verification = recursive.verify_cover(manifest, parent)
            return supervisor.seal({
                "schema_version": SCHEMA_VERSION,
                "kind": "paper400-c0084-recursive-readonly-audit-v1",
                "gate": GATE,
                "admission_record_sha256": admission["record_sha256"],
                "parent_audit": audit,
                "split_manifest": manifest,
                "cover_verification": verification,
                "fanout": FANOUT,
                "hardness_only": True,
                "solver_terminal_claim": False,
                "writes_performed": False,
                "services_started_or_stopped": False,
            }, "record_sha256")
    finally:
        root_guard.close(held)


def _retirement_value(
    bundle: Mapping[str, Any], audit: Mapping[str, Any],
) -> dict[str, Any]:
    return supervisor.seal({
        "schema_version": SCHEMA_VERSION,
        "kind": RETIREMENT_KIND,
        "gate": GATE,
        "bundle_sha256": bundle["bundle_sha256"],
        "parent_root": audit["parent_root"],
        "parent_static_sha256": audit["parent_static_sha256"],
        "parent_session_sha256": audit["parent_session_sha256"],
        "parent_pid": audit["parent_pid"],
        "parent_proc_start_ticks": audit["parent_proc_start_ticks"],
        "parent_state": "INACTIVE_CHECKER_CRASH_GUARDED",
        "admission_record_sha256": _active()[2],
        "checkpoint_created": False,
        "old_proof_certified": False,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "source_binding": _active_source_binding(),
    }, "record_sha256")


def create_bundle(
    bundle: Path, *, admission_path: Path, admission_file_sha256: str,
    cpus: Sequence[int], control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Create only a new recursive bundle; it does not dispatch children."""

    held = root_guard.acquire(admission_path, admission_file_sha256)
    reservation: Mapping[str, Any] | None = None
    target = Path(bundle)
    committed = False
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            control = supervisor._ensure_control_root(control_root)
            if (
                not target.is_absolute()
                or str(target) != os.path.abspath(str(target))
                or target.parent != control
                or os.path.lexists(target)
            ):
                raise C0084RecursiveSplitError("new bundle path is unsafe")
            pool, observations = supervisor._validate_cpu_pool(cpus)
            if len(pool) != FANOUT:
                raise C0084RecursiveSplitError("c0084 recovery requires four CPU leases")
            admission, static, session, started, parent = _material_from_guard(held)
            audit, manifest = _build_recovery_material(
                admission, static, session, started, parent,
            )
            reservation = supervisor._reserve_cpus(
                control, bundle=target, cpus=pool, observations=observations,
            )
            os.mkdir(target, 0o700)
            supervisor._fsync_dir(control)
            for name in (
                supervisor.WORKERS_DIR.name, supervisor.CHILDREN_DIR.name,
            ):
                os.mkdir(target / name, 0o700)
            supervisor._publish_new(target / supervisor.PARENT_DIMACS, parent)
            supervisor._publish_json(target / supervisor.PARENT_AUDIT, audit)
            supervisor._publish_json(target / supervisor.SPLIT_MANIFEST, manifest)
            supervisor._publish_json(target / supervisor.CPU_RESERVATION, reservation)
            queue = recursive.create_split_queue(
                target / supervisor.QUEUE, manifest, cpu_pool=pool,
                parent_manifest_sha256=audit["parent_static_sha256"],
                lease_seconds=supervisor.LEASE_SECONDS,
            )
            bundle_value = supervisor._bundle_value(
                target, audit, manifest, reservation, queue,
            )
            supervisor._publish_json(
                target / supervisor.BUNDLE_COMMIT, bundle_value,
            )
            committed = True
            loaded = supervisor._load_bundle(target, control_root=control)
            retirement = _retirement_value(bundle_value, audit)
            supervisor._publish_json(
                target / supervisor.PARENT_CHECKPOINT, retirement,
            )
            _validate_retirement(loaded, retirement)
            return supervisor.seal({
                "schema_version": SCHEMA_VERSION,
                "kind": RESULT_KIND,
                "gate": GATE,
                "bundle_sha256": bundle_value["bundle_sha256"],
                "retirement_sha256": retirement["record_sha256"],
                "admission_record_sha256": admission["record_sha256"],
                "split_manifest_sha256": manifest["manifest_sha256"],
                "queue_sha256": queue["queue_sha256"],
                "cpu_reservation_sha256": reservation["reservation_sha256"],
                "fanout": FANOUT,
                "children_dispatched": False,
                "hardness_only": True,
                "solver_terminal_claim": False,
                "old_proof_certified": False,
            }, "record_sha256")
    except BaseException:
        if reservation is not None and not committed:
            supervisor._release_cpus(Path(control_root), reservation)
        raise
    finally:
        root_guard.close(held)


def dispatch_initial_children(
    bundle: Path, *, admission_path: Path, admission_file_sha256: str,
    control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Durably claim all four leaves before starting any trusted child."""

    held = root_guard.acquire(admission_path, admission_file_sha256)
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            loaded = supervisor._load_bundle(bundle, control_root=control_root)
            _require_retirement(loaded)
            return initial_dispatch.dispatch_initial_batch(
                bundle, control_root=control_root,
                worker_prefix=f"c0084-crash-recovery-{os.uname().nodename}-{os.getpid()}",
            )
    finally:
        root_guard.close(held)


def child_start(
    root: Path, *, cpu: int, admission_path: Path,
    admission_file_sha256: str,
) -> dict[str, Any]:
    """External affinity namespace used only by the trusted batch starter."""

    held = root_guard.acquire(admission_path, admission_file_sha256)
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            return supervisor.child_runner.start_root(root, cpu=cpu)
    finally:
        root_guard.close(held)


def tick_bundle(
    bundle: Path, *, admission_path: Path, admission_file_sha256: str,
    control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Advance the existing trusted v3 lifecycle under the c0084 guard."""

    held = root_guard.acquire(admission_path, admission_file_sha256)
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            loaded = initial_dispatch._load_immutable_components(
                bundle, control_root=control_root,
            )
            _require_retirement(loaded)
            return lifecycle.tick_bundle(bundle, control_root=control_root)
    finally:
        root_guard.close(held)


def run_loop(
    bundle: Path, *, admission_path: Path, admission_file_sha256: str,
    control_root: Path = supervisor.CONTROL_ROOT,
    interval_seconds: float = DEFAULT_INTERVAL_SECONDS,
) -> None:
    if (
        type(interval_seconds) not in {int, float}
        or not 1.0 <= float(interval_seconds) <= 3600.0
    ):
        raise C0084RecursiveSplitError("lifecycle interval is unsafe")
    held = root_guard.acquire(admission_path, admission_file_sha256)
    try:
        with _adapter_runtime(admission_path, admission_file_sha256):
            loaded = initial_dispatch._load_immutable_components(
                bundle, control_root=control_root,
            )
            _require_retirement(loaded)
            while True:
                result = lifecycle.tick_bundle(bundle, control_root=control_root)
                sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
                sys.stdout.buffer.flush()
                time.sleep(float(interval_seconds))
    finally:
        root_guard.close(held)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    for name in (
        "audit", "create-bundle", "dispatch", "child-start", "tick",
        "run-loop",
    ):
        command = sub.add_parser(name, allow_abbrev=False)
        command.add_argument("--admission", required=True, type=Path)
        command.add_argument("--admission-sha256", required=True)
        if name not in {"audit", "child-start"}:
            command.add_argument("--bundle", required=True, type=Path)
        if name == "create-bundle":
            command.add_argument("--cpu", required=True, action="append", type=int)
        if name == "run-loop":
            command.add_argument(
                "--interval-seconds", type=float,
                default=DEFAULT_INTERVAL_SECONDS,
            )
        if name == "child-start":
            command.add_argument("--root", required=True, type=Path)
            command.add_argument("--cpu", required=True, type=int)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    common = {
        "admission_path": args.admission,
        "admission_file_sha256": args.admission_sha256,
    }
    if args.action == "audit":
        result = audit_recovery(**common)
    elif args.action == "create-bundle":
        result = create_bundle(
            args.bundle, cpus=args.cpu, control_root=args.control_root, **common,
        )
    elif args.action == "dispatch":
        result = dispatch_initial_children(
            args.bundle, control_root=args.control_root, **common,
        )
    elif args.action == "child-start":
        result = child_start(args.root, cpu=args.cpu, **common)
    elif args.action == "tick":
        result = tick_bundle(
            args.bundle, control_root=args.control_root, **common,
        )
    elif args.action == "run-loop":
        run_loop(
            args.bundle, control_root=args.control_root,
            interval_seconds=args.interval_seconds, **common,
        )
        return 0
    else:  # pragma: no cover
        raise C0084RecursiveSplitError("unsupported c0084 action")
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        C0084RecursiveSplitError,
        root_guard.C0084RecoveryGuardError,
        recursive.RecursiveSplitError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        initial_dispatch.InitialBatchDispatchError,
        checkpoint_recovery.RecursiveCheckpointRecoveryError,
        OSError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
