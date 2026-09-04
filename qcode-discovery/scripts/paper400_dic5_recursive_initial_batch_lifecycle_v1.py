#!/usr/bin/env python3
"""Recoverable lifecycle for simultaneous initial recursive child launches.

``paper400_dic5_recursive_initial_batch_dispatch_v1`` intentionally claims
every child before it starts any one of them.  The frozen v1 supervisor has a
one-claim bootstrap ledger, so it cannot subsequently tick that all-claim
queue.  This sidecar supplies the missing lifecycle without changing the
frozen sources or weakening their proof checks:

* it replays the sealed initial batch plan and every durable worker binding;
* it records each queue mutation as a prepared, then committed transaction;
* an interrupted atomic queue write is recovered only after the child proof is
  freshly revalidated again;
* a quick DMTCP exit follows the existing DRAT/LRAT/fresh-replay recovery
  path, while an ordinary stopped child follows the frozen child runner;
* it aggregates a parent only after every exact frontier child is certified.

The module never resumes a parent, starts a child, releases an uncertified
claim, infers UNSAT from a timeout, or deletes data.  It is deliberately a
separate, versioned sidecar because its source identity is part of the audit
records it publishes.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import math
import os
import stat
import sys
import time
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-initial-batch-lifecycle-v1"
LOCK = Path(".initial-batch-lifecycle-v1.lock")
TRANSITIONS = initial.SIDECAR_DIR / "queue-transitions"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
TRANSITION_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-v1"
PREPARE_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-prepare-v1"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-initial-batch-parent-aggregate-v1"
RESULT_KIND = "paper400-dic5-recursive-initial-batch-lifecycle-tick-v1"
SUPPORTED_ACTIONS = {"CERTIFY_CHILD", "RENEW_CLAIM"}


class InitialBatchLifecycleError(RuntimeError):
    """The all-claim initial batch cannot be safely replayed or advanced."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "initial_batch_lifecycle": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "initial_batch_dispatch": initial._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "frozen_supervisor": supervisor._legacy_source_binding(),
    }


@contextlib.contextmanager
def _lifecycle_lock(bundle: Path) -> Iterator[None]:
    """Serialize lifecycle ticks independently of the first-launch lock."""

    path = bundle / LOCK
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise InitialBatchLifecycleError("initial batch lifecycle lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise InitialBatchLifecycleError("initial batch lifecycle lock metadata is unsafe")
        import fcntl

        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise InitialBatchLifecycleError("another initial batch lifecycle tick is active") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _safe_existing_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.exists():
        raise InitialBatchLifecycleError(f"{label} is absent or unsafe")
    try:
        return supervisor._safe_directory(path, require_mode_0700=True)
    except supervisor.RecursiveSplitSupervisorError as exc:
        raise InitialBatchLifecycleError(f"{label} is unsafe") from exc


def _queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    matches = [
        item for item in queue.get("items", [])
        if isinstance(item, dict) and item.get("item_id") == item_id
    ]
    if len(matches) != 1:
        raise InitialBatchLifecycleError("queue item is absent or ambiguous")
    return matches[0]


def _step_for_item(loaded: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    matches = [
        step for step in loaded["plan"]["steps"]
        if isinstance(step, dict) and step.get("item_id") == item_id
    ]
    if len(matches) != 1:
        raise InitialBatchLifecycleError("initial batch plan has no unique item step")
    return matches[0]


def _worker_for_item(
    loaded: Mapping[str, Any], queue: Mapping[str, Any], item_id: str,
    *, require_live_claim: bool,
) -> tuple[dict[str, Any], dict[str, Any], Path]:
    """Bind the current queue item to its immutable initial worker record."""

    step = _step_for_item(loaded, item_id)
    worker = step["worker"]
    bundle = Path(loaded["root"])
    worker_path = bundle / supervisor.WORKERS_DIR / step["worker_filename"]
    if worker_path.is_symlink() or not worker_path.exists():
        raise InitialBatchLifecycleError("initial worker record is absent or unsafe")
    if supervisor._read_json(worker_path) != worker:
        raise InitialBatchLifecycleError("initial worker record changed after dispatch")
    item = _queue_item(queue, item_id)
    child_root = Path(worker.get("child_root", ""))
    expected_root = bundle / supervisor.CHILDREN_DIR / item.get("path", "")
    if (
        child_root != expected_root
        or worker.get("item_id") != item_id
        or worker.get("leaf_id") != item.get("leaf_id")
        or worker.get("leaf_sha256") != item.get("leaf_sha256")
        or worker.get("cpu_ids") != step["worker"].get("cpu_ids")
    ):
        raise InitialBatchLifecycleError("initial worker no longer binds its child leaf")
    if require_live_claim:
        claim = item.get("claim")
        if (
            item.get("state") != "CLAIMED"
            or not isinstance(claim, dict)
            or claim.get("token") != worker.get("token")
            or claim.get("worker_id") != worker.get("worker_id")
            or claim.get("cpu_ids") != worker.get("cpu_ids")
            or item.get("cpu_ids") != worker.get("cpu_ids")
        ):
            raise InitialBatchLifecycleError("initial worker lost its claimed queue binding")
    elif item.get("state") not in {"CLAIMED", "CERTIFIED"}:
        raise InitialBatchLifecycleError("initial worker queue state is unsupported")
    return item, worker, child_root


def _load_initial_batch(
    bundle: Path, *, control_root: Path,
) -> dict[str, Any]:
    """Replay static evidence plus the immutable all-claim launch commit."""

    loaded = initial._load_immutable_components(bundle, control_root=control_root)
    root = Path(loaded["root"])
    sidecar = _safe_existing_directory(root / initial.SIDECAR_DIR, label="initial batch sidecar")
    plan_path = sidecar / initial.PLAN.name
    ledger_path = root / initial.LEDGER
    commit_path = root / initial.COMMIT
    if any(path.is_symlink() or not path.exists() for path in (plan_path, ledger_path, commit_path)):
        raise InitialBatchLifecycleError("initial batch plan, ledger, or commit is absent")
    try:
        plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
    except batch.BatchDispatchError as exc:
        raise InitialBatchLifecycleError("initial batch plan is not replayable") from exc
    initial_queue = plan["steps"][0]["before_queue"]
    final_queue = plan["steps"][-1]["after_queue"]
    if (
        plan.get("initial_queue_sha256") != loaded["bundle"].get("queue_sha256")
        or plan.get("initial_event_sequence") != 0
        or plan.get("final_event_sequence") != len(plan["steps"])
        or len(plan["steps"]) != loaded["bundle"].get("fanout")
        or {step.get("item_id") for step in plan["steps"]}
        != {item.get("item_id") for item in initial_queue.get("items", [])}
        or any(item.get("state") != "PENDING" for item in initial_queue.get("items", []))
        or any(item.get("state") != "CLAIMED" for item in final_queue.get("items", []))
    ):
        raise InitialBatchLifecycleError("initial all-claim plan does not cover its pristine queue")
    queue = recursive.load_split_queue(root / supervisor.QUEUE)
    reconstructed = recovery._reconstruct_initial_queue(queue)
    if reconstructed != initial_queue:
        raise InitialBatchLifecycleError("current queue cannot reconstruct the pristine initial queue")
    expected_ledger = initial._ledger_value(loaded, plan)
    expected_commit = initial._commit_value(loaded, plan, expected_ledger)
    if supervisor._read_json(ledger_path) != expected_ledger:
        raise InitialBatchLifecycleError("initial all-claim ledger changed")
    if supervisor._read_json(commit_path) != expected_commit:
        raise InitialBatchLifecycleError("initial all-claim commit changed")
    if (root / recovery.QUEUE_LEDGER_DIR).exists() or (root / recovery.QUEUE_LEDGER_DIR).is_symlink():
        raise InitialBatchLifecycleError("initial all-claim queue overlaps the v1 one-claim ledger")
    for step in plan["steps"]:
        worker_path = root / supervisor.WORKERS_DIR / step["worker_filename"]
        if worker_path.is_symlink() or not worker_path.exists() or supervisor._read_json(worker_path) != step["worker"]:
            raise InitialBatchLifecycleError("initial all-claim worker record changed")
    return {
        **loaded,
        "queue": queue,
        "plan": plan,
        "initial_ledger": expected_ledger,
        "initial_commit": expected_commit,
        "initial_queue": initial_queue,
        "initial_final_queue": final_queue,
    }


def _transition_paths(root: Path) -> tuple[Path, Path]:
    return root / RECORDS, root / PREPARES


def _read_ordered_records(directory: Path, *, suffix: str, label: str) -> list[dict[str, Any]]:
    if not directory.exists() and not directory.is_symlink():
        return []
    safe = _safe_existing_directory(directory, label=label)
    paths = sorted(safe.iterdir(), key=lambda path: path.name)
    records: list[dict[str, Any]] = []
    for position, path in enumerate(paths):
        expected = f"{position:06d}-{suffix}.json"
        if path.name != expected or path.is_symlink() or not path.is_file():
            raise InitialBatchLifecycleError(f"{label} contains an unknown or unordered record")
        records.append(supervisor._read_json(path))
    return records


def _expected_certified_queue(
    before: Mapping[str, Any], *, item_id: str, worker_id: str, token: str,
    certificate: Mapping[str, Any], validation: Mapping[str, Any], timestamp: float,
) -> dict[str, Any]:
    """Pure replay of the public ``certify_queue_item`` mutation."""

    value = copy.deepcopy(recursive._queue_unsigned(before))
    item = _queue_item(value, item_id)
    recursive._check_claim(item, worker_id, token)
    if not recursive._queue_certificate_complete(certificate, item, validation):
        raise InitialBatchLifecycleError("certification transaction lacks a complete fresh proof")
    digest = recursive._certificate_digest(certificate)
    unsigned = recursive._queue_item_unsigned(item)
    unsigned.update({
        "state": "CERTIFIED", "claim": None, "cpu_ids": [],
        "certificate_sha256": digest, "last_error": None,
    })
    item.clear()
    item.update(recursive.seal(unsigned, "item_sha256"))
    value["updated_at"] = timestamp
    value["event_sequence"] += 1
    return recursive._reseal_queue(value)


def _expected_renewed_queue(
    before: Mapping[str, Any], *, item_id: str, worker_id: str, token: str,
    lease_seconds: float, timestamp: float,
) -> dict[str, Any]:
    """Pure replay of the public ``renew_queue_item`` mutation."""

    value = copy.deepcopy(recursive._queue_unsigned(before))
    item = _queue_item(value, item_id)
    recursive._check_claim(item, worker_id, token)
    claim = item["claim"]
    if timestamp >= claim["lease_expires_at"]:
        raise InitialBatchLifecycleError("cannot renew an expired initial child claim")
    if not math.isfinite(lease_seconds) or not 0 < lease_seconds <= recursive.QUEUE_MAX_LEASE_SECONDS:
        raise InitialBatchLifecycleError("initial child renewal duration is invalid")
    renewed_claim = dict(claim)
    renewed_claim["lease_expires_at"] = timestamp + lease_seconds
    unsigned = recursive._queue_item_unsigned(item)
    unsigned["claim"] = renewed_claim
    item.clear()
    item.update(recursive.seal(unsigned, "item_sha256"))
    value["updated_at"] = timestamp
    value["event_sequence"] += 1
    return recursive._reseal_queue(value)


def _prepare_value(
    loaded: Mapping[str, Any], *, sequence: int, previous_record_sha256: str,
    action: str, item_id: str, before: Mapping[str, Any], after: Mapping[str, Any],
    binding: Mapping[str, Any],
) -> dict[str, Any]:
    if action not in SUPPORTED_ACTIONS or type(sequence) is not int or sequence < 0:
        raise InitialBatchLifecycleError("initial queue transition request is invalid")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PREPARE_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": loaded["plan"]["record_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "sequence": sequence,
            "previous_record_sha256": previous_record_sha256,
            "action": action,
            "item_id": item_id,
            "before_queue": copy.deepcopy(dict(before)),
            "after_queue": copy.deepcopy(dict(after)),
            "binding": copy.deepcopy(dict(binding)),
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _transition_value(loaded: Mapping[str, Any], prepared: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": TRANSITION_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": loaded["plan"]["record_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "sequence": prepared["sequence"],
            "previous_record_sha256": prepared["previous_record_sha256"],
            "prepared_sha256": prepared["record_sha256"],
            "action": prepared["action"],
            "item_id": prepared["item_id"],
            "before_queue": copy.deepcopy(prepared["before_queue"]),
            "after_queue": copy.deepcopy(prepared["after_queue"]),
            "binding": copy.deepcopy(prepared["binding"]),
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_transition_request(
    loaded: Mapping[str, Any], value: Mapping[str, Any], *, sequence: int,
    previous_record_sha256: str, before: Mapping[str, Any],
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "plan_sha256",
        "initial_commit_sha256", "sequence", "previous_record_sha256", "action",
        "item_id", "before_queue", "after_queue", "binding", "source_binding",
        "record_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != PREPARE_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("plan_sha256") != loaded["plan"].get("record_sha256")
        or value.get("initial_commit_sha256") != loaded["initial_commit"].get("record_sha256")
        or value.get("sequence") != sequence
        or value.get("previous_record_sha256") != previous_record_sha256
        or value.get("before_queue") != before
        or value.get("action") not in SUPPORTED_ACTIONS
        or type(value.get("item_id")) is not str
        or not isinstance(value.get("after_queue"), dict)
        or not isinstance(value.get("binding"), dict)
        or value.get("source_binding") != _source_binding()
    ):
        raise InitialBatchLifecycleError("prepared initial queue transition is malformed")
    try:
        recursive._validate_queue(value["before_queue"])
        recursive._validate_queue(value["after_queue"])
    except recursive.RecursiveSplitError as exc:
        raise InitialBatchLifecycleError("prepared queue snapshot is malformed") from exc
    action = value["action"]
    binding = value["binding"]
    item = _queue_item(before, value["item_id"])
    if (
        type(binding.get("timestamp")) not in {int, float}
        or not math.isfinite(float(binding["timestamp"]))
        or binding.get("worker_id") != item.get("claim", {}).get("worker_id")
        or binding.get("token") != item.get("claim", {}).get("token")
        or binding.get("worker_sha256") != _step_for_item(loaded, value["item_id"])["worker"].get("worker_sha256")
        or binding.get("queue_item_sha256_before") != item.get("item_sha256")
    ):
        raise InitialBatchLifecycleError("prepared initial queue transition lost its worker binding")
    timestamp = float(binding["timestamp"])
    if action == "CERTIFY_CHILD":
        if binding.get("proof_mode") not in {"NORMAL", "FAST"}:
            raise InitialBatchLifecycleError("prepared child certification has no admitted proof mode")
        certificate = binding.get("certificate")
        validation = binding.get("validation")
        if not isinstance(certificate, dict) or not isinstance(validation, dict):
            raise InitialBatchLifecycleError("prepared child certification lacks proof records")
        expected = _expected_certified_queue(
            before, item_id=value["item_id"], worker_id=binding["worker_id"], token=binding["token"],
            certificate=certificate, validation=validation, timestamp=timestamp,
        )
    else:
        lease_seconds = binding.get("lease_seconds")
        if type(lease_seconds) not in {int, float}:
            raise InitialBatchLifecycleError("prepared claim renewal lacks its duration")
        expected = _expected_renewed_queue(
            before, item_id=value["item_id"], worker_id=binding["worker_id"], token=binding["token"],
            lease_seconds=float(lease_seconds), timestamp=timestamp,
        )
    if expected != value["after_queue"]:
        raise InitialBatchLifecycleError("prepared queue transition does not replay its admitted mutation")
    return dict(value)


def _validate_transition_record(
    loaded: Mapping[str, Any], value: Mapping[str, Any], *, prepared: Mapping[str, Any],
    sequence: int, previous_record_sha256: str, before: Mapping[str, Any],
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "plan_sha256",
        "initial_commit_sha256", "sequence", "previous_record_sha256", "prepared_sha256",
        "action", "item_id", "before_queue", "after_queue", "binding", "source_binding",
        "record_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != TRANSITION_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("plan_sha256") != loaded["plan"].get("record_sha256")
        or value.get("initial_commit_sha256") != loaded["initial_commit"].get("record_sha256")
        or value.get("sequence") != sequence
        or value.get("previous_record_sha256") != previous_record_sha256
        or value.get("prepared_sha256") != prepared.get("record_sha256")
        or value.get("action") != prepared.get("action")
        or value.get("item_id") != prepared.get("item_id")
        or value.get("before_queue") != prepared.get("before_queue")
        or value.get("after_queue") != prepared.get("after_queue")
        or value.get("binding") != prepared.get("binding")
        or value.get("source_binding") != _source_binding()
    ):
        raise InitialBatchLifecycleError("committed initial queue transition is malformed")
    _validate_transition_request(
        loaded, prepared, sequence=sequence, previous_record_sha256=previous_record_sha256,
        before=before,
    )
    return dict(value)


def _read_transition_state(loaded: Mapping[str, Any]) -> dict[str, Any]:
    """Replay committed and at-most-one prepared queue transaction."""

    root = Path(loaded["root"])
    transition_dir, prepare_dir = _transition_paths(root)
    prepared = _read_ordered_records(prepare_dir, suffix="prepare", label="initial queue prepares")
    records = _read_ordered_records(transition_dir, suffix="transition", label="initial queue transitions")
    if len(prepared) not in {len(records), len(records) + 1}:
        raise InitialBatchLifecycleError("initial queue transaction history has a gap")
    before = loaded["initial_final_queue"]
    previous = loaded["plan"]["record_sha256"]
    for sequence, record in enumerate(records):
        prepared_value = _validate_transition_request(
            loaded, prepared[sequence], sequence=sequence,
            previous_record_sha256=previous, before=before,
        )
        committed = _validate_transition_record(
            loaded, record, prepared=prepared_value, sequence=sequence,
            previous_record_sha256=previous, before=before,
        )
        before = committed["after_queue"]
        previous = committed["record_sha256"]
    pending: dict[str, Any] | None = None
    if len(prepared) == len(records) + 1:
        pending = _validate_transition_request(
            loaded, prepared[-1], sequence=len(records),
            previous_record_sha256=previous, before=before,
        )
    current = recursive.load_split_queue(root / supervisor.QUEUE)
    if current != before and (pending is None or current != pending["after_queue"]):
        raise InitialBatchLifecycleError("queue differs from both its committed and prepared transaction states")
    return {
        "records": records,
        "prepared": prepared,
        "pending": pending,
        "committed_queue": before,
        "previous_record_sha256": previous,
        "current_queue": current,
    }


def _prepare_path(root: Path, sequence: int) -> Path:
    return initial._safe_sidecar_dir(root, PREPARES) / f"{sequence:06d}-prepare.json"


def _transition_path(root: Path, sequence: int) -> Path:
    return initial._safe_sidecar_dir(root, RECORDS) / f"{sequence:06d}-transition.json"


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        if path.is_symlink() or supervisor._read_json(path) != value:
            raise InitialBatchLifecycleError(f"existing {label} conflicts with replay")
        return
    supervisor._publish_json(path, value)


def _is_fast_orphan(loaded: Mapping[str, Any], *, item_id: str) -> bool:
    step = _step_for_item(loaded, item_id)
    worker_path = Path(loaded["root"]) / supervisor.WORKERS_DIR / step["worker_filename"]
    orphan = worker_path.with_name(worker_path.stem + ".orphan.json")
    if not orphan.exists() and not orphan.is_symlink():
        return False
    # ``_worker_context`` authenticates both the orphan and the current queue
    # claim.  A non-fast orphan is an audit stop, never a reason to start a
    # replacement child.
    try:
        recovery._worker_context(loaded, item_id=item_id, require_live_claim=True)
    except recovery.RecursiveCheckpointRecoveryError as exc:
        raise InitialBatchLifecycleError("initial child orphan is not an exact fast-terminal receipt") from exc
    return True


def _fresh_fast_validation(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, item_id: str,
    require_live_claim: bool = True,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Replay the existing fast path without relying on the v1 queue loader."""

    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    item, worker, child_root = _worker_for_item(
        loaded, queue, item_id, require_live_claim=require_live_claim,
    )
    _recovery_item, _path, recovery_worker, _orphan, _queue = recovery._worker_context(
        loaded, item_id=item_id, require_live_claim=require_live_claim,
    )
    if recovery_worker != worker or _recovery_item != item:
        raise InitialBatchLifecycleError("fast-terminal worker changed during replay")
    with supervisor.child_runner._root_lock(child_root, exclusive=False):
        fast_recovery, claim, fresh_drat, fresh_lrat = recovery._revalidate_fast_terminal_claim(
            loaded, receipt, root=child_root, require_live_claim=require_live_claim,
        )
        certificate = supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE)
        expected = recovery._fast_certificate_value(loaded, fast_recovery, claim, root=child_root)
        if certificate != expected:
            raise InitialBatchLifecycleError("fast-terminal certificate does not replay its claim")
        validation = supervisor.seal(
            {
                "schema_version": recovery.SCHEMA_VERSION,
                "kind": recovery.FAST_FRESH_VALIDATION_KIND,
                "gate": recovery.GATE,
                "root": str(child_root),
                "fast_recovery_sha256": fast_recovery["record_sha256"],
                "fast_terminal_claim_sha256": claim["terminal_claim_sha256"],
                "certificate_sha256": certificate["certificate_sha256"],
                "fresh_drat": fresh_drat,
                "fresh_lrat": fresh_lrat,
                "valid": True,
                "strict_proof_unsat": True,
                "fresh_proof_replay": True,
                "source_toolchain_fresh": True,
                "failures": [],
                "global_distance_claim": None,
                "publication_certificate": False,
                "upload_authorized": False,
            },
            "validation_sha256",
        )
        return certificate, validation


def _revalidate_certification(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], prepared: Mapping[str, Any],
) -> None:
    """Recheck proof evidence before completing a crash-recovery queue write."""

    binding = prepared["binding"]
    item_id = prepared["item_id"]
    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    # The queue can already be CERTIFIED after the atomic write; use the
    # immutable before snapshot to validate worker ownership and then the child
    # filesystem to validate the actual proof.
    before_item = _queue_item(prepared["before_queue"], item_id)
    step = _step_for_item(loaded, item_id)
    worker = step["worker"]
    if (
        before_item.get("claim", {}).get("worker_id") != worker.get("worker_id")
        or before_item.get("claim", {}).get("token") != worker.get("token")
        or binding.get("worker_sha256") != worker.get("worker_sha256")
    ):
        raise InitialBatchLifecycleError("prepared certification worker binding changed")
    child_root = Path(worker["child_root"])
    certificate = binding.get("certificate")
    validation = binding.get("validation")
    if not isinstance(certificate, dict) or not isinstance(validation, dict):
        raise InitialBatchLifecycleError("prepared certification proof records are absent")
    if binding.get("proof_mode") == "FAST":
        # The helper requires a live queue claim.  For an already-applied
        # atomic certification, replay against the stored, immutable claim is
        # still represented by its child terminal records; the normal
        # fast-recovery verifier deliberately cannot be invoked after claim
        # release.  In that case validate certificate shape and the frozen
        # final record instead of pretending a live claim still exists.
        current_item = _queue_item(queue, item_id)
        if current_item.get("state") == "CLAIMED":
            fresh_certificate, _fresh_validation = _fresh_fast_validation(loaded, receipt, item_id=item_id)
            if fresh_certificate != certificate:
                raise InitialBatchLifecycleError("fast-terminal certificate changed during recovery")
        else:
            fresh_certificate, _fresh_validation = _fresh_fast_validation(
                loaded, receipt, item_id=item_id, require_live_claim=False,
            )
            if fresh_certificate != certificate:
                raise InitialBatchLifecycleError("already-certified fast certificate changed")
    elif binding.get("proof_mode") == "NORMAL":
        stored = supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE)
        if stored != certificate:
            raise InitialBatchLifecycleError("normal child certificate changed during recovery")
        # ``verify_final_root`` performs new DRAT and LRAT replays.  Its
        # validation object is intentionally fresh and need not byte-match the
        # original transaction's validation receipt.
        supervisor.child_runner.verify_final_root(child_root)
    else:
        raise InitialBatchLifecycleError("prepared certification proof mode is invalid")
    if not recursive._queue_certificate_complete(certificate, before_item, validation):
        raise InitialBatchLifecycleError("prepared certification is no longer complete")


def _apply_prepared_transition(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], state: Mapping[str, Any],
) -> dict[str, Any]:
    """Finish at most one prepared mutation, including the queue-write gap."""

    prepared = state.get("pending")
    if prepared is None:
        return dict(state)
    current = state["current_queue"]
    before = prepared["before_queue"]
    after = prepared["after_queue"]
    action = prepared["action"]
    binding = prepared["binding"]
    if current == before:
        if action == "CERTIFY_CHILD":
            _revalidate_certification(loaded, receipt, prepared)
            actual = recursive.certify_queue_item(
                Path(loaded["root"]) / supervisor.QUEUE,
                item_id=prepared["item_id"], worker_id=binding["worker_id"], token=binding["token"],
                certificate=binding["certificate"], validation=binding["validation"],
                now=float(binding["timestamp"]),
            )
        else:
            actual = recursive.renew_queue_item(
                Path(loaded["root"]) / supervisor.QUEUE,
                item_id=prepared["item_id"], worker_id=binding["worker_id"], token=binding["token"],
                lease_seconds=float(binding["lease_seconds"]), now=float(binding["timestamp"]),
            )
        if actual != after:
            raise InitialBatchLifecycleError("atomic queue mutation did not match its prepared transition")
    elif current == after:
        if action == "CERTIFY_CHILD":
            _revalidate_certification(loaded, receipt, prepared)
    else:  # guarded by _read_transition_state; retained for defensive clarity.
        raise InitialBatchLifecycleError("prepared queue transaction has an unknown on-disk state")
    transition = _transition_value(loaded, prepared)
    _publish_exact(
        _transition_path(Path(loaded["root"]), prepared["sequence"]), transition,
        label="initial queue transition",
    )
    return _read_transition_state(loaded)


def _begin_certification(
    loaded: Mapping[str, Any], state: Mapping[str, Any], *, item_id: str,
    certificate: Mapping[str, Any], validation: Mapping[str, Any], proof_mode: str,
) -> dict[str, Any]:
    if state.get("pending") is not None:
        raise InitialBatchLifecycleError("cannot prepare a second initial queue mutation")
    before = state["committed_queue"]
    item, worker, _child_root = _worker_for_item(loaded, before, item_id, require_live_claim=True)
    timestamp = time.time()
    binding = {
        "worker_id": worker["worker_id"],
        "token": worker["token"],
        "worker_sha256": worker["worker_sha256"],
        "queue_item_sha256_before": item["item_sha256"],
        "timestamp": timestamp,
        "proof_mode": proof_mode,
        "certificate": copy.deepcopy(dict(certificate)),
        "validation": copy.deepcopy(dict(validation)),
    }
    after = _expected_certified_queue(
        before, item_id=item_id, worker_id=worker["worker_id"], token=worker["token"],
        certificate=certificate, validation=validation, timestamp=timestamp,
    )
    prepared = _prepare_value(
        loaded, sequence=len(state["records"]), previous_record_sha256=state["previous_record_sha256"],
        action="CERTIFY_CHILD", item_id=item_id, before=before, after=after, binding=binding,
    )
    _publish_exact(
        _prepare_path(Path(loaded["root"]), prepared["sequence"]), prepared,
        label="initial child certification prepare",
    )
    return _read_transition_state(loaded)


def _begin_renewal(
    loaded: Mapping[str, Any], state: Mapping[str, Any], *, item_id: str,
) -> dict[str, Any]:
    if state.get("pending") is not None:
        raise InitialBatchLifecycleError("cannot prepare a second initial queue mutation")
    before = state["committed_queue"]
    item, worker, _child_root = _worker_for_item(loaded, before, item_id, require_live_claim=True)
    timestamp = time.time()
    lease_seconds = float(supervisor.LEASE_SECONDS)
    binding = {
        "worker_id": worker["worker_id"],
        "token": worker["token"],
        "worker_sha256": worker["worker_sha256"],
        "queue_item_sha256_before": item["item_sha256"],
        "timestamp": timestamp,
        "lease_seconds": lease_seconds,
    }
    after = _expected_renewed_queue(
        before, item_id=item_id, worker_id=worker["worker_id"], token=worker["token"],
        lease_seconds=lease_seconds, timestamp=timestamp,
    )
    prepared = _prepare_value(
        loaded, sequence=len(state["records"]), previous_record_sha256=state["previous_record_sha256"],
        action="RENEW_CLAIM", item_id=item_id, before=before, after=after, binding=binding,
    )
    _publish_exact(
        _prepare_path(Path(loaded["root"]), prepared["sequence"]), prepared,
        label="initial child renewal prepare",
    )
    return _read_transition_state(loaded)


def _aggregate_if_complete(loaded: Mapping[str, Any]) -> dict[str, Any] | None:
    root = Path(loaded["root"])
    queue = recursive.load_split_queue(root / supervisor.QUEUE)
    status = recursive.split_queue_status(root / supervisor.QUEUE)
    if status.get("status") != recursive.QUEUE_STATUS_COMPLETE:
        return None
    certificates: list[dict[str, Any]] = []
    for item in queue["items"]:
        _queue_item_value, worker, child_root = _worker_for_item(
            loaded, queue, item["item_id"], require_live_claim=False,
        )
        if worker.get("item_id") != item["item_id"]:
            raise InitialBatchLifecycleError("complete queue child has mismatched worker")
        certificate = supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE)
        certificates.append(certificate)
    aggregate = recursive.aggregate_child_certificates(loaded["manifest"], certificates)
    if aggregate.get("status") != "PARENT_CUBE_UNSAT":
        raise InitialBatchLifecycleError("complete initial queue did not aggregate to parent UNSAT")
    expected = supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PARENT_AGGREGATE_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "aggregate": aggregate,
            "aggregate_sha256": aggregate["aggregate_sha256"],
            "hardness_only": False,
            "parent_solver_terminal_claim": True,
            "global_distance_claim": None,
            "publication_certificate": False,
            "upload_authorized": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )
    path = root / supervisor.PARENT_AGGREGATE
    _publish_exact(path, expected, label="initial batch parent aggregate")
    # CPU reservations become releasable only after the sealed parent
    # aggregate exists.  The helper is idempotent and never removes data.
    supervisor._release_cpus(Path(loaded["control_root"]), loaded["reservation"])
    return expected


def _tick_claimed_item(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], state: Mapping[str, Any], *, item_id: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Observe exactly one claimed child and advance one safe transaction."""

    queue = state["committed_queue"]
    item, worker, child_root = _worker_for_item(loaded, queue, item_id, require_live_claim=True)
    claim = item["claim"]
    now = time.time()
    if claim["lease_expires_at"] - now < supervisor.RENEW_BEFORE_SECONDS:
        state = _begin_renewal(loaded, state, item_id=item_id)
        state = _apply_prepared_transition(loaded, receipt, state)
        return state, {"item_id": item_id, "action": "LEASE_RENEWED"}
    if _is_fast_orphan(loaded, item_id=item_id):
        recovered = recovery._recover_fast_terminal_root(
            loaded, receipt, item=item, worker=worker,
            orphan=recovery._worker_context(loaded, item_id=item_id, require_live_claim=True)[3],
            root=child_root, require_live_claim=True,
        )
        certificate, validation = _fresh_fast_validation(loaded, receipt, item_id=item_id)
        if certificate != recovered["certificate"]:
            raise InitialBatchLifecycleError("fast child certificate changed before queue certification")
        state = _begin_certification(
            loaded, state, item_id=item_id, certificate=certificate, validation=validation,
            proof_mode="FAST",
        )
        state = _apply_prepared_transition(loaded, receipt, state)
        return state, {"item_id": item_id, "action": "FAST_TERMINAL_CERTIFIED"}
    status = supervisor.child_runner.status_root(child_root, verify_hashes=False)
    observed = status.get("state")
    if observed in {"INACTIVE_UNCHECKPOINTED", "CHECKPOINTED"}:
        supervisor.child_runner.harvest_stopped_root(child_root)
        status = supervisor.child_runner.status_root(child_root, verify_hashes=False)
        observed = status.get("state")
    if observed == "PROOF_CARRYING_CHILD_UNSAT":
        validation = supervisor.child_runner.verify_final_root(child_root)
        certificate = supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE)
        state = _begin_certification(
            loaded, state, item_id=item_id, certificate=certificate, validation=validation,
            proof_mode="NORMAL",
        )
        state = _apply_prepared_transition(loaded, receipt, state)
        return state, {"item_id": item_id, "action": "CERTIFIED", "certificate_sha256": certificate["certificate_sha256"]}
    return state, {"item_id": item_id, "action": "OBSERVED", "state": observed}


def tick_bundle(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Safely progress one simultaneous-initial-launch recursive bundle."""

    target = Path(bundle)
    with initial._dispatch_lock(target):
        with _lifecycle_lock(target):
            loaded = _load_initial_batch(target, control_root=control_root)
            receipt = recovery._require_checkpoint_receipt(loaded)
            parent_root = Path(loaded["audit"]["parent_root"])
            with recovery._legacy_shared_lock(parent_root):
                recovery._checked_checkpointed_parent(loaded)
                state = _read_transition_state(loaded)
                aggregate_path = Path(loaded["root"]) / supervisor.PARENT_AGGREGATE
                if not aggregate_path.exists() and not aggregate_path.is_symlink():
                    with supervisor._catalog_lock(Path(loaded["control_root"])):
                        recovery._require_reserved_cpu_leases(loaded)
                state = _apply_prepared_transition(loaded, receipt, state)
                actions: list[dict[str, Any]] = []
                # One queue mutation at a time gives every completed proof a
                # durable recovery boundary.  The remaining live children are
                # still observed in the next ticks and keep solving meanwhile.
                for item in recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)["items"]:
                    if item.get("state") != "CLAIMED":
                        continue
                    state, action = _tick_claimed_item(loaded, receipt, state, item_id=item["item_id"])
                    actions.append(action)
                    if action["action"] in {"LEASE_RENEWED", "FAST_TERMINAL_CERTIFIED", "CERTIFIED"}:
                        break
                aggregate = _aggregate_if_complete(loaded)
                queue_status = recursive.split_queue_status(Path(loaded["root"]) / supervisor.QUEUE)
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "queue_status": queue_status,
            "actions": actions,
            "aggregate": aggregate,
            "complete": queue_status.get("status") == recursive.QUEUE_STATUS_COMPLETE,
            "hardness_only": aggregate is None,
            "solver_terminal_claim": aggregate is not None,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    tick = sub.add_parser("tick", allow_abbrev=False)
    tick.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action != "tick":  # pragma: no cover - argparse guards this
        raise InitialBatchLifecycleError("unsupported lifecycle action")
    result = tick_bundle(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        InitialBatchLifecycleError,
        initial.InitialBatchDispatchError,
        batch.BatchDispatchError,
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
