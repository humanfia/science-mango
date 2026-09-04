#!/usr/bin/env python3
"""Atomically claim all pending post-bootstrap recursive children before start.

The original v1 recovery dispatcher claims a child and immediately starts it.
That is correct for one leaf, but a very fast terminal can raise before the
session receipt is sealed and prematurely stop its loop.  This companion keeps
the immutable v1 sources untouched: for a bundle that already has a valid v1
queue bootstrap, it first publishes a durable batch plan, commits every
pending queue claim and worker record, then starts every sibling.  A fast
terminal remains an orphan that must pass the normal DRAT/LRAT/fresh-replay
chain; it never blocks a later sibling from being started.

The plan contains the full logical queue transition sequence.  It makes the
two physical writes (workers then final queue) recoverable: an interrupted run
can finish the missing v1 transition receipts before it ever touches child
material.  This tool never resumes a parent, releases a lease, or deletes
data.  It deliberately requires an existing v1 bootstrap rather than
inventing a normal-start orphan record for a pristine queue.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import math
import os
import secrets
import stat
import subprocess
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
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-postbootstrap-batch-dispatch-v1"
SIDECAR_DIR = Path("postbootstrap-batch-dispatch-v1")
PLAN = SIDECAR_DIR / "000000-plan.json"
COMMIT = SIDECAR_DIR / "000001-claims-committed.json"
STARTS_DIR = SIDECAR_DIR / "starts"
PLAN_KIND = "paper400-dic5-recursive-postbootstrap-batch-plan-v1"
COMMIT_KIND = "paper400-dic5-recursive-postbootstrap-batch-commit-v1"
START_INTENT_KIND = "paper400-dic5-recursive-postbootstrap-start-intent-v1"
STARTED_KIND = "paper400-dic5-recursive-postbootstrap-started-v1"
MAX_START_STDERR_BYTES = 16 << 10


class BatchDispatchError(RuntimeError):
    """The batch dispatcher cannot prove an operation is recoverable."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "batch_dispatch_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "checkpoint_recovery": recovery._script_binding(),
    }


@contextlib.contextmanager
def _batch_lock(bundle: Path) -> Iterator[None]:
    path = bundle / ".postbootstrap-batch-dispatch-v1.lock"
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise BatchDispatchError("batch dispatcher lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise BatchDispatchError("batch dispatcher lock metadata is unsafe")
        import fcntl
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise BatchDispatchError("another batch dispatcher is active") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            import fcntl
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _safe_sidecar_dir(bundle: Path, relative: Path) -> Path:
    if relative.is_absolute() or not relative.parts or any(part in {"", ".", ".."} for part in relative.parts):
        raise BatchDispatchError("batch sidecar relative path is unsafe")
    path = bundle / relative
    if path.exists():
        if path.is_symlink():
            raise BatchDispatchError("batch sidecar path is unsafe")
        try:
            return supervisor._safe_directory(path, require_mode_0700=True)
        except supervisor.RecursiveSplitSupervisorError as exc:
            raise BatchDispatchError("batch sidecar directory is unsafe") from exc
    if len(relative.parts) > 1:
        _safe_sidecar_dir(bundle, Path(*relative.parts[:-1]))
    try:
        os.mkdir(path, 0o700)
        supervisor._fsync_dir(path.parent)
    except OSError as exc:
        raise BatchDispatchError("cannot create batch sidecar directory") from exc
    return path


def _queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    matches = [
        item for item in queue.get("items", [])
        if isinstance(item, dict) and item.get("item_id") == item_id
    ]
    if len(matches) != 1:
        raise BatchDispatchError("queue item is absent or ambiguous")
    return matches[0]


def _bootstrap_is_present(bundle: Path) -> bool:
    path = bundle / recovery.QUEUE_BOOTSTRAP
    return path.exists() and not path.is_symlink()


def _require_postbootstrap_bundle(
    bundle: Path, *, control_root: Path,
) -> dict[str, Any]:
    loaded = recovery._load_recovery_bundle(bundle, control_root=control_root)
    if loaded.get("queue_progress_bootstrap_required") is True or not _bootstrap_is_present(Path(loaded["root"])):
        raise BatchDispatchError("batch dispatch requires an authenticated v1 queue bootstrap")
    return loaded


def _worker_path(bundle: Path, worker: Mapping[str, Any]) -> Path:
    return supervisor._worker_path(bundle, str(worker["item_id"]), str(worker["token"]))


def _claim_one(
    queue: Mapping[str, Any], *, item_id: str, worker_id: str, token: str, now: float,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Create one logical queue claim without publishing it."""

    before = copy.deepcopy(dict(queue))
    # ``_queue_unsigned`` removes only the outer self-hash.  Deep-copy it
    # again before changing an item, otherwise its nested ``items`` list
    # aliases the immutable ``before`` snapshot kept in the plan.
    value = copy.deepcopy(recursive._queue_unsigned(before))
    occupied = {
        cpu for item in value["items"] if item.get("state") == "CLAIMED"
        for cpu in item.get("cpu_ids", [])
    }
    index = next((i for i, item in enumerate(value["items"]) if item["item_id"] == item_id), None)
    if index is None:
        raise BatchDispatchError("planned queue item disappeared")
    item = value["items"][index]
    if item.get("state") != "PENDING" or item.get("claim") is not None or item.get("cpu_ids") != []:
        raise BatchDispatchError("planned queue item is no longer pending")
    slots = item.get("cpu_slots")
    available = [cpu for cpu in value["cpu_pool"] if cpu not in occupied]
    if type(slots) is not int or slots < 1 or len(available) < slots:
        raise BatchDispatchError("batch has insufficient unclaimed CPU leases")
    cpu_ids = available[:slots]
    claim = {
        "worker_id": worker_id,
        "token": token,
        "claimed_at": now,
        "lease_expires_at": now + float(value["lease_seconds"]),
        "cpu_slots": slots,
        "cpu_ids": cpu_ids,
    }
    unsigned = recursive._queue_item_unsigned(item)
    unsigned.update(state="CLAIMED", claim=claim, cpu_ids=cpu_ids)
    value["items"][index] = recursive.seal(unsigned, "item_sha256")
    value["event_sequence"] += 1
    value["updated_at"] = now
    after = recursive._reseal_queue(value)
    return before, after, _queue_item(after, item_id)


def _plan_value(loaded: Mapping[str, Any], *, worker_prefix: str, now: float) -> dict[str, Any]:
    bundle = Path(loaded["root"])
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    pending = [item for item in queue["items"] if item.get("state") == "PENDING"]
    if not pending:
        raise BatchDispatchError("batch dispatch has no pending children")
    if any(item.get("state") not in {"PENDING", "CLAIMED", "CERTIFIED"} for item in queue["items"]):
        raise BatchDispatchError("queue contains an unsupported state")
    current = queue
    steps: list[dict[str, Any]] = []
    for ordinal, pending_item in enumerate(pending):
        item_id = pending_item["item_id"]
        worker_id = f"{worker_prefix}-{ordinal:02d}"
        token = secrets.token_hex(32)
        before, after, claimed_item = _claim_one(
            current, item_id=item_id, worker_id=worker_id, token=token, now=now,
        )
        claim = {
            "queue_sha256": after["queue_sha256"],
            "item": claimed_item,
            "claim": claimed_item["claim"],
        }
        child_root = bundle / supervisor.CHILDREN_DIR / claimed_item["path"]
        worker = supervisor._worker_value(loaded, claim, child_root=child_root, state="CLAIMED")
        steps.append(
            {
                "ordinal": ordinal,
                "item_id": claimed_item["item_id"],
                "path": claimed_item["path"],
                "before_queue": before,
                "after_queue": after,
                "worker": worker,
                "worker_filename": _worker_path(bundle, worker).name,
            }
        )
        current = after
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PLAN_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "root": str(bundle),
            "root_identity": supervisor._root_identity(bundle),
            "parent_checkpoint_sha256": recovery._require_checkpoint_receipt(loaded)["record_sha256"],
            "initial_queue_sha256": queue["queue_sha256"],
            "initial_event_sequence": queue["event_sequence"],
            "final_queue_sha256": current["queue_sha256"],
            "final_event_sequence": current["event_sequence"],
            "steps": steps,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_plan(loaded: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "root", "root_identity",
        "parent_checkpoint_sha256", "initial_queue_sha256", "initial_event_sequence",
        "final_queue_sha256", "final_event_sequence", "steps", "hardness_only",
        "solver_terminal_claim", "source_binding", "record_sha256",
    }
    bundle = Path(loaded["root"])
    receipt = recovery._require_checkpoint_receipt(loaded)
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != PLAN_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("root") != str(bundle)
        or not supervisor._same(value.get("root_identity"), supervisor._root_identity(bundle))
        or value.get("parent_checkpoint_sha256") != receipt.get("record_sha256")
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(value.get("steps"), list)
        or not value["steps"]
    ):
        raise BatchDispatchError("batch plan is malformed or no longer bound")
    previous: dict[str, Any] | None = None
    item_ids: set[str] = set()
    for ordinal, step in enumerate(value["steps"]):
        required = {
            "ordinal", "item_id", "path", "before_queue", "after_queue", "worker", "worker_filename",
        }
        if set(step) != required or step.get("ordinal") != ordinal:
            raise BatchDispatchError("batch plan step is malformed")
        before, after = step.get("before_queue"), step.get("after_queue")
        if not isinstance(before, dict) or not isinstance(after, dict):
            raise BatchDispatchError("batch plan queue snapshots are malformed")
        try:
            recursive._validate_queue(before)
            recursive._validate_queue(after)
        except recursive.RecursiveSplitError as exc:
            raise BatchDispatchError("batch plan queue snapshot is invalid") from exc
        if previous is not None and before.get("queue_sha256") != previous.get("queue_sha256"):
            raise BatchDispatchError("batch plan queue chain is discontinuous")
        if after.get("event_sequence") != before.get("event_sequence", -1) + 1:
            raise BatchDispatchError("batch plan event sequence is discontinuous")
        item_id = step.get("item_id")
        if type(item_id) is not str or item_id in item_ids:
            raise BatchDispatchError("batch plan item IDs are invalid")
        item_ids.add(item_id)
        item = _queue_item(after, item_id)
        worker = step.get("worker")
        claim = item.get("claim")
        worker_fields = {
            "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim", "item_id",
            "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids", "claim_expires_at",
            "child_root", "state", "error", "created_at", "worker_sha256",
        }
        if (
            not isinstance(worker, dict)
            or set(worker) != worker_fields
            or not recursive.selfhash_valid(worker, "worker_sha256")
            or worker.get("schema_version") != supervisor.SCHEMA_VERSION
            or worker.get("kind") != supervisor.WORKER_RECORD_KIND
            or worker.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
            or worker.get("state") != "CLAIMED"
            or worker.get("error") is not None
            or type(worker.get("created_at")) not in {int, float}
            or not math.isfinite(float(worker["created_at"]))
            or not isinstance(claim, dict)
            or worker.get("item_id") != item_id
            or worker.get("leaf_id") != item.get("leaf_id")
            or worker.get("leaf_sha256") != item.get("leaf_sha256")
            or worker.get("token") != claim.get("token")
            or worker.get("worker_id") != claim.get("worker_id")
            or worker.get("cpu_ids") != item.get("cpu_ids")
            or worker.get("queue_sha256_at_claim") != after.get("queue_sha256")
            or worker.get("claim_expires_at") != claim.get("lease_expires_at")
            or worker.get("child_root") != str(bundle / supervisor.CHILDREN_DIR / item.get("path", ""))
            or step.get("worker_filename") != _worker_path(bundle, worker).name
        ):
            raise BatchDispatchError("batch plan worker binding is invalid")
        if type(claim.get("claimed_at")) not in {int, float}:
            raise BatchDispatchError("batch plan claim timestamp is invalid")
        try:
            expected_before, expected_after, expected_item = _claim_one(
                before,
                item_id=item_id,
                worker_id=worker["worker_id"],
                token=worker["token"],
                now=float(claim["claimed_at"]),
            )
        except (KeyError, TypeError, ValueError, recursive.RecursiveSplitError) as exc:
            raise BatchDispatchError("batch plan claim transition cannot be replayed") from exc
        if expected_before != before or expected_after != after or expected_item != item:
            raise BatchDispatchError("batch plan changes more than its one queued claim")
        if step.get("path") != item.get("path"):
            raise BatchDispatchError("batch plan path does not bind its queued child")
        previous = after
    if (
        value.get("initial_queue_sha256") != value["steps"][0]["before_queue"].get("queue_sha256")
        or value.get("initial_event_sequence") != value["steps"][0]["before_queue"].get("event_sequence")
        or value.get("final_queue_sha256") != previous.get("queue_sha256")
        or value.get("final_event_sequence") != previous.get("event_sequence")
    ):
        raise BatchDispatchError("batch plan endpoints are invalid")
    return dict(value)


def _publish_planned_workers(bundle: Path, plan: Mapping[str, Any]) -> None:
    for step in plan["steps"]:
        path = bundle / supervisor.WORKERS_DIR / step["worker_filename"]
        if path.exists() or path.is_symlink():
            existing = supervisor._read_json(path)
            if existing != step["worker"]:
                raise BatchDispatchError("planned worker path already has different evidence")
        else:
            supervisor._publish_json(path, step["worker"])


def _publish_final_queue(bundle: Path, plan: Mapping[str, Any]) -> None:
    before = plan["steps"][0]["before_queue"]
    final = plan["steps"][-1]["after_queue"]
    queue_path = bundle / supervisor.QUEUE
    lock = recursive._ensure_queue_lock(queue_path)
    with recursive._exclusive_lock(lock, blocking=True):
        current = recursive.load_split_queue(queue_path)
        if current.get("queue_sha256") == final.get("queue_sha256"):
            return
        if current.get("queue_sha256") != before.get("queue_sha256"):
            raise BatchDispatchError("queue changed outside the durable batch plan")
        recursive._atomic_write_queue(queue_path, final)


def _append_missing_transitions(bundle: Path, loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> None:
    records = recovery._read_queue_ledger_records(loaded)
    if not records:
        raise BatchDispatchError("v1 queue ledger unexpectedly lacks a bootstrap")
    current_sha = records[-1].get("current_queue_sha256", records[-1].get("after_queue_sha256"))
    for step in plan["steps"]:
        before = step["before_queue"]
        after = step["after_queue"]
        if current_sha == after["queue_sha256"]:
            continue
        if current_sha != before["queue_sha256"]:
            raise BatchDispatchError("queue ledger diverged from durable batch plan")
        item = _queue_item(after, step["item_id"])
        worker = step["worker"]
        recovery._append_queue_transition(
            loaded,
            before=before,
            after=after,
            action="CLAIM_CHILD",
            item_id=item["item_id"],
            binding={
                "worker_sha256": worker["worker_sha256"],
                "claim_token": worker["token"],
                "worker_id": worker["worker_id"],
                "cpu_ids": list(worker["cpu_ids"]),
                "queue_item_sha256_after": item["item_sha256"],
            },
        )
        current_sha = after["queue_sha256"]
    if current_sha != plan["final_queue_sha256"]:
        raise BatchDispatchError("batch transition ledger did not reach final queue")


def _commit_value(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> dict[str, Any]:
    records = recovery._read_queue_ledger_records(loaded)
    if not records:
        raise BatchDispatchError("batch commit lacks a queue ledger")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": COMMIT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "queue_sha256": plan["final_queue_sha256"],
            "queue_event_sequence": plan["final_event_sequence"],
            "queue_ledger_sha256": records[-1].get("record_sha256"),
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _ensure_claims_committed(
    bundle: Path, *, control_root: Path, plan: Mapping[str, Any], loaded: Mapping[str, Any],
) -> dict[str, Any]:
    _publish_planned_workers(bundle, plan)
    _publish_final_queue(bundle, plan)
    _append_missing_transitions(bundle, loaded, plan)
    replay = _require_postbootstrap_bundle(bundle, control_root=control_root)
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    if queue.get("queue_sha256") != plan.get("final_queue_sha256"):
        raise BatchDispatchError("final queue cannot be replayed after batch commit")
    _ = recovery._require_dispatchable_queue_state(replay)
    sidecar = _safe_sidecar_dir(bundle, SIDECAR_DIR)
    commit_path = sidecar / COMMIT.name
    expected = _commit_value(replay, plan)
    if commit_path.exists() or commit_path.is_symlink():
        existing = supervisor._read_json(commit_path)
        if existing != expected:
            raise BatchDispatchError("batch commit receipt changed")
    else:
        supervisor._publish_json(commit_path, expected)
    return replay


def _bare_loaded_for_interrupted_commit(bundle: Path) -> dict[str, Any]:
    """Load only the immutable pieces needed to finish a planned ledger write.

    This path is used solely after the atomic final queue replacement but
    before all v1 transition receipts are present.  The normal v1 loader must
    reject that temporary state, so it cannot be used to recover it.
    """

    target = supervisor._safe_directory(bundle, require_mode_0700=True)
    value = supervisor._read_json(target / supervisor.BUNDLE_COMMIT)
    audit = supervisor._read_json(target / supervisor.PARENT_AUDIT)
    fields = {
        "schema_version", "kind", "gate", "bundle_root", "bundle_root_identity",
        "parent_audit_sha256", "split_manifest_sha256", "cpu_reservation_sha256",
        "queue_sha256", "fanout", "source_binding", "hardness_only",
        "parent_solver_terminal_claim", "global_distance_claim", "publication_certificate",
        "upload_authorized", "bundle_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "bundle_sha256")
        or value.get("schema_version") != supervisor.SCHEMA_VERSION
        or value.get("kind") != supervisor.BUNDLE_KIND
        or value.get("gate") != supervisor.GATE
        or value.get("bundle_root") != str(target)
        or not supervisor._same(value.get("bundle_root_identity"), supervisor._root_identity(target))
        or value.get("hardness_only") is not True
        or value.get("parent_solver_terminal_claim") is not False
        or value.get("global_distance_claim") is not None
        or value.get("publication_certificate") is not False
        or value.get("upload_authorized") is not False
        or not supervisor._same(value.get("source_binding"), supervisor._legacy_source_binding())
    ):
        raise BatchDispatchError("interrupted batch bundle envelope is malformed")
    try:
        supervisor.child_runner._validate_parent_audit(audit)
    except supervisor.child_runner.RecursiveChildRunnerError as exc:
        raise BatchDispatchError("interrupted batch parent audit is malformed") from exc
    if audit.get("audit_sha256") != value.get("parent_audit_sha256"):
        raise BatchDispatchError("interrupted batch audit no longer binds its bundle")
    return {"root": target, "bundle": value, "audit": audit}


def _recover_interrupted_final_queue(bundle: Path) -> None:
    """Finish only the ledger suffix proven by an immutable batch plan."""

    sidecar = bundle / SIDECAR_DIR
    plan_path = sidecar / PLAN.name
    if not plan_path.exists() or plan_path.is_symlink():
        raise BatchDispatchError("queue is ahead of its ledger without a batch plan")
    bare = _bare_loaded_for_interrupted_commit(bundle)
    plan = _validate_plan(bare, supervisor._read_json(plan_path))
    current = recursive.load_split_queue(bundle / supervisor.QUEUE)
    if current.get("queue_sha256") != plan.get("final_queue_sha256"):
        raise BatchDispatchError("interrupted batch queue is not the planned final queue")
    _publish_planned_workers(bundle, plan)
    _append_missing_transitions(bundle, bare, plan)


def _start_intent_value(plan: Mapping[str, Any], step: Mapping[str, Any]) -> dict[str, Any]:
    worker = step["worker"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": START_INTENT_KIND,
            "gate": GATE,
            "plan_sha256": plan["record_sha256"],
            "item_id": step["item_id"],
            "worker_sha256": worker["worker_sha256"],
            "claim_token": worker["token"],
            "child_root": worker["child_root"],
            "cpu_ids": list(worker["cpu_ids"]),
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _start_receipt_value(intent: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    session_sha = session.get("record_sha256")
    if not recursive.is_sha256(session_sha):
        raise BatchDispatchError("child start did not return a sealed session")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": STARTED_KIND,
            "gate": GATE,
            "intent_sha256": intent["record_sha256"],
            "child_root": intent["child_root"],
            "expected_single_cpu": intent["cpu_ids"][0],
            "session_sha256": session_sha,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _publish_started_receipt(path: Path, expected: Mapping[str, Any]) -> None:
    if path.exists() or path.is_symlink():
        existing = supervisor._read_json(path)
        if existing != expected:
            raise BatchDispatchError("child started receipt does not bind its sealed session")
        return
    supervisor._publish_json(path, expected)


def _claim_at_step(step: Mapping[str, Any]) -> dict[str, Any]:
    """Return the immutable queue claim as it existed for one worker.

    The final queue hash is necessarily different after later batch claims.
    A fast-terminal orphan must retain the worker's *own* claim hash, because
    the frozen recovery helper compares that value exactly before it can
    certify a proof.
    """

    after = step["after_queue"]
    item = _queue_item(after, step["item_id"])
    return {
        "queue_sha256": after["queue_sha256"],
        "item": item,
        "claim": item["claim"],
    }


def _write_orphan(
    loaded: Mapping[str, Any], *, worker: Mapping[str, Any], claim: Mapping[str, Any],
    child_root: Path, error: str,
) -> Path:
    """Record an unresolved launch outcome once, without overwriting evidence."""

    path = _worker_path(Path(loaded["root"]), worker).with_name(
        _worker_path(Path(loaded["root"]), worker).stem + ".orphan.json"
    )
    value = supervisor._worker_value(
        loaded, claim, child_root=child_root, state="ORPHAN_UNRESOLVED", error=error,
    )
    if path.exists() or path.is_symlink():
        existing = supervisor._read_json(path)
        if existing != value:
            # ``created_at`` deliberately differs for a newly constructed
            # value.  Compare the invariant worker binding separately and
            # never overwrite a prior forensic receipt.
            required = {
                "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim", "item_id",
                "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids", "claim_expires_at",
                "child_root", "state", "error", "created_at", "worker_sha256",
            }
            invariant = (
                set(existing) == required
                and recursive.selfhash_valid(existing, "worker_sha256")
                and existing.get("state") == "ORPHAN_UNRESOLVED"
                and existing.get("error") == error
                and all(
                    existing.get(key) == value.get(key)
                    for key in (
                        "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim",
                        "item_id", "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids",
                        "claim_expires_at", "child_root",
                    )
                )
            )
            if not invariant:
                raise BatchDispatchError("child start failure conflicts with an orphan receipt")
        return path
    supervisor._publish_json(path, value)
    return path


def _existing_fast_orphan(
    loaded: Mapping[str, Any], *, item_id: str, worker: Mapping[str, Any],
) -> bool:
    """Accept an old orphan only through frozen fast-terminal validation."""

    orphan_path = _worker_path(Path(loaded["root"]), worker).with_name(
        _worker_path(Path(loaded["root"]), worker).stem + ".orphan.json"
    )
    if not orphan_path.exists() and not orphan_path.is_symlink():
        return False
    try:
        _item, _path, recovered_worker, _orphan, _queue = recovery._worker_context(
            loaded, item_id=item_id, require_live_claim=True,
        )
    except recovery.RecursiveCheckpointRecoveryError as exc:
        raise BatchDispatchError("existing orphan is not an exact fast-terminal receipt") from exc
    if recovered_worker != worker:
        raise BatchDispatchError("existing orphan belongs to a different worker")
    return True


def _sealed_session_after_external_start(child_root: Path) -> dict[str, Any]:
    """Read a sealed session without retrying or otherwise mutating a child."""

    runner = supervisor.child_runner
    target = runner._safe_root(child_root)
    with runner._root_lock(target, exclusive=False):
        loaded = runner._load_static(target)
        return runner._load_session(target, loaded)


def _spawn_child_start(child_root: Path, *, cpu: int) -> subprocess.Popen[bytes]:
    """Start one frozen child runner in its own process-affinity namespace."""

    script = Path(supervisor.child_runner.__file__).resolve(strict=True)
    return subprocess.Popen(
        [str(Path(sys.executable).resolve(strict=True)), str(script), "start", "--root", str(child_root), "--cpu", str(cpu)],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        close_fds=True,
    )


def _external_start_error(returncode: int, stderr: bytes) -> str:
    """Classify only the one frozen-runner fast-terminal signal as recoverable."""

    if len(stderr) > MAX_START_STDERR_BYTES:
        return "external child start emitted excessive stderr"
    text = stderr.decode("utf-8", "replace").strip()
    if returncode == 2 and text == "ERROR: unsealed child start commit is not live and bound":
        return recovery.FAST_START_ERROR
    if not text:
        text = "no diagnostic"
    return f"external child start failed rc={returncode}: {text[-2000:]}"


def _start_all(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Publish every intent, prepare every root, then launch all siblings.

    ``start_root`` changes process-global affinity, resource limits, and the
    DMTCP environment.  Running it in threads would therefore race.  Each
    child is instead started through the frozen CLI in a distinct process;
    all ``Popen`` calls happen before waiting for any result.  A fast terminal
    or an unexpected one-child failure is recorded, but never prevents a
    later sibling from receiving its own start attempt.
    """

    bundle = Path(loaded["root"])
    starts = _safe_sidecar_dir(bundle, STARTS_DIR)
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    entries: list[dict[str, Any]] = []
    for step in plan["steps"]:
        worker = step["worker"]
        item = _queue_item(queue, step["item_id"])
        if item.get("state") != "CLAIMED":
            raise BatchDispatchError("batch item left CLAIMED state before start")
        intent = _start_intent_value(plan, step)
        key = f"{step['ordinal']:04d}-{worker['token'][:16]}"
        intent_path = starts / f"{key}.intent.json"
        started_path = starts / f"{key}.started.json"
        if intent_path.exists() or intent_path.is_symlink():
            existing_intent = supervisor._read_json(intent_path)
            if existing_intent != intent:
                raise BatchDispatchError("child start intent changed")
        else:
            supervisor._publish_json(intent_path, intent)
        entries.append(
            {
                "step": step, "worker": worker, "item": item, "intent": intent,
                "started_path": started_path, "child_root": Path(worker["child_root"]),
                "claim": _claim_at_step(step),
            }
        )

    results: list[dict[str, Any]] = []
    failures: list[str] = []
    launches: list[dict[str, Any]] = []
    # No child process is started until all durable start intents are present.
    for entry in entries:
        worker, item, child_root = entry["worker"], entry["item"], entry["child_root"]
        if _existing_fast_orphan(loaded, item_id=item["item_id"], worker=worker):
            results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
            continue
        started_path = entry["started_path"]
        if started_path.exists() or started_path.is_symlink():
            existing = supervisor._read_json(started_path)
            session = _sealed_session_after_external_start(child_root)
            expected = _start_receipt_value(entry["intent"], session)
            if existing != expected:
                raise BatchDispatchError("child started receipt does not bind its sealed session")
            results.append({"item_id": item["item_id"], "state": "RUNNING", "started_sha256": expected["record_sha256"]})
            continue
        try:
            if child_root.is_symlink():
                raise BatchDispatchError("child root is a symlink")
            if not child_root.exists():
                supervisor.child_runner.prepare_root_from_material(
                    child_root,
                    parent_dimacs=loaded["parent"],
                    split_manifest=loaded["manifest"],
                    leaf_path=item["path"],
                    parent_audit=loaded["audit"],
                )
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            _write_orphan(
                loaded, worker=worker, claim=entry["claim"], child_root=child_root, error=error,
            )
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        launches.append(entry)

    processes: list[tuple[dict[str, Any], subprocess.Popen[bytes]]] = []
    # Launch every prepared sibling before observing the first completion.
    for entry in launches:
        try:
            process = _spawn_child_start(entry["child_root"], cpu=entry["item"]["cpu_ids"][0])
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            _write_orphan(
                loaded, worker=entry["worker"], claim=entry["claim"],
                child_root=entry["child_root"], error=error,
            )
            results.append({"item_id": entry["item"]["item_id"], "state": "START_ERROR", "error": error})
            failures.append(entry["item"]["item_id"])
            continue
        processes.append((entry, process))

    for entry, process in processes:
        item = entry["item"]
        try:
            _stdout, stderr = process.communicate()
            returncode = process.returncode
            if type(returncode) is not int:
                raise BatchDispatchError("child start process has no exit status")
        except BaseException as exc:
            # The process outcome itself is unknown, so retain a forensic
            # orphan rather than attempting any automatic retry.
            error = f"{type(exc).__name__}: {exc}"
            _write_orphan(
                loaded, worker=entry["worker"], claim=entry["claim"],
                child_root=entry["child_root"], error=error,
            )
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        if returncode == 0:
            try:
                session = _sealed_session_after_external_start(entry["child_root"])
                started = _start_receipt_value(entry["intent"], session)
                _publish_started_receipt(entry["started_path"], started)
            except BaseException as exc:
                # A successful frozen CLI followed by an unreadable session
                # is not the fast-start race.  Do not manufacture an orphan
                # that could contradict a real sealed child; leave the start
                # intent plus child root for a separate exact audit.
                error = f"{type(exc).__name__}: {exc}"
                results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
                failures.append(item["item_id"])
                continue
            results.append({
                "item_id": item["item_id"], "state": "RUNNING",
                "started_sha256": started["record_sha256"],
            })
            continue
        error = _external_start_error(returncode, stderr or b"")
        _write_orphan(
            loaded, worker=entry["worker"], claim=entry["claim"],
            child_root=entry["child_root"], error=error,
        )
        if error == recovery.FAST_START_ERROR:
            results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
        else:
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
    if failures:
        raise BatchDispatchError(
            "one or more child starts need audit after all siblings were attempted: " + ",".join(failures)
        )
    return results


def dispatch_pending_batch(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT, worker_prefix: str | None = None,
) -> dict[str, Any]:
    """Claim all current pending leaves, then start every sibling independently."""

    target = Path(bundle)
    with _batch_lock(target):
        try:
            loaded = _require_postbootstrap_bundle(target, control_root=control_root)
        except (recovery.RecursiveCheckpointRecoveryError, supervisor.RecursiveSplitSupervisorError):
            _recover_interrupted_final_queue(target)
            loaded = _require_postbootstrap_bundle(target, control_root=control_root)
        receipt = recovery._require_checkpoint_receipt(loaded)
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            _observation, chain = recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            sidecar = _safe_sidecar_dir(target, SIDECAR_DIR)
            plan_path = sidecar / PLAN.name
            if plan_path.exists() or plan_path.is_symlink():
                plan = _validate_plan(loaded, supervisor._read_json(plan_path))
            else:
                prefix = worker_prefix or f"recursive-batch-{os.uname().nodename}-{os.getpid()}"
                plan = _plan_value(loaded, worker_prefix=prefix, now=time.time())
                supervisor._publish_json(plan_path, plan)
            replay = _ensure_claims_committed(
                target, control_root=control_root, plan=plan, loaded=loaded,
            )
            results = _start_all(replay, plan)
            return supervisor.seal(
                {
                    "schema_version": SCHEMA_VERSION,
                    "kind": "paper400-dic5-recursive-postbootstrap-batch-dispatch-result-v1",
                    "gate": GATE,
                    "bundle_sha256": replay["bundle"]["bundle_sha256"],
                    "parent_checkpoint_sha256": receipt["record_sha256"],
                    "checkpoint_manifest_sha256": chain["latest_checkpoint_sha256"],
                    "plan_sha256": plan["record_sha256"],
                    "children": results,
                    "hardness_only": True,
                    "solver_terminal_claim": False,
                },
                "record_sha256",
            )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    dispatch = sub.add_parser("dispatch", allow_abbrev=False)
    dispatch.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = dispatch_pending_batch(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        BatchDispatchError,
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
