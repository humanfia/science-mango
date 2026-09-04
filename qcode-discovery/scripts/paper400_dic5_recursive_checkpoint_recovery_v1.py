#!/usr/bin/env python3
"""Fail-closed recovery helpers for a v1 recursive Paper400 split.

The frozen v1 split supervisor intentionally refuses to dispatch children
unless its sidecar checkpoint receipt exists.  DMTCP can expose a narrow,
benign visibility window: ``checkpoint-stop`` has committed the immutable
checkpoint, while the immediately following status replay still observes the
old inactive transition.  This tool recovers that receipt, then may dispatch
only exact queued child material.  It never resumes a parent, releases a CPU
lease early, or deletes data.

The recovery is deliberately separate from the frozen supervisor source: v1
bundles bind that source by hash.  Before publishing anything, this tool uses
the frozen runner's canonical read-only status action under a shared legacy
root lock and requires an exact CHECKPOINTED transport chain.

It also handles one deliberately narrow child-start race.  A split child can
finish UNSAT between DMTCP's authenticated ``start.commit`` and the frozen
child runner's live-PID session receipt.  That outcome is never trusted from
stdout alone: this module accepts it only after exact controller, queue,
transcript, and stopped-proof checks, then runs the normal independent
DRAT/LRAT/fresh-replay chain before it can certify the queue item.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import os
import stat
import sys
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-checkpoint-recovery-v1"
RECOVERY_KIND = "paper400-dic5-recursive-parent-checkpoint-recovery-v1"
RECOVERY_REASON = "POST_COMMAND_STATUS_VISIBILITY_RACE"

FAST_RECOVERY_KIND = "paper400-dic5-recursive-fast-terminal-recovery-v1"
FAST_TERMINAL_CLAIM_KIND = "paper400-dic5-recursive-fast-terminal-claim-v1"
FAST_CERTIFICATE_KIND = "paper400-dic5-recursive-fast-terminal-unsat-v1"
FAST_VALIDATION_KIND = "paper400-dic5-recursive-fast-terminal-validation-v1"
FAST_FINAL_KIND = "paper400-dic5-recursive-fast-terminal-final-v1"
FAST_FRESH_VALIDATION_KIND = "paper400-dic5-recursive-fast-terminal-fresh-validation-v1"

FAST_RECOVERY = Path("state/06-fast-terminal-recovery.json")
FAST_TERMINAL_CLAIM = Path("state/31-fast-terminal.claim.json")
FAST_FINAL = Path("FAST-TERMINAL-COMMIT.json")

QUEUE_LEDGER_DIR = Path("queue-progress")
QUEUE_BOOTSTRAP = Path("queue-progress/000000-bootstrap.json")
QUEUE_BOOTSTRAP_KIND = "paper400-dic5-recursive-queue-bootstrap-v1"
QUEUE_TRANSITION_KIND = "paper400-dic5-recursive-queue-transition-v1"

MAX_SOLVER_TRANSCRIPT_BYTES = 1 << 20
FAST_UNSAT_STDOUT = b"s UNSATISFIABLE\n"
FAST_START_ERROR = (
    "RecursiveChildRunnerError: unsealed child start commit is not live and bound"
)


class RecursiveCheckpointRecoveryError(RuntimeError):
    """A recovery prerequisite was absent or contradictory."""


def _script_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "recovery_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "frozen_supervisor": supervisor._legacy_source_binding(),
    }


@contextlib.contextmanager
def _legacy_shared_lock(root: Path) -> Iterator[None]:
    """Hold the legacy action lock while replaying and publishing a receipt.

    A shared lock permits the frozen runner's read-only ``status`` subprocess
    to take its own shared lock, while preventing a competing terminal action
    from claiming the parent between the status replay and publication.
    """

    lock = root / ".hierarchical-resume.lock"
    try:
        fd = os.open(lock, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise RecursiveCheckpointRecoveryError("legacy root lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise RecursiveCheckpointRecoveryError("legacy root lock metadata is unsafe")
        try:
            fcntl.flock(fd, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RecursiveCheckpointRecoveryError(
                "legacy root is busy; defer checkpoint receipt recovery"
            ) from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _require_pending_pre_dispatch_state(loaded: Mapping[str, Any]) -> None:
    """Reject a receipt recovery after any child queue transition."""

    bundle = Path(loaded["root"])
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    original = loaded["queue"]
    if (
        queue.get("queue_sha256") != original.get("queue_sha256")
        or queue.get("status") != recursive.QUEUE_STATUS_OPEN
        or not isinstance(queue.get("items"), list)
    ):
        raise RecursiveCheckpointRecoveryError("queue changed after bundle admission")
    for item in queue["items"]:
        if (
            not isinstance(item, dict)
            or item.get("state") != "PENDING"
            or item.get("claim") is not None
            or item.get("attempts") != 0
            or item.get("cpu_ids") != []
        ):
            raise RecursiveCheckpointRecoveryError("queue is no longer pristine")
    workers = bundle / supervisor.WORKERS_DIR
    children = bundle / supervisor.CHILDREN_DIR
    if any(workers.iterdir()) or any(children.iterdir()):
        raise RecursiveCheckpointRecoveryError("child evidence exists before recovery receipt")
    if (bundle / supervisor.PARENT_AGGREGATE).exists():
        raise RecursiveCheckpointRecoveryError("parent aggregate exists before recovery receipt")


def _require_reserved_cpu_leases(loaded: Mapping[str, Any]) -> None:
    """Ensure the admitted child CPUs remain exclusive to this bundle."""

    reservation = loaded["reservation"]
    expected = set(reservation.get("cpus", []))
    if not expected or len(expected) != len(reservation.get("cpus", [])):
        raise RecursiveCheckpointRecoveryError("bundle CPU reservation is malformed")
    catalog = supervisor._load_catalog(Path(loaded["control_root"]))
    matching = [
        entry
        for entry in catalog["leases"]
        if entry.get("bundle") == str(loaded["root"])
    ]
    if (
        len(matching) != len(expected)
        or {entry.get("cpu") for entry in matching} != expected
        or any(
            entry.get("state") != "RESERVED"
            or entry.get("reservation_sha256") != reservation.get("reservation_sha256")
            for entry in matching
        )
    ):
        raise RecursiveCheckpointRecoveryError("reserved CPU leases changed")


def _reconstruct_initial_queue(queue: Mapping[str, Any]) -> dict[str, Any]:
    """Rebuild the admitted zero-event queue from immutable queue fields."""

    unsigned = recursive._queue_unsigned(queue)
    items: list[dict[str, Any]] = []
    for item in queue["items"]:
        reset = recursive._queue_item_unsigned(item)
        reset.update(
            state="PENDING", claim=None, cpu_ids=[], attempts=0,
            last_error=None, certificate_sha256=None,
        )
        items.append(recursive.seal(reset, "item_sha256"))
    unsigned.update(
        items=items,
        event_sequence=0,
        recovery_count=0,
        updated_at=queue["created_at"],
    )
    return recursive._reseal_queue(unsigned)


def _validate_bootstrap_queue_shape(queue: Mapping[str, Any]) -> dict[str, Any]:
    """Admit only the one known, pre-ledger claim transition.

    The frozen supervisor sealed the initial queue hash into ``BUNDLE.json``
    but then legitimately changed that hash on the first claim.  Before this
    sidecar has an append-only transition ledger, accepting arbitrary later
    queue states would be unsafe.  We therefore recover exactly one claim and
    nothing else.
    """

    if (
        queue.get("event_sequence") != 1
        or queue.get("recovery_count") != 0
        or queue.get("status") != recursive.QUEUE_STATUS_OPEN
    ):
        raise RecursiveCheckpointRecoveryError("unledgered queue is not one recoverable claim")
    claimed = [item for item in queue["items"] if item.get("state") == "CLAIMED"]
    if len(claimed) != 1:
        raise RecursiveCheckpointRecoveryError("unledgered queue does not contain exactly one claim")
    for item in queue["items"]:
        if (
            item.get("attempts") != 0
            or item.get("last_error") is not None
            or item.get("certificate_sha256") is not None
        ):
            raise RecursiveCheckpointRecoveryError("unledgered queue has unsupported mutable item fields")
        if item is claimed[0]:
            if not isinstance(item.get("claim"), dict) or not item.get("cpu_ids"):
                raise RecursiveCheckpointRecoveryError("unledgered claimed item is malformed")
        elif (
            item.get("state") != "PENDING"
            or item.get("claim") is not None
            or item.get("cpu_ids") != []
        ):
            raise RecursiveCheckpointRecoveryError("unledgered queue has an unsupported non-claim transition")
    return claimed[0]


def _read_queue_ledger_records(loaded: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Read an append-only sidecar ledger without accepting an unknown file."""

    root = Path(loaded["root"])
    directory = root / QUEUE_LEDGER_DIR
    if not directory.exists() or directory.is_symlink():
        return []
    try:
        safe = supervisor._safe_directory(directory, require_mode_0700=True)
        paths = sorted(safe.iterdir(), key=lambda path: path.name)
    except OSError as exc:
        raise RecursiveCheckpointRecoveryError("queue progress ledger is unreadable") from exc
    if not paths or paths[0].name != QUEUE_BOOTSTRAP.name.split("/")[-1]:
        raise RecursiveCheckpointRecoveryError("queue progress ledger lacks its bootstrap record")
    records: list[dict[str, Any]] = []
    for position, path in enumerate(paths):
        if path.is_symlink() or not path.is_file() or not path.name.endswith(".json"):
            raise RecursiveCheckpointRecoveryError("queue progress ledger contains an unsafe entry")
        if position == 0:
            if path.name != "000000-bootstrap.json":
                raise RecursiveCheckpointRecoveryError("queue progress ledger bootstrap name is invalid")
        elif path.name != f"{position:06d}-transition.json":
            raise RecursiveCheckpointRecoveryError("queue progress ledger transition order is invalid")
        records.append(supervisor._read_json(path))
    return records


def _validate_queue_ledger(
    loaded: Mapping[str, Any], queue: Mapping[str, Any], *, initial_queue: Mapping[str, Any],
) -> dict[str, Any] | None:
    """Validate all sidecar queue transitions and bind the last one to disk."""

    records = _read_queue_ledger_records(loaded)
    if not records:
        return None
    bootstrap = records[0]
    bootstrap_fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "initial_queue_sha256",
        "current_queue_sha256", "queue_id", "event_sequence", "recovery_count",
        "item_id", "worker_sha256", "orphan_worker_sha256", "claim_token", "worker_id",
        "cpu_ids", "source_binding", "record_sha256",
    }
    if (
        set(bootstrap) != bootstrap_fields
        or not recursive.selfhash_valid(bootstrap, "record_sha256")
        or bootstrap.get("schema_version") != SCHEMA_VERSION
        or bootstrap.get("kind") != QUEUE_BOOTSTRAP_KIND
        or bootstrap.get("gate") != GATE
        or bootstrap.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or bootstrap.get("initial_queue_sha256") != loaded["bundle"].get("queue_sha256")
        or bootstrap.get("initial_queue_sha256") != initial_queue.get("queue_sha256")
        or bootstrap.get("queue_id") != queue.get("queue_id")
        or bootstrap.get("event_sequence") != 1
        or bootstrap.get("recovery_count") != 0
        or bootstrap.get("source_binding") != _script_binding()
        or not isinstance(bootstrap.get("cpu_ids"), list)
        or any(type(cpu) is not int or cpu < 0 for cpu in bootstrap["cpu_ids"])
        or any(
            not recursive.is_sha256(bootstrap.get(key))
            for key in (
                "current_queue_sha256", "worker_sha256", "orphan_worker_sha256", "claim_token",
            )
        )
        or type(bootstrap.get("item_id")) is not str
        or type(bootstrap.get("worker_id")) is not str
    ):
        raise RecursiveCheckpointRecoveryError("queue bootstrap ledger record is malformed")
    previous = bootstrap
    for sequence, transition in enumerate(records[1:], start=1):
        fields = {
            "schema_version", "kind", "gate", "bundle_sha256", "previous_record_sha256",
            "before_queue_sha256", "after_queue_sha256", "before_event_sequence",
            "after_event_sequence", "action", "item_id", "binding", "source_binding",
            "record_sha256",
        }
        if (
            set(transition) != fields
            or not recursive.selfhash_valid(transition, "record_sha256")
            or transition.get("schema_version") != SCHEMA_VERSION
            or transition.get("kind") != QUEUE_TRANSITION_KIND
            or transition.get("gate") != GATE
            or transition.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
            or transition.get("previous_record_sha256") != previous.get("record_sha256")
            or transition.get("before_queue_sha256") != previous.get("current_queue_sha256", previous.get("after_queue_sha256"))
            or transition.get("before_event_sequence") != previous.get("event_sequence", previous.get("after_event_sequence"))
            or transition.get("after_event_sequence") != transition.get("before_event_sequence", -1) + 1
            or transition.get("action") not in {"CERTIFY_FAST_TERMINAL", "CLAIM_CHILD"}
            or type(transition.get("item_id")) is not str
            or not isinstance(transition.get("binding"), dict)
            or transition.get("source_binding") != _script_binding()
            or any(
                not recursive.is_sha256(transition.get(key))
                for key in ("previous_record_sha256", "before_queue_sha256", "after_queue_sha256")
            )
        ):
            raise RecursiveCheckpointRecoveryError("queue transition ledger record is malformed")
        previous = transition
    current_sha = previous.get("current_queue_sha256", previous.get("after_queue_sha256"))
    if current_sha != queue.get("queue_sha256"):
        raise RecursiveCheckpointRecoveryError("queue does not match the last ledger transition")
    return previous


def _load_recovery_bundle(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Load a static v1 bundle while replaying allowed queue progress.

    The frozen loader is used unchanged for a pristine queue.  Its only known
    incompatibility is a queue-hash comparison after a legitimate mutation;
    the fallback below duplicates all static checks and then admits only a
    queue that reconstructs to the sealed initial hash plus an append-only
    sidecar history.
    """

    try:
        loaded = supervisor._load_bundle(bundle, control_root=control_root)
    except supervisor.RecursiveSplitSupervisorError as exc:
        if str(exc) != "bundle component binding mismatch":
            raise
    else:
        return {**loaded, "queue_progress_bootstrap_required": False}
    target = supervisor._safe_directory(bundle, require_mode_0700=True)
    control = supervisor._safe_directory(control_root, require_mode_0700=True)
    if target.parent != control:
        raise RecursiveCheckpointRecoveryError("bundle is outside the recursive control root")
    value = supervisor._read_json(target / supervisor.BUNDLE_COMMIT)
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
        raise RecursiveCheckpointRecoveryError("static recursive split bundle is malformed")
    audit = supervisor._read_json(target / supervisor.PARENT_AUDIT)
    supervisor.child_runner._validate_parent_audit(audit)
    manifest = supervisor._read_json(target / supervisor.SPLIT_MANIFEST)
    parent = supervisor._stable_bytes(target / supervisor.PARENT_DIMACS, cap=supervisor.MAX_DIMACS_BYTES, executable=False)
    recursive.verify_cover(manifest, parent)
    reservation = supervisor._read_json(target / supervisor.CPU_RESERVATION)
    if (
        not recursive.selfhash_valid(reservation, "reservation_sha256")
        or reservation.get("kind") != supervisor.CPU_RESERVATION_KIND
        or reservation.get("bundle") != str(target)
        or reservation.get("kernel_hardware_exclusive") is not False
        or reservation.get("scheduler_lease_only") is not True
    ):
        raise RecursiveCheckpointRecoveryError("recursive CPU reservation is malformed")
    queue = recursive.load_split_queue(target / supervisor.QUEUE)
    if (
        audit.get("audit_sha256") != value.get("parent_audit_sha256")
        or manifest.get("manifest_sha256") != value.get("split_manifest_sha256")
        or reservation.get("reservation_sha256") != value.get("cpu_reservation_sha256")
        or manifest.get("split_policy", {}).get("fanout") != value.get("fanout")
        or queue.get("split_manifest_sha256") != manifest.get("manifest_sha256")
        or queue.get("parent_manifest_sha256") != audit.get("parent_static_sha256")
        or queue.get("cpu_pool") != reservation.get("cpus")
    ):
        raise RecursiveCheckpointRecoveryError("mutable queue no longer binds static split material")
    initial_queue = _reconstruct_initial_queue(queue)
    if initial_queue.get("queue_sha256") != value.get("queue_sha256"):
        raise RecursiveCheckpointRecoveryError("mutable queue cannot replay the sealed initial queue")
    loaded = {
        "bundle": value,
        "audit": audit,
        "manifest": manifest,
        "parent": parent,
        "reservation": reservation,
        "queue": queue,
        "root": target,
        "control_root": control,
    }
    last = _validate_queue_ledger(loaded, queue, initial_queue=initial_queue)
    if last is None:
        _validate_bootstrap_queue_shape(queue)
    return {
        **loaded,
        "initial_queue": initial_queue,
        "queue_progress_bootstrap_required": last is None,
    }


def _bootstrap_queue_ledger(loaded: Mapping[str, Any], *, item_id: str) -> dict[str, Any]:
    """Persist the one verified pre-ledger claim before any proof work begins."""

    root = Path(loaded["root"])
    existing = _read_queue_ledger_records(loaded)
    if existing:
        return existing[0]
    if loaded.get("queue_progress_bootstrap_required") is not True:
        raise RecursiveCheckpointRecoveryError("queue bootstrap is not authorized for this bundle")
    item, _worker_path, worker, orphan, queue = _worker_context(
        loaded, item_id=item_id, require_live_claim=True,
    )
    initial = loaded.get("initial_queue")
    if not isinstance(initial, dict) or initial.get("queue_sha256") != loaded["bundle"].get("queue_sha256"):
        raise RecursiveCheckpointRecoveryError("queue bootstrap lacks a reconstructed sealed initial queue")
    record = supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": QUEUE_BOOTSTRAP_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "initial_queue_sha256": initial["queue_sha256"],
            "current_queue_sha256": queue["queue_sha256"],
            "queue_id": queue["queue_id"],
            "event_sequence": queue["event_sequence"],
            "recovery_count": queue["recovery_count"],
            "item_id": item["item_id"],
            "worker_sha256": worker["worker_sha256"],
            "orphan_worker_sha256": orphan["worker_sha256"],
            "claim_token": worker["token"],
            "worker_id": worker["worker_id"],
            "cpu_ids": list(worker["cpu_ids"]),
            "source_binding": _script_binding(),
        },
        "record_sha256",
    )
    directory = root / QUEUE_LEDGER_DIR
    if not directory.exists():
        os.mkdir(directory, 0o700)
        supervisor._fsync_dir(root)
    elif directory.is_symlink():
        raise RecursiveCheckpointRecoveryError("queue progress ledger path is unsafe")
    supervisor._publish_json(root / QUEUE_BOOTSTRAP, record)
    return record


def _append_queue_transition(
    loaded: Mapping[str, Any], *, before: Mapping[str, Any], after: Mapping[str, Any],
    action: str, item_id: str, binding: Mapping[str, Any],
) -> dict[str, Any]:
    """Append one exact queue mutation receipt after the atomic queue update."""

    if action not in {"CERTIFY_FAST_TERMINAL", "CLAIM_CHILD"}:
        raise RecursiveCheckpointRecoveryError("queue transition action is not admitted")
    records = _read_queue_ledger_records(loaded)
    if not records:
        raise RecursiveCheckpointRecoveryError("queue transition has no bootstrap ledger")
    previous = records[-1]
    previous_sha = previous.get("current_queue_sha256", previous.get("after_queue_sha256"))
    previous_event = previous.get("event_sequence", previous.get("after_event_sequence"))
    if (
        before.get("queue_sha256") != previous_sha
        or before.get("event_sequence") != previous_event
        or after.get("event_sequence") != before.get("event_sequence", -1) + 1
    ):
        raise RecursiveCheckpointRecoveryError("queue transition does not follow the append-only ledger")
    record = supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": QUEUE_TRANSITION_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "previous_record_sha256": previous["record_sha256"],
            "before_queue_sha256": before["queue_sha256"],
            "after_queue_sha256": after["queue_sha256"],
            "before_event_sequence": before["event_sequence"],
            "after_event_sequence": after["event_sequence"],
            "action": action,
            "item_id": item_id,
            "binding": dict(binding),
            "source_binding": _script_binding(),
        },
        "record_sha256",
    )
    path = Path(loaded["root"]) / QUEUE_LEDGER_DIR / f"{len(records):06d}-transition.json"
    supervisor._publish_json(path, record)
    return record


def _checkpoint_chain_from_status(
    loaded: Mapping[str, Any], observation: Mapping[str, Any]
) -> dict[str, Any]:
    """Validate frozen-runner status against the audited parent identity."""

    result = observation.get("result")
    if not isinstance(result, dict):
        raise RecursiveCheckpointRecoveryError("canonical status result is malformed")
    audit = loaded["audit"]
    root = Path(audit["parent_root"])
    if (
        result.get("root") != str(root)
        or result.get("resume_static_sha256") != audit.get("parent_static_sha256")
        or result.get("session_sha256") != audit.get("parent_session_sha256")
        or result.get("terminal_claimed") is not False
        or result.get("terminal_committed") is not False
        or not recursive.is_sha256(result.get("record_sha256"))
    ):
        raise RecursiveCheckpointRecoveryError("canonical status does not prove CHECKPOINTED parent")
    chain = result.get("chain")
    if not isinstance(chain, dict) or chain.get("state") != "CHECKPOINTED":
        raise RecursiveCheckpointRecoveryError("canonical transport chain is not CHECKPOINTED")
    generations = chain.get("generations")
    if not isinstance(generations, list) or len(generations) != 1:
        raise RecursiveCheckpointRecoveryError("checkpointed parent has an unexpected generation chain")
    generation = generations[0]
    if not isinstance(generation, dict):
        raise RecursiveCheckpointRecoveryError("checkpointed generation is malformed")
    session = supervisor._read_json(root / "state/11-session.json")
    if (
        supervisor._root_identity(root) != audit.get("parent_root_identity")
        or session.get("record_sha256") != audit.get("parent_session_sha256")
        or generation.get("generation") != audit.get("parent_generation")
        or generation.get("active_kind") != "start.commit"
        or generation.get("active_manifest_sha256") != session.get("controller_start_sha256")
        or generation.get("pid") != audit.get("parent_pid")
        or generation.get("proc_start_ticks") != audit.get("parent_proc_start_ticks")
        or generation.get("pid_identity_alive") is not False
        or not recursive.is_sha256(generation.get("checkpoint_manifest_sha256"))
        or generation.get("checkpoint_manifest_sha256")
        != chain.get("latest_checkpoint_sha256")
        or not isinstance(generation.get("image_bytes"), int)
        or generation["image_bytes"] <= 0
        or not isinstance(chain.get("total_checkpoint_image_bytes"), int)
        or chain["total_checkpoint_image_bytes"] != generation["image_bytes"]
    ):
        raise RecursiveCheckpointRecoveryError("checkpoint chain no longer matches the audited parent")
    return chain


def _require_checkpoint_receipt(loaded: Mapping[str, Any]) -> dict[str, Any]:
    """Bind a pre-dispatch operation to one durable checkpoint receipt."""

    path = Path(loaded["root"]) / supervisor.PARENT_CHECKPOINT
    if not path.exists() or path.is_symlink():
        raise RecursiveCheckpointRecoveryError("parent checkpoint receipt is absent")
    receipt = supervisor._read_json(path)
    audit = loaded["audit"]
    if (
        not recursive.selfhash_valid(receipt, "record_sha256")
        or receipt.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or receipt.get("parent_root") != audit.get("parent_root")
        or receipt.get("parent_static_sha256") != audit.get("parent_static_sha256")
        or receipt.get("parent_session_sha256") != audit.get("parent_session_sha256")
        or receipt.get("parent_pid") != audit.get("parent_pid")
        or receipt.get("parent_proc_start_ticks") != audit.get("parent_proc_start_ticks")
        or receipt.get("parent_state") != "CHECKPOINTED"
    ):
        raise RecursiveCheckpointRecoveryError("parent checkpoint receipt does not bind this bundle")
    return receipt


def _queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    items = queue.get("items")
    if not isinstance(items, list):
        raise RecursiveCheckpointRecoveryError("split queue item list is malformed")
    item = next(
        (candidate for candidate in items if isinstance(candidate, dict) and candidate.get("item_id") == item_id),
        None,
    )
    if item is None:
        raise RecursiveCheckpointRecoveryError("recursive child queue item is absent")
    return item


def _read_regular_bytes(path: Path, *, cap: int) -> bytes:
    """Read one owned regular transcript without following a replacement."""

    try:
        initial = path.lstat()
    except OSError as exc:
        raise RecursiveCheckpointRecoveryError("solver transcript is unavailable") from exc
    if (
        not stat.S_ISREG(initial.st_mode)
        or initial.st_uid != os.geteuid()
        or initial.st_nlink != 1
        or stat.S_IMODE(initial.st_mode) != 0o600
        or initial.st_size < 0
        or initial.st_size > cap
    ):
        raise RecursiveCheckpointRecoveryError("solver transcript metadata is unsafe")
    try:
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise RecursiveCheckpointRecoveryError("solver transcript cannot be opened safely") from exc
    try:
        before = os.fstat(fd)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_dev != initial.st_dev
            or before.st_ino != initial.st_ino
            or before.st_size != initial.st_size
            or before.st_uid != initial.st_uid
            or before.st_nlink != initial.st_nlink
            or stat.S_IMODE(before.st_mode) != stat.S_IMODE(initial.st_mode)
        ):
            raise RecursiveCheckpointRecoveryError("solver transcript changed before read")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, min(1 << 20, cap + 1))
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise RecursiveCheckpointRecoveryError("solver transcript exceeds its cap")
            chunks.append(chunk)
        after = os.fstat(fd)
        if (
            after.st_dev != before.st_dev
            or after.st_ino != before.st_ino
            or after.st_size != before.st_size
            or after.st_mtime_ns != before.st_mtime_ns
            or total != before.st_size
        ):
            raise RecursiveCheckpointRecoveryError("solver transcript changed while read")
        return b"".join(chunks)
    finally:
        os.close(fd)


def _worker_context(
    loaded: Mapping[str, Any], *, item_id: str, require_live_claim: bool,
) -> tuple[dict[str, Any], Path, dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Bind one sidecar worker and its orphan receipt to a queue item."""

    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    item = _queue_item(queue, item_id)
    candidates = [
        (path, record)
        for path, record in supervisor._worker_records(loaded)
        if record.get("item_id") == item_id
    ]
    if len(candidates) != 1:
        raise RecursiveCheckpointRecoveryError("recursive queue item lacks one durable worker record")
    worker_path, worker = candidates[0]
    child_root = Path(worker.get("child_root", ""))
    if (
        worker.get("state") != "CLAIMED"
        or worker.get("leaf_id") != item.get("leaf_id")
        or worker.get("leaf_sha256") != item.get("leaf_sha256")
        or child_root != Path(loaded["root"]) / supervisor.CHILDREN_DIR / item.get("path", "")
        or not recursive.is_sha256(worker.get("worker_sha256"))
    ):
        raise RecursiveCheckpointRecoveryError("recursive worker does not bind its child leaf")
    orphan_path = worker_path.with_name(worker_path.stem + ".orphan.json")
    if not orphan_path.exists() or orphan_path.is_symlink():
        raise RecursiveCheckpointRecoveryError("fast terminal has no durable orphan receipt")
    orphan = supervisor._read_json(orphan_path)
    worker_fields = {
        "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim", "item_id",
        "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids", "claim_expires_at",
        "child_root", "state", "error", "created_at", "worker_sha256",
    }
    if (
        set(orphan) != worker_fields
        or not recursive.selfhash_valid(orphan, "worker_sha256")
        or orphan.get("schema_version") != supervisor.SCHEMA_VERSION
        or orphan.get("kind") != supervisor.WORKER_RECORD_KIND
        or orphan.get("state") != "ORPHAN_UNRESOLVED"
        or orphan.get("error") != FAST_START_ERROR
        or any(
            orphan.get(key) != worker.get(key)
            for key in (
                "bundle_sha256", "queue_sha256_at_claim", "item_id", "leaf_id", "leaf_sha256",
                "token", "worker_id", "cpu_ids", "claim_expires_at", "child_root",
            )
        )
    ):
        raise RecursiveCheckpointRecoveryError("fast-terminal orphan receipt is not exact")
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
            raise RecursiveCheckpointRecoveryError("fast terminal queue claim no longer matches worker")
    elif item.get("state") not in {"CLAIMED", "CERTIFIED"}:
        raise RecursiveCheckpointRecoveryError("fast terminal queue item is neither claimed nor certified")
    return item, worker_path, worker, orphan, queue


def _fast_start_context(root: Path, loaded: Mapping[str, Any]) -> dict[str, Any]:
    """Read the only quiescent transport state eligible for fast recovery."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    if any((target / path).exists() or (target / path).is_symlink() for path in (
        runner.SESSION_COMMIT, runner.TERMINAL_CLAIM, runner.FINAL_COMMIT,
    )):
        raise RecursiveCheckpointRecoveryError("fast terminal conflicts with a sealed normal child state")
    claim = runner._read_start_claim(target, loaded)
    config = runner._load_expected_controller_config(target)
    runtime = target / runner.RUNTIME_ROOT
    with runner._clean_controller_environment():
        status = runner.controller.inspect(runtime, verify_hashes=True)
    generations = status.get("generations")
    if (
        status.get("root") != str(runtime)
        or status.get("config_manifest_sha256") != config.get("self_sha256")
        or status.get("state") != "INACTIVE_UNCHECKPOINTED"
        or not isinstance(generations, list)
        or len(generations) != 1
        or not isinstance(generations[0], dict)
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal transport is not exactly one inactive start")
    generation = generations[0]
    generation_dir = runner.controller._generation_dir(runtime, 0)
    active = runner.controller._active_commit(generation_dir, 0)
    controller_claim = runner.controller.read_manifest(
        generation_dir / "start.claim.json", expected_kind="start.claim",
    )
    if (
        generation.get("generation") != 0
        or generation.get("active_kind") != "start.commit"
        or generation.get("active_manifest_sha256") != active.get("self_sha256")
        or generation.get("pid_identity_alive") is not False
        or generation.get("checkpointed") is not False
        or generation.get("poison_claim") is not None
        or generation.get("stale_tail_injected") is not False
        or active.get("kind") != "start.commit"
        or active.get("generation") != 0
        or active.get("claim_sha256") != controller_claim.get("self_sha256")
        or controller_claim.get("generation") != 0
        or controller_claim.get("init_manifest_sha256") != config.get("self_sha256")
        or type(active.get("pid")) is not int
        or active["pid"] <= 0
        or type(active.get("proc_start_ticks")) is not int
        or active["proc_start_ticks"] < 0
        or active.get("single_process_peer_count") != 1
        or type(active.get("coordinator_port")) is not int
        or not 1 <= active["coordinator_port"] <= 65535
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal start commit is not an exact singleton")
    if any((generation_dir / name).exists() or (generation_dir / name).is_symlink() for name in (
        "checkpoint.claim.json", "checkpoint.commit.json", "resume.claim.json", "resume.commit.json",
    )):
        raise RecursiveCheckpointRecoveryError("fast terminal has checkpoint or resume ambiguity")
    images = generation_dir / "images"
    if images.exists() and any(images.iterdir()):
        raise RecursiveCheckpointRecoveryError("fast terminal retained unexpected checkpoint images")
    stdout_path = runtime / "solver.stdout"
    stderr_path = runtime / "solver.stderr"
    if _read_regular_bytes(stdout_path, cap=MAX_SOLVER_TRANSCRIPT_BYTES) != FAST_UNSAT_STDOUT:
        raise RecursiveCheckpointRecoveryError("fast terminal stdout is not the exact UNSAT transcript")
    if _read_regular_bytes(stderr_path, cap=MAX_SOLVER_TRANSCRIPT_BYTES) != b"":
        raise RecursiveCheckpointRecoveryError("fast terminal stderr is not empty")
    proof_path = runtime / "proof.drat"
    holders = runner._writable_holders(proof_path)
    if holders:
        raise RecursiveCheckpointRecoveryError(f"fast terminal proof has writable holders: {holders}")
    proof = runner.v2._physical_record(
        proof_path, target, "raw-binary-drat", cap=loaded["policy"]["proof_max_bytes"],
    )
    if proof.get("bytes", 0) <= 0:
        raise RecursiveCheckpointRecoveryError("fast terminal proof is empty")
    snapshot = runner.seal(
        {
            "schema_version": runner.SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-stopped-proof-snapshot-v1",
            "transport_state": "INACTIVE_UNCHECKPOINTED",
            "controller_status_sha256": recursive.canonical_sha256(status),
            "latest_generation": 0,
            "latest_pid": active["pid"],
            "latest_proc_start_ticks": active["proc_start_ticks"],
            "latest_pid_identity_alive": False,
            "proof": proof,
            "writable_holders": [],
        },
        "snapshot_sha256",
    )
    return {
        "root": target,
        "claim": claim,
        "config": config,
        "status": status,
        "active": active,
        "snapshot": snapshot,
        "stdout": runner.v2._physical_record(
            stdout_path, target, "solver-stdout", cap=MAX_SOLVER_TRANSCRIPT_BYTES,
        ),
        "stderr": runner.v2._physical_record(
            stderr_path, target, "solver-stderr", cap=MAX_SOLVER_TRANSCRIPT_BYTES,
        ),
    }


def _fast_recovery_value(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, item: Mapping[str, Any],
    worker: Mapping[str, Any], orphan: Mapping[str, Any], context: Mapping[str, Any],
) -> dict[str, Any]:
    """Seal the exact evidence that turns a start race into a stopped proof."""

    child_static = supervisor.child_runner._load_static(Path(context["root"]))["static"]
    child = child_static["child"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAST_RECOVERY_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "root": str(context["root"]),
            "root_identity": supervisor._root_identity(Path(context["root"])),
            "static_sha256": child_static["static_sha256"],
            "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
            "parent_audit_sha256": loaded["audit"]["audit_sha256"],
            "item_id": item["item_id"],
            "queue_item_sha256": item["item_sha256"],
            "leaf_id": child["leaf_id"],
            "leaf_sha256": child["leaf_sha256"],
            "child_cnf_sha256": child["child_cnf_sha256"],
            "child_dimacs_sha256": child["child_dimacs_sha256"],
            "worker_sha256": worker["worker_sha256"],
            "orphan_worker_sha256": orphan["worker_sha256"],
            "claim_token": worker["token"],
            "worker_id": worker["worker_id"],
            "cpu_ids": list(worker["cpu_ids"]),
            "start_claim_sha256": context["claim"]["record_sha256"],
            "controller_config_sha256": context["config"]["self_sha256"],
            "controller_start_sha256": context["active"]["self_sha256"],
            "controller_pid": context["active"]["pid"],
            "controller_proc_start_ticks": context["active"]["proc_start_ticks"],
            "snapshot": dict(context["snapshot"]),
            "solver_stdout": dict(context["stdout"]),
            "solver_stderr": dict(context["stderr"]),
            "hardness_only": False,
            "solver_terminal_claim": False,
            "source_binding": _script_binding(),
        },
        "record_sha256",
    )


def _read_fast_recovery(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, root: Path,
    require_live_claim: bool,
) -> tuple[dict[str, Any], dict[str, Any], tuple[dict[str, Any], Path, dict[str, Any], dict[str, Any], dict[str, Any]]]:
    """Replay a fast-start receipt against current, quiescent child evidence."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    path = target / FAST_RECOVERY
    if not path.exists() or path.is_symlink():
        raise RecursiveCheckpointRecoveryError("fast terminal recovery receipt is absent")
    value = supervisor._read_json(path)
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "parent_checkpoint_sha256",
        "root", "root_identity", "static_sha256", "split_manifest_sha256", "parent_audit_sha256",
        "item_id", "queue_item_sha256", "leaf_id", "leaf_sha256", "child_cnf_sha256",
        "child_dimacs_sha256", "worker_sha256", "orphan_worker_sha256", "claim_token",
        "worker_id", "cpu_ids", "start_claim_sha256", "controller_config_sha256",
        "controller_start_sha256", "controller_pid", "controller_proc_start_ticks", "snapshot",
        "solver_stdout", "solver_stderr", "hardness_only", "solver_terminal_claim",
        "source_binding", "record_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != FAST_RECOVERY_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("parent_checkpoint_sha256") != receipt.get("record_sha256")
        or value.get("root") != str(target)
        or value.get("root_identity") != supervisor._root_identity(target)
        or value.get("split_manifest_sha256") != loaded["manifest"].get("manifest_sha256")
        or value.get("parent_audit_sha256") != loaded["audit"].get("audit_sha256")
        or value.get("hardness_only") is not False
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _script_binding()
        or not isinstance(value.get("cpu_ids"), list)
        or any(type(cpu) is not int or cpu < 0 for cpu in value["cpu_ids"])
        or any(
            not recursive.is_sha256(value.get(key))
            for key in (
                "static_sha256", "leaf_sha256", "child_cnf_sha256", "child_dimacs_sha256",
                "queue_item_sha256", "worker_sha256", "orphan_worker_sha256", "claim_token",
                "start_claim_sha256", "controller_config_sha256", "controller_start_sha256",
            )
        )
        or type(value.get("item_id")) is not str
        or type(value.get("leaf_id")) is not str
        or type(value.get("worker_id")) is not str
        or type(value.get("controller_pid")) is not int
        or value["controller_pid"] <= 0
        or type(value.get("controller_proc_start_ticks")) is not int
        or value["controller_proc_start_ticks"] < 0
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal recovery receipt is malformed")
    context = _fast_start_context(target, runner._load_static(target))
    static = runner._load_static(target)["static"]
    child = static["child"]
    if (
        value.get("static_sha256") != static.get("static_sha256")
        or value.get("leaf_id") != child.get("leaf_id")
        or value.get("leaf_sha256") != child.get("leaf_sha256")
        or value.get("child_cnf_sha256") != child.get("child_cnf_sha256")
        or value.get("child_dimacs_sha256") != child.get("child_dimacs_sha256")
        or value.get("start_claim_sha256") != context["claim"].get("record_sha256")
        or value.get("controller_config_sha256") != context["config"].get("self_sha256")
        or value.get("controller_start_sha256") != context["active"].get("self_sha256")
        or value.get("controller_pid") != context["active"].get("pid")
        or value.get("controller_proc_start_ticks") != context["active"].get("proc_start_ticks")
        or value.get("snapshot") != context["snapshot"]
        or value.get("solver_stdout") != context["stdout"]
        or value.get("solver_stderr") != context["stderr"]
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal recovery evidence changed")
    worker_context = _worker_context(
        loaded, item_id=value["item_id"], require_live_claim=require_live_claim,
    )
    item, _worker_path, worker, orphan, _queue = worker_context
    if (
        worker.get("worker_sha256") != value.get("worker_sha256")
        or orphan.get("worker_sha256") != value.get("orphan_worker_sha256")
        or worker.get("token") != value.get("claim_token")
        or worker.get("worker_id") != value.get("worker_id")
        or worker.get("cpu_ids") != value.get("cpu_ids")
        or item.get("leaf_id") != value.get("leaf_id")
        or item.get("leaf_sha256") != value.get("leaf_sha256")
        or (require_live_claim and item.get("item_sha256") != value.get("queue_item_sha256"))
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal worker/queue binding changed")
    return value, context, worker_context


def _fast_terminal_claim_value(
    loaded: Mapping[str, Any], recovery: Mapping[str, Any], *, root: Path,
    proof_chain: Mapping[str, Any],
) -> dict[str, Any]:
    """Bind a fully replayed proof chain to a fast-start recovery receipt."""

    runner = supervisor.child_runner
    static = runner._load_static(root)["static"]
    child = static["child"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAST_TERMINAL_CLAIM_KIND,
            "gate": GATE,
            "root": str(root),
            "root_identity": supervisor._root_identity(root),
            "static_sha256": static["static_sha256"],
            "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
            "fast_recovery_sha256": recovery["record_sha256"],
            "leaf_id": child["leaf_id"],
            "leaf_sha256": child["leaf_sha256"],
            "child_cnf_sha256": child["child_cnf_sha256"],
            "child_dimacs_sha256": child["child_dimacs_sha256"],
            "snapshot": dict(recovery["snapshot"]),
            "proof_chain": dict(proof_chain),
            "terminal": True,
            "hardness_only": False,
            "solver_terminal_claim": True,
        },
        "terminal_claim_sha256",
    )


def _read_fast_terminal_claim(
    loaded: Mapping[str, Any], recovery: Mapping[str, Any], *, root: Path,
) -> dict[str, Any]:
    runner = supervisor.child_runner
    target = runner._safe_root(root)
    path = target / FAST_TERMINAL_CLAIM
    if not path.exists() or path.is_symlink():
        raise RecursiveCheckpointRecoveryError("fast terminal claim is absent")
    value = supervisor._read_json(path)
    fields = {
        "schema_version", "kind", "gate", "root", "root_identity", "static_sha256",
        "split_manifest_sha256", "fast_recovery_sha256", "leaf_id", "leaf_sha256",
        "child_cnf_sha256", "child_dimacs_sha256", "snapshot", "proof_chain", "terminal",
        "hardness_only", "solver_terminal_claim", "terminal_claim_sha256",
    }
    static = runner._load_static(target)["static"]
    child = static["child"]
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "terminal_claim_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != FAST_TERMINAL_CLAIM_KIND
        or value.get("gate") != GATE
        or value.get("root") != str(target)
        or value.get("root_identity") != supervisor._root_identity(target)
        or value.get("static_sha256") != static.get("static_sha256")
        or value.get("split_manifest_sha256") != loaded["manifest"].get("manifest_sha256")
        or value.get("fast_recovery_sha256") != recovery.get("record_sha256")
        or value.get("leaf_id") != child.get("leaf_id")
        or value.get("leaf_sha256") != child.get("leaf_sha256")
        or value.get("child_cnf_sha256") != child.get("child_cnf_sha256")
        or value.get("child_dimacs_sha256") != child.get("child_dimacs_sha256")
        or value.get("snapshot") != recovery.get("snapshot")
        or value.get("terminal") is not True
        or value.get("hardness_only") is not False
        or value.get("solver_terminal_claim") is not True
    ):
        raise RecursiveCheckpointRecoveryError("fast terminal claim is malformed")
    try:
        runner._validate_terminal_claim_shape({
            "snapshot": value["snapshot"], "proof_chain": value["proof_chain"],
        })
    except runner.RecursiveChildRunnerError as exc:
        raise RecursiveCheckpointRecoveryError("fast terminal proof chain is malformed") from exc
    return value


def _fast_certificate_value(
    loaded: Mapping[str, Any], recovery: Mapping[str, Any], claim: Mapping[str, Any], *, root: Path,
) -> dict[str, Any]:
    runner = supervisor.child_runner
    static = runner._load_static(root)["static"]
    child = static["child"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAST_CERTIFICATE_KIND,
            "gate": GATE,
            "root": str(root),
            "static_sha256": static["static_sha256"],
            "parent_audit_sha256": loaded["audit"]["audit_sha256"],
            "split_manifest_sha256": loaded["manifest"]["manifest_sha256"],
            "fast_recovery_sha256": recovery["record_sha256"],
            "fast_terminal_claim_sha256": claim["terminal_claim_sha256"],
            "leaf_id": child["leaf_id"],
            "leaf_sha256": child["leaf_sha256"],
            "child_cnf_sha256": child["child_cnf_sha256"],
            "child_dimacs_sha256": child["child_dimacs_sha256"],
            "child_num_variables": child["child_num_variables"],
            "child_num_clauses": child["child_num_clauses"],
            "child_dimacs_bytes": child["child_dimacs_bytes"],
            "proof_chain": dict(claim["proof_chain"]),
            "valid": True,
            "strict_proof_unsat": True,
            "proof_replay_complete": True,
            "fresh_proof_replay": True,
            "source_toolchain_fresh": True,
            "hardness_only": False,
            "solver_terminal_claim": True,
            "transport_authority": "TEST_ONLY",
            "transport_trusted_for_scientific_proof": False,
            "global_distance_claim": None,
            "publication_certificate": False,
            "upload_authorized": False,
        },
        "certificate_sha256",
    )


def _fast_validation_value(root: Path, certificate: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAST_VALIDATION_KIND,
            "gate": GATE,
            "root": str(root),
            "certificate": dict(certificate),
            "certificate_sha256": certificate["certificate_sha256"],
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


def _fast_final_value(
    recovery: Mapping[str, Any], claim: Mapping[str, Any], certificate: Mapping[str, Any],
    validation: Mapping[str, Any], *, root: Path,
) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAST_FINAL_KIND,
            "gate": GATE,
            "root": str(root),
            "fast_recovery_sha256": recovery["record_sha256"],
            "fast_terminal_claim_sha256": claim["terminal_claim_sha256"],
            "certificate_sha256": certificate["certificate_sha256"],
            "validation_sha256": validation["validation_sha256"],
            "strict_proof_unsat": True,
            "proof_replay_complete": True,
            "fresh_proof_replay": True,
            "hardness_only": False,
            "solver_terminal_claim": True,
            "global_distance_claim": None,
            "publication_certificate": False,
            "upload_authorized": False,
        },
        "final_sha256",
    )


def _complete_fast_terminal(
    loaded: Mapping[str, Any], recovery: Mapping[str, Any], claim: Mapping[str, Any], *, root: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Publish only deterministic terminal records after a fast claim exists."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    certificate_path = target / runner.CERTIFICATE
    validation_path = target / runner.VALIDATION
    final_path = target / FAST_FINAL
    expected_certificate = _fast_certificate_value(loaded, recovery, claim, root=target)
    if certificate_path.exists() or certificate_path.is_symlink():
        certificate = supervisor._read_json(certificate_path)
        if (
            not recursive.selfhash_valid(certificate, "certificate_sha256")
            or certificate != expected_certificate
        ):
            raise RecursiveCheckpointRecoveryError("existing child certificate conflicts with fast recovery")
    else:
        supervisor._publish_json(certificate_path, expected_certificate)
        certificate = expected_certificate
    expected_validation = _fast_validation_value(target, certificate)
    if validation_path.exists() or validation_path.is_symlink():
        validation = supervisor._read_json(validation_path)
        if (
            not recursive.selfhash_valid(validation, "validation_sha256")
            or validation != expected_validation
        ):
            raise RecursiveCheckpointRecoveryError("existing child validation conflicts with fast recovery")
    else:
        supervisor._publish_json(validation_path, expected_validation)
        validation = expected_validation
    expected_final = _fast_final_value(recovery, claim, certificate, validation, root=target)
    if final_path.exists() or final_path.is_symlink():
        final = supervisor._read_json(final_path)
        if not recursive.selfhash_valid(final, "final_sha256") or final != expected_final:
            raise RecursiveCheckpointRecoveryError("existing fast terminal final record is malformed")
    else:
        supervisor._publish_json(final_path, expected_final)
        final = expected_final
    return certificate, validation, final


def _revalidate_fast_terminal_claim(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, root: Path,
    require_live_claim: bool,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Freshly replay the two proof formats without trusting old checker logs."""

    runner = supervisor.child_runner
    recovery, _context, _worker = _read_fast_recovery(
        loaded, receipt, root=root, require_live_claim=require_live_claim,
    )
    claim = _read_fast_terminal_claim(loaded, recovery, root=root)
    raw_path, raw = runner._bound_claim_artifact(
        root, claim["proof_chain"].get("raw_drat"), role="raw-binary-drat",
        cap=runner._load_static(root)["policy"]["proof_max_bytes"],
    )
    lrat_path, lrat = runner._bound_claim_artifact(
        root, claim["proof_chain"].get("converted_lrat"), role="converted-lrat",
        cap=runner.MAX_PROOF_BYTES,
    )
    child_loaded = runner._load_static(root)
    fresh_drat, _drat_out, _drat_err, _drat_bound = runner._checker(
        root, child_loaded, role="final-drat-replay", proof_path=raw_path,
        proof_record=raw, proof_cap=child_loaded["policy"]["proof_max_bytes"],
    )
    fresh_lrat, _lrat_out, _lrat_err, _lrat_bound = runner._checker(
        root, child_loaded, role="final-lrat-replay", proof_path=lrat_path,
        proof_record=lrat, proof_cap=runner.MAX_PROOF_BYTES,
    )
    if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
        raise RecursiveCheckpointRecoveryError("fast terminal fresh DRAT/LRAT replay failed")
    recovery_after, _context_after, _worker_after = _read_fast_recovery(
        loaded, receipt, root=root, require_live_claim=require_live_claim,
    )
    if recovery_after != recovery:
        raise RecursiveCheckpointRecoveryError("fast terminal evidence changed during fresh replay")
    return recovery, claim, fresh_drat, fresh_lrat


def _recover_fast_terminal_root(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, item: Mapping[str, Any],
    worker: Mapping[str, Any], orphan: Mapping[str, Any], root: Path,
    require_live_claim: bool,
) -> dict[str, Any]:
    """Convert an exact quick exit into a separately certified child result."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    with runner._root_lock(target):
        claim_path = target / FAST_TERMINAL_CLAIM
        if claim_path.exists() or claim_path.is_symlink():
            recovery, claim, _fresh_drat, _fresh_lrat = _revalidate_fast_terminal_claim(
                loaded, receipt, root=target, require_live_claim=require_live_claim,
            )
            certificate, validation, final = _complete_fast_terminal(
                loaded, recovery, claim, root=target,
            )
            return {
                "recovery": recovery,
                "claim": claim,
                "certificate": certificate,
                "validation": validation,
                "final": final,
            }
        recovery_path = target / FAST_RECOVERY
        if recovery_path.exists() or recovery_path.is_symlink():
            recovery, _context, _worker_context = _read_fast_recovery(
                loaded, receipt, root=target, require_live_claim=require_live_claim,
            )
        else:
            child_loaded = runner._load_static(target)
            context = _fast_start_context(target, child_loaded)
            recovery = _fast_recovery_value(
                loaded, receipt, item=item, worker=worker, orphan=orphan, context=context,
            )
            supervisor._publish_json(recovery_path, recovery)
            recovery, _context, _worker_context = _read_fast_recovery(
                loaded, receipt, root=target, require_live_claim=require_live_claim,
            )
        child_loaded = runner._load_static(target)
        snapshot = recovery["snapshot"]
        direct = snapshot["proof"]
        drat, drat_out, drat_err, _drat_bound = runner._checker(
            target, child_loaded, role="drat-verify", proof_path=target / runner.RUNTIME_ROOT / "proof.drat",
            proof_record=direct, proof_cap=child_loaded["policy"]["proof_max_bytes"],
        )
        if drat.get("verified") is not True:
            raise RecursiveCheckpointRecoveryError(
                "fast terminal DRAT preflight failed; no terminal claim was published"
            )
        recovery_after_drat, _context_after_drat, _worker_after_drat = _read_fast_recovery(
            loaded, receipt, root=target, require_live_claim=require_live_claim,
        )
        if recovery_after_drat != recovery:
            raise RecursiveCheckpointRecoveryError("fast terminal evidence changed during DRAT preflight")
        attempt = runner._new_attempt(target)
        raw_path = attempt / "child.drat"
        raw = runner._copy_proof(
            target / runner.RUNTIME_ROOT / "proof.drat", raw_path, root=target,
            expected=direct, cap=child_loaded["policy"]["proof_max_bytes"],
        )
        conversion, lrat, _conversion_out, _conversion_err, _conversion_bound = runner._generate_lrat(
            target, child_loaded, raw_path=raw_path, raw_record=raw, attempt=attempt,
        )
        lrat_path = target / lrat["relative_path"]
        lrat_check, _lrat_out, _lrat_err, _lrat_bound = runner._checker(
            target, child_loaded, role="lrat-check", proof_path=lrat_path,
            proof_record=lrat, proof_cap=runner.MAX_PROOF_BYTES,
        )
        if lrat_check.get("verified") is not True:
            raise RecursiveCheckpointRecoveryError("fast terminal converted LRAT verification failed")
        fresh_drat, _fresh_drat_out, _fresh_drat_err, _fresh_drat_bound = runner._checker(
            target, child_loaded, role="final-drat-replay", proof_path=raw_path,
            proof_record=raw, proof_cap=child_loaded["policy"]["proof_max_bytes"],
        )
        fresh_lrat, _fresh_lrat_out, _fresh_lrat_err, _fresh_lrat_bound = runner._checker(
            target, child_loaded, role="final-lrat-replay", proof_path=lrat_path,
            proof_record=lrat, proof_cap=runner.MAX_PROOF_BYTES,
        )
        if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
            raise RecursiveCheckpointRecoveryError("fast terminal initial fresh replay failed")
        recovery_after_all, _context_after_all, _worker_after_all = _read_fast_recovery(
            loaded, receipt, root=target, require_live_claim=require_live_claim,
        )
        if recovery_after_all != recovery:
            raise RecursiveCheckpointRecoveryError("fast terminal evidence changed during proof chain")
        proof_chain = runner._proof_chain_value(
            raw=raw, lrat=lrat, drat_check=drat, conversion=conversion,
            lrat_check=lrat_check, fresh_drat=fresh_drat, fresh_lrat=fresh_lrat,
            snapshot=snapshot,
        )
        terminal_claim = _fast_terminal_claim_value(
            loaded, recovery, root=target, proof_chain=proof_chain,
        )
        supervisor._publish_json(claim_path, terminal_claim)
        recovery, claim, _last_drat, _last_lrat = _revalidate_fast_terminal_claim(
            loaded, receipt, root=target, require_live_claim=require_live_claim,
        )
        certificate, validation, final = _complete_fast_terminal(
            loaded, recovery, claim, root=target,
        )
        return {
            "recovery": recovery,
            "claim": claim,
            "certificate": certificate,
            "validation": validation,
            "final": final,
            "drat_preflight_stdout_sha256": hashlib.sha256(drat_out).hexdigest(),
            "drat_preflight_stderr_sha256": hashlib.sha256(drat_err).hexdigest(),
        }


def recover_fast_terminal_child(
    bundle: Path, *, item_id: str, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Recover one exact DMTCP quick-exit child; never release its queue lease."""

    loaded = _load_recovery_bundle(bundle, control_root=control_root)
    receipt = _require_checkpoint_receipt(loaded)
    root = Path(loaded["audit"]["parent_root"])
    with _legacy_shared_lock(root):
        _observation, _chain = _checked_checkpointed_parent(loaded)
        if loaded.get("queue_progress_bootstrap_required") is True:
            _bootstrap_queue_ledger(loaded, item_id=item_id)
            loaded = _load_recovery_bundle(bundle, control_root=control_root)
            receipt = _require_checkpoint_receipt(loaded)
            _observation, _chain = _checked_checkpointed_parent(loaded)
        item, _worker_path, worker, orphan, _queue = _worker_context(
            loaded, item_id=item_id, require_live_claim=True,
        )
        return _recover_fast_terminal_root(
            loaded, receipt, item=item, worker=worker, orphan=orphan,
            root=Path(worker["child_root"]), require_live_claim=True,
        )


def verify_fast_terminal_child(
    bundle: Path, *, item_id: str, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Freshly replay a recovered quick-exit child without changing the queue."""

    loaded = _load_recovery_bundle(bundle, control_root=control_root)
    receipt = _require_checkpoint_receipt(loaded)
    root = Path(loaded["audit"]["parent_root"])
    with _legacy_shared_lock(root):
        _observation, _chain = _checked_checkpointed_parent(loaded)
        item, _worker_path, worker, _orphan, _queue = _worker_context(
            loaded, item_id=item_id, require_live_claim=False,
        )
        child_root = Path(worker["child_root"])
        with supervisor.child_runner._root_lock(child_root, exclusive=False):
            recovery, claim, fresh_drat, fresh_lrat = _revalidate_fast_terminal_claim(
                loaded, receipt, root=child_root,
                require_live_claim=item.get("state") == "CLAIMED",
            )
            certificate = supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE)
            expected = _fast_certificate_value(loaded, recovery, claim, root=child_root)
            if certificate != expected:
                raise RecursiveCheckpointRecoveryError("fast terminal certificate does not replay claim")
            validation = supervisor.seal(
                {
                    "schema_version": SCHEMA_VERSION,
                    "kind": FAST_FRESH_VALIDATION_KIND,
                    "gate": GATE,
                    "root": str(child_root),
                    "fast_recovery_sha256": recovery["record_sha256"],
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
            return validation


def certify_fast_terminal_child(
    bundle: Path, *, item_id: str, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Recover, freshly replay, then atomically certify one claimed quick exit."""

    recovered = recover_fast_terminal_child(
        bundle, item_id=item_id, control_root=control_root,
    )
    validation = verify_fast_terminal_child(
        bundle, item_id=item_id, control_root=control_root,
    )
    loaded = _load_recovery_bundle(bundle, control_root=control_root)
    item, _worker_path, worker, _orphan, before_queue = _worker_context(
        loaded, item_id=item_id, require_live_claim=True,
    )
    certificate = recovered["certificate"]
    queue = recursive.certify_queue_item(
        Path(loaded["root"]) / supervisor.QUEUE,
        item_id=item_id,
        worker_id=worker["worker_id"],
        token=worker["token"],
        certificate=certificate,
        validation=validation,
    )
    transition = _append_queue_transition(
        loaded,
        before=before_queue,
        after=queue,
        action="CERTIFY_FAST_TERMINAL",
        item_id=item_id,
        binding={
            "certificate_sha256": certificate["certificate_sha256"],
            "fresh_validation_sha256": validation["validation_sha256"],
            "worker_sha256": worker["worker_sha256"],
            "orphan_worker_sha256": _orphan["worker_sha256"],
            "queue_item_sha256_before": item["item_sha256"],
        },
    )
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-fast-terminal-certification-v1",
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "item_id": item_id,
            "certificate_sha256": certificate["certificate_sha256"],
            "fresh_validation_sha256": validation["validation_sha256"],
            "queue_sha256": queue["queue_sha256"],
            "queue_transition_sha256": transition["record_sha256"],
            "hardness_only": False,
            "solver_terminal_claim": True,
        },
        "record_sha256",
    )


def _checked_checkpointed_parent(
    loaded: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Use the frozen runner's chain record, not an absent top-level state."""

    root = Path(loaded["audit"]["parent_root"])
    supervisor._legacy_terminal_absent(root)
    observation = supervisor._legacy_cli("status", root)
    return observation, _checkpoint_chain_from_status(loaded, observation)


def _recovery_receipt(
    loaded: Mapping[str, Any], observation: Mapping[str, Any], chain: Mapping[str, Any]
) -> dict[str, Any]:
    audit = loaded["audit"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RECOVERY_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "parent_root": audit["parent_root"],
            "parent_static_sha256": audit["parent_static_sha256"],
            "parent_session_sha256": audit["parent_session_sha256"],
            "parent_generation": audit["parent_generation"],
            "parent_pid": audit["parent_pid"],
            "parent_proc_start_ticks": audit["parent_proc_start_ticks"],
            "parent_state": "CHECKPOINTED",
            "checkpoint_manifest_sha256": chain["latest_checkpoint_sha256"],
            "canonical_status": dict(observation),
            "canonical_status_record_sha256": observation["result"]["record_sha256"],
            "recovery_reason": RECOVERY_REASON,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _script_binding(),
        },
        "record_sha256",
    )


def recover_checkpoint_receipt(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT
) -> dict[str, Any]:
    """Publish a receipt only for an already, canonically checkpointed parent."""

    loaded = _load_recovery_bundle(bundle, control_root=control_root)
    receipt_path = Path(loaded["root"]) / supervisor.PARENT_CHECKPOINT
    if receipt_path.exists() or receipt_path.is_symlink():
        existing = supervisor._read_json(receipt_path)
        if not recursive.selfhash_valid(existing, "record_sha256"):
            raise RecursiveCheckpointRecoveryError("existing parent checkpoint receipt is malformed")
        return existing
    root = Path(loaded["audit"]["parent_root"])
    with _legacy_shared_lock(root):
        _require_pending_pre_dispatch_state(loaded)
        observation, chain = _checked_checkpointed_parent(loaded)
        supervisor._legacy_terminal_absent(root)
        with supervisor._catalog_lock(Path(loaded["control_root"])):
            _require_reserved_cpu_leases(loaded)
            receipt = _recovery_receipt(loaded, observation, chain)
            supervisor._publish_json(receipt_path, receipt)
            return receipt


def _require_dispatchable_queue_state(loaded: Mapping[str, Any]) -> set[str]:
    """Require every existing durable worker to match the mutable queue."""

    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    if queue.get("status") != recursive.QUEUE_STATUS_OPEN:
        raise RecursiveCheckpointRecoveryError("recursive queue is not open for child dispatch")
    if (Path(loaded["root"]) / supervisor.PARENT_AGGREGATE).exists():
        raise RecursiveCheckpointRecoveryError("parent aggregate exists while dispatch is requested")
    by_item: dict[str, dict[str, Any]] = {}
    for _path, worker in supervisor._worker_records(loaded):
        item_id = worker.get("item_id")
        if type(item_id) is not str or item_id in by_item:
            raise RecursiveCheckpointRecoveryError("recursive worker records are not one-to-one")
        item = _queue_item(queue, item_id)
        expected_child = Path(loaded["root"]) / supervisor.CHILDREN_DIR / item["path"]
        if (
            worker.get("leaf_id") != item.get("leaf_id")
            or worker.get("leaf_sha256") != item.get("leaf_sha256")
            or worker.get("child_root") != str(expected_child)
        ):
            raise RecursiveCheckpointRecoveryError("recursive worker/static leaf binding changed")
        if item.get("state") == "CLAIMED":
            claim = item.get("claim")
            if (
                not isinstance(claim, dict)
                or worker.get("token") != claim.get("token")
                or worker.get("worker_id") != claim.get("worker_id")
                or worker.get("cpu_ids") != claim.get("cpu_ids")
                or item.get("cpu_ids") != worker.get("cpu_ids")
            ):
                raise RecursiveCheckpointRecoveryError("claimed recursive worker no longer matches queue")
        elif item.get("state") != "CERTIFIED":
            raise RecursiveCheckpointRecoveryError("durable worker has an unsupported queue state")
        by_item[item_id] = worker
    for item in queue["items"]:
        item_id = item["item_id"]
        if item.get("state") == "PENDING" and item_id in by_item:
            raise RecursiveCheckpointRecoveryError("pending recursive queue item retains a worker")
        if item.get("state") in {"CLAIMED", "CERTIFIED"} and item_id not in by_item:
            raise RecursiveCheckpointRecoveryError("active recursive queue item lacks a worker")
    return set(by_item)


def dispatch_children(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
    worker_prefix: str | None = None,
) -> dict[str, Any]:
    """Claim and start pending v1 children after exact checkpoint replay.

    This intentionally remains separate from the frozen v1 supervisor.  It
    preserves the original queue and worker-record format but obtains parent
    state from the frozen runner's ``chain.state`` field.  Its caller must keep
    the service cgroup alive after return so a partial start cannot be cleaned
    up by service exit.
    """

    loaded = _load_recovery_bundle(bundle, control_root=control_root)
    _require_checkpoint_receipt(loaded)
    root = Path(loaded["audit"]["parent_root"])
    with _legacy_shared_lock(root):
        observation, chain = _checked_checkpointed_parent(loaded)
        if loaded.get("queue_progress_bootstrap_required") is True:
            queue = loaded["queue"]
            claimed = [item for item in queue["items"] if item.get("state") == "CLAIMED"]
            if len(claimed) != 1:
                raise RecursiveCheckpointRecoveryError("cannot bootstrap dispatch queue without one claim")
            _bootstrap_queue_ledger(loaded, item_id=claimed[0]["item_id"])
            loaded = _load_recovery_bundle(bundle, control_root=control_root)
            observation, chain = _checked_checkpointed_parent(loaded)
        with supervisor._catalog_lock(Path(loaded["control_root"])):
            _require_reserved_cpu_leases(loaded)
        existing = _require_dispatchable_queue_state(loaded)
        results: list[dict[str, Any]] = []
        prefix = worker_prefix or f"recursive-recovery-{os.uname().nodename}-{os.getpid()}"
        while True:
            before_queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
            claim = recursive.claim_queue_item(
                Path(loaded["root"]) / supervisor.QUEUE,
                worker_id=prefix,
                lease_seconds=supervisor.LEASE_SECONDS,
            )
            if claim is None:
                break
            item = claim["item"]
            if item["item_id"] in existing:
                raise RecursiveCheckpointRecoveryError("queue has duplicate durable worker record")
            child_root = Path(loaded["root"]) / supervisor.CHILDREN_DIR / item["path"]
            initial = supervisor._worker_value(
                loaded, claim, child_root=child_root, state="CLAIMED",
            )
            record_path = supervisor._worker_path(
                Path(loaded["root"]), item["item_id"], claim["claim"]["token"],
            )
            supervisor._publish_json(record_path, initial)
            after_queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
            _append_queue_transition(
                loaded,
                before=before_queue,
                after=after_queue,
                action="CLAIM_CHILD",
                item_id=item["item_id"],
                binding={
                    "worker_sha256": initial["worker_sha256"],
                    "claim_token": claim["claim"]["token"],
                    "worker_id": claim["claim"]["worker_id"],
                    "cpu_ids": list(claim["claim"]["cpu_ids"]),
                    "queue_item_sha256_after": item["item_sha256"],
                },
            )
            try:
                supervisor.child_runner.prepare_root_from_material(
                    child_root,
                    parent_dimacs=loaded["parent"],
                    split_manifest=loaded["manifest"],
                    leaf_path=item["path"],
                    parent_audit=loaded["audit"],
                )
                session = supervisor.child_runner.start_root(
                    child_root, cpu=item["cpu_ids"][0],
                )
            except BaseException as exc:
                orphan = supervisor._worker_value(
                    loaded,
                    claim,
                    child_root=child_root,
                    state="ORPHAN_UNRESOLVED",
                    error=f"{type(exc).__name__}: {exc}",
                )
                supervisor._publish_json(
                    record_path.with_name(record_path.stem + ".orphan.json"), orphan,
                )
                raise
            results.append(
                {
                    "item_id": item["item_id"],
                    "child_root": str(child_root),
                    "session": session,
                }
            )
            existing.add(item["item_id"])
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-checkpoint-recovery-dispatch-v1",
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "checkpoint_manifest_sha256": chain["latest_checkpoint_sha256"],
            "canonical_status_record_sha256": observation["result"]["record_sha256"],
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
    recover = sub.add_parser("recover-receipt", allow_abbrev=False)
    recover.add_argument("--bundle", type=Path, required=True)
    dispatch = sub.add_parser("dispatch", allow_abbrev=False)
    dispatch.add_argument("--bundle", type=Path, required=True)
    fast = sub.add_parser("recover-fast-terminal", allow_abbrev=False)
    fast.add_argument("--bundle", type=Path, required=True)
    fast.add_argument("--item-id", required=True)
    certify_fast = sub.add_parser("certify-fast-terminal", allow_abbrev=False)
    certify_fast.add_argument("--bundle", type=Path, required=True)
    certify_fast.add_argument("--item-id", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "recover-receipt":
        result = recover_checkpoint_receipt(args.bundle, control_root=args.control_root)
    elif args.action == "dispatch":
        result = dispatch_children(args.bundle, control_root=args.control_root)
    elif args.action == "recover-fast-terminal":
        result = recover_fast_terminal_child(
            args.bundle, item_id=args.item_id, control_root=args.control_root,
        )
    elif args.action == "certify-fast-terminal":
        result = certify_fast_terminal_child(
            args.bundle, item_id=args.item_id, control_root=args.control_root,
        )
    else:  # pragma: no cover
        raise RecursiveCheckpointRecoveryError("unknown action")
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        RecursiveCheckpointRecoveryError,
        supervisor.RecursiveSplitSupervisorError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
