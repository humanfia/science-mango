#!/usr/bin/env python3
"""Crash-recoverable simultaneous first launch for a pristine recursive split.

The original v1 supervisor can claim and start children one at a time.  That
is safe but operationally poor for a multi-way split: a very quick first cube
can interrupt the call before its siblings receive any start intent.  This
sidecar is for a *pristine*, checkpointed v1 bundle only.  It creates every
queue claim, worker record, and start intent durably before it materialises or
launches a single child; it then creates every ``Popen`` before waiting for
any child-runner result.

The frozen v1 queue bootstrap format represents exactly one pre-ledger claim,
so this initial all-sibling transaction has its own immutable sidecar ledger.
It never changes the sealed initial queue or a parent checkpoint, never
derives UNSAT from a timeout or stdout, and never deletes data.  A child that
finishes before a session receipt is handled only as an exact, still-unproved
fast-terminal orphan.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
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
from scripts import paper400_dic5_recursive_live_session_compat_v1 as compat
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-initial-batch-dispatch-v1"
SIDECAR_DIR = Path("initial-batch-dispatch-v1")
PLAN = SIDECAR_DIR / "000000-plan.json"
LEDGER = SIDECAR_DIR / "000001-initial-claims-ledger.json"
COMMIT = SIDECAR_DIR / "000002-claims-committed.json"
STARTS_DIR = SIDECAR_DIR / "starts"
LOCK = Path(".initial-batch-dispatch-v1.lock")
LEDGER_KIND = "paper400-dic5-recursive-initial-batch-claims-ledger-v1"
COMMIT_KIND = "paper400-dic5-recursive-initial-batch-commit-v1"
RESULT_KIND = "paper400-dic5-recursive-initial-batch-dispatch-result-v1"


class InitialBatchDispatchError(RuntimeError):
    """A pristine bundle cannot safely enter or replay the batch launch."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "initial_batch_dispatch": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "batch_plan": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "live_session_compat": compat._source_binding(),
    }


@contextlib.contextmanager
def _dispatch_lock(bundle: Path) -> Iterator[None]:
    """Exclude all first-batch publishers without retaining the parent lock."""

    path = bundle / LOCK
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise InitialBatchDispatchError("initial batch lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise InitialBatchDispatchError("initial batch lock metadata is unsafe")
        import fcntl
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise InitialBatchDispatchError("another initial batch dispatcher is active") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _safe_sidecar_dir(bundle: Path, relative: Path = SIDECAR_DIR) -> Path:
    return batch._safe_sidecar_dir(bundle, relative)


def _start_paths(bundle: Path, step: Mapping[str, Any]) -> tuple[Path, Path]:
    worker = step["worker"]
    key = f"{step['ordinal']:04d}-{worker['token'][:16]}"
    starts = _safe_sidecar_dir(bundle, STARTS_DIR)
    return starts / f"{key}.intent.json", starts / f"{key}.started.json"


def _load_immutable_components(
    bundle: Path, *, control_root: Path,
) -> dict[str, Any]:
    """Replay frozen static bundle evidence while permitting our known queue state."""

    target = supervisor._safe_directory(bundle, require_mode_0700=True)
    control = supervisor._safe_directory(control_root, require_mode_0700=True)
    if target.parent != control:
        raise InitialBatchDispatchError("bundle is outside the recursive control root")
    value = supervisor._read_json(target / supervisor.BUNDLE_COMMIT)
    fields = {
        "schema_version", "kind", "gate", "bundle_root", "bundle_root_identity",
        "parent_audit_sha256", "split_manifest_sha256", "cpu_reservation_sha256",
        "queue_sha256", "fanout", "source_binding", "hardness_only",
        "parent_solver_terminal_claim", "global_distance_claim",
        "publication_certificate", "upload_authorized", "bundle_sha256",
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
        raise InitialBatchDispatchError("immutable recursive split bundle is malformed")
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
        raise InitialBatchDispatchError("immutable CPU reservation is malformed")
    queue = recursive.load_split_queue(target / supervisor.QUEUE)
    if (
        audit.get("audit_sha256") != value.get("parent_audit_sha256")
        or manifest.get("manifest_sha256") != value.get("split_manifest_sha256")
        or reservation.get("reservation_sha256") != value.get("cpu_reservation_sha256")
        or manifest.get("split_policy", {}).get("fanout") != value.get("fanout")
        or queue.get("split_manifest_sha256") != manifest.get("manifest_sha256")
        or queue.get("cpu_pool") != reservation.get("cpus")
    ):
        raise InitialBatchDispatchError("static bundle component binding changed")
    return {
        "bundle": value,
        "audit": audit,
        "manifest": manifest,
        "parent": parent,
        "reservation": reservation,
        "queue": queue,
        "root": target,
        "control_root": control,
    }


def _ledger_value(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> dict[str, Any]:
    steps = plan["steps"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": LEDGER_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "initial_queue_sha256": plan["initial_queue_sha256"],
            "initial_event_sequence": plan["initial_event_sequence"],
            "final_queue_sha256": plan["final_queue_sha256"],
            "final_event_sequence": plan["final_event_sequence"],
            "item_ids": [step["item_id"] for step in steps],
            "worker_sha256s": [step["worker"]["worker_sha256"] for step in steps],
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _commit_value(loaded: Mapping[str, Any], plan: Mapping[str, Any], ledger: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": COMMIT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "ledger_sha256": ledger["record_sha256"],
            "queue_sha256": plan["final_queue_sha256"],
            "queue_event_sequence": plan["final_event_sequence"],
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        existing = supervisor._read_json(path)
        if existing != value:
            raise InitialBatchDispatchError(f"existing {label} conflicts with replay")
        return
    supervisor._publish_json(path, value)


def _validate_committed_batch(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> dict[str, Any]:
    """Validate the custom first-batch ledger against the mutable queue."""

    bundle = Path(loaded["root"])
    if (bundle / recovery.QUEUE_LEDGER_DIR).exists():
        raise InitialBatchDispatchError("initial batch cannot overlap the v1 single-claim ledger")
    try:
        batch._validate_plan(loaded, plan)
    except batch.BatchDispatchError as exc:
        raise InitialBatchDispatchError("initial batch plan is not replayable") from exc
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    initial = recovery._reconstruct_initial_queue(queue)
    if (
        initial.get("queue_sha256") != loaded["bundle"].get("queue_sha256")
        or initial.get("event_sequence") != 0
        or queue.get("queue_sha256") != plan.get("final_queue_sha256")
        or queue.get("event_sequence") != plan.get("final_event_sequence")
    ):
        raise InitialBatchDispatchError("mutable queue does not replay the initial all-claim plan")
    for step in plan["steps"]:
        worker_path = bundle / supervisor.WORKERS_DIR / step["worker_filename"]
        if not worker_path.exists() or worker_path.is_symlink():
            raise InitialBatchDispatchError("planned worker is absent")
        if supervisor._read_json(worker_path) != step["worker"]:
            raise InitialBatchDispatchError("planned worker changed after publication")
    ledger = _ledger_value(loaded, plan)
    ledger_path = bundle / LEDGER
    _publish_exact(ledger_path, ledger, label="initial batch ledger")
    commit = _commit_value(loaded, plan, ledger)
    _publish_exact(bundle / COMMIT, commit, label="initial batch commit")
    return {**loaded, "queue": queue, "plan": dict(plan), "ledger": ledger, "commit": commit}


def _ensure_claims_committed(
    loaded: Mapping[str, Any], *, worker_prefix: str,
) -> dict[str, Any]:
    """Make all four claims durable before any child materialisation."""

    bundle = Path(loaded["root"])
    plan_path = _safe_sidecar_dir(bundle) / PLAN.name
    current = recursive.load_split_queue(bundle / supervisor.QUEUE)
    if plan_path.exists() or plan_path.is_symlink():
        plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
    else:
        if current.get("queue_sha256") != loaded["bundle"].get("queue_sha256"):
            raise InitialBatchDispatchError("unknown queue mutation precedes initial batch plan")
        plan = batch._plan_value(loaded, worker_prefix=worker_prefix, now=time.time())
        _publish_exact(plan_path, plan, label="initial batch plan")
    for step in plan["steps"]:
        _publish_exact(
            bundle / supervisor.WORKERS_DIR / step["worker_filename"],
            step["worker"], label="initial batch worker",
        )
    batch._publish_final_queue(bundle, plan)
    return _validate_committed_batch(loaded, plan)


def _exact_stopped_fast_context(child_root: Path) -> bool:
    try:
        child_loaded = supervisor.child_runner._load_static(child_root)
        recovery._fast_start_context(child_root, child_loaded)
    except (
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.child_runner.RecursiveChildRunnerError,
    ):
        return False
    return True


def _existing_initial_orphan(
    loaded: Mapping[str, Any], *, item_id: str, worker: Mapping[str, Any],
) -> bool:
    """Recognise only an exact orphan published by this immutable plan.

    The v1 post-bootstrap helper delegates this check to the single-claim
    queue ledger.  Initial batches deliberately use a different all-claim
    ledger, so replay the narrow worker invariants here instead of treating an
    arbitrary file as a reason to skip a launch.
    """

    bundle = Path(loaded["root"])
    path = batch._worker_path(bundle, worker).with_name(
        batch._worker_path(bundle, worker).stem + ".orphan.json"
    )
    if not path.exists() and not path.is_symlink():
        return False
    if path.is_symlink():
        raise InitialBatchDispatchError("initial batch orphan path is unsafe")
    value = supervisor._read_json(path)
    plan = loaded["plan"]
    steps = [step for step in plan["steps"] if step.get("item_id") == item_id]
    if len(steps) != 1:
        raise InitialBatchDispatchError("initial batch orphan has no unique plan step")
    claim = batch._claim_at_step(steps[0])
    item = claim["item"]
    fields = {
        "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim", "item_id",
        "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids", "claim_expires_at",
        "child_root", "state", "error", "created_at", "worker_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "worker_sha256")
        or value.get("schema_version") != supervisor.SCHEMA_VERSION
        or value.get("kind") != supervisor.WORKER_RECORD_KIND
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("queue_sha256_at_claim") != claim.get("queue_sha256")
        or value.get("item_id") != item.get("item_id")
        or value.get("leaf_id") != item.get("leaf_id")
        or value.get("leaf_sha256") != item.get("leaf_sha256")
        or value.get("token") != claim["claim"].get("token")
        or value.get("worker_id") != claim["claim"].get("worker_id")
        or value.get("cpu_ids") != claim["claim"].get("cpu_ids")
        or value.get("claim_expires_at") != claim["claim"].get("lease_expires_at")
        or value.get("child_root") != worker.get("child_root")
        or value.get("state") != "ORPHAN_UNRESOLVED"
        or type(value.get("error")) is not str
        or not value.get("error")
        or type(value.get("created_at")) not in {int, float}
    ):
        raise InitialBatchDispatchError("initial batch orphan does not replay its worker claim")
    return True


def _start_all(loaded: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Materialise and launch all durable claims before observing any result."""

    bundle = Path(loaded["root"])
    plan = loaded["plan"]
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    entries: list[dict[str, Any]] = []
    for step in plan["steps"]:
        item = batch._queue_item(queue, step["item_id"])
        if item.get("state") != "CLAIMED":
            raise InitialBatchDispatchError("batch child left CLAIMED state before launch")
        intent = batch._start_intent_value(plan, step)
        intent_path, started_path = _start_paths(bundle, step)
        _publish_exact(intent_path, intent, label="initial batch start intent")
        entries.append({
            "step": step,
            "item": item,
            "worker": step["worker"],
            "intent": intent,
            "started_path": started_path,
            "child_root": Path(step["worker"]["child_root"]),
            "claim": batch._claim_at_step(step),
        })
    launches: list[dict[str, Any]] = []
    results: list[dict[str, Any]] = []
    failures: list[str] = []
    for entry in entries:
        item, child_root = entry["item"], entry["child_root"]
        if _existing_initial_orphan(loaded, item_id=item["item_id"], worker=entry["worker"]):
            results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
            continue
        if entry["started_path"].exists() or entry["started_path"].is_symlink():
            session = batch._sealed_session_after_external_start(child_root)
            started = batch._start_receipt_value(entry["intent"], session)
            batch._publish_started_receipt(entry["started_path"], started)
            results.append({"item_id": item["item_id"], "state": "ALREADY_SEALED"})
            continue
        try:
            if child_root.is_symlink():
                raise InitialBatchDispatchError("child root is a symlink")
            if not child_root.exists():
                supervisor.child_runner.prepare_root_from_material(
                    child_root, parent_dimacs=loaded["parent"], split_manifest=loaded["manifest"],
                    leaf_path=item["path"], parent_audit=loaded["audit"],
                )
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            batch._write_orphan(loaded, worker=entry["worker"], claim=entry["claim"], child_root=child_root, error=error)
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        launches.append(entry)
    processes: list[tuple[dict[str, Any], Any]] = []
    # This loop deliberately does no process-result observation.
    for entry in launches:
        try:
            processes.append((entry, batch._spawn_child_start(entry["child_root"], cpu=entry["item"]["cpu_ids"][0])))
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            batch._write_orphan(
                loaded, worker=entry["worker"], claim=entry["claim"],
                child_root=entry["child_root"], error=error,
            )
            results.append({"item_id": entry["item"]["item_id"], "state": "START_ERROR", "error": error})
            failures.append(entry["item"]["item_id"])
    for entry, process in processes:
        item, child_root = entry["item"], entry["child_root"]
        try:
            _stdout, stderr = process.communicate()
            returncode = process.returncode
            if type(returncode) is not int:
                raise InitialBatchDispatchError("child start process has no exit status")
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            batch._write_orphan(loaded, worker=entry["worker"], claim=entry["claim"], child_root=child_root, error=error)
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        if returncode == 0:
            try:
                session = batch._sealed_session_after_external_start(child_root)
                started = batch._start_receipt_value(entry["intent"], session)
                batch._publish_started_receipt(entry["started_path"], started)
            except BaseException as exc:
                error = f"{type(exc).__name__}: {exc}"
                results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
                failures.append(item["item_id"])
                continue
            results.append({"item_id": item["item_id"], "state": "RUNNING", "started_sha256": started["record_sha256"]})
            continue
        error = batch._external_start_error(returncode, stderr or b"")
        if error == recovery.FAST_START_ERROR:
            try:
                session = compat.seal_live_session(child_root, cpu=item["cpu_ids"][0])["session"]
            except compat.LiveSessionCompatError as compat_exc:
                if _exact_stopped_fast_context(child_root):
                    batch._write_orphan(loaded, worker=entry["worker"], claim=entry["claim"], child_root=child_root, error=error)
                    results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
                    continue
                deferred = f"{type(compat_exc).__name__}: {compat_exc}"
                batch._write_orphan(loaded, worker=entry["worker"], claim=entry["claim"], child_root=child_root, error=deferred)
                results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": deferred})
                failures.append(item["item_id"])
                continue
            started = batch._start_receipt_value(entry["intent"], session)
            batch._publish_started_receipt(entry["started_path"], started)
            results.append({
                "item_id": item["item_id"],
                "state": "LIVE_SESSION_SEALED_SCHEMA_COMPAT",
                "started_sha256": started["record_sha256"],
            })
            continue
        batch._write_orphan(loaded, worker=entry["worker"], claim=entry["claim"], child_root=child_root, error=error)
        results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
        failures.append(item["item_id"])
    if failures:
        raise InitialBatchDispatchError("one or more initial child starts need audit after all siblings were attempted: " + ",".join(failures))
    return results


def dispatch_initial_batch(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT, worker_prefix: str | None = None,
) -> dict[str, Any]:
    """Atomically claim and concurrently first-start every child in a new bundle."""

    target = Path(bundle)
    with _dispatch_lock(target):
        loaded = _load_immutable_components(target, control_root=control_root)
        parent_receipt = recovery._require_checkpoint_receipt(loaded)
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            _observation, checkpoint_chain = recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            prefix = worker_prefix or f"recursive-initial-batch-{os.uname().nodename}-{os.getpid()}"
            committed = _ensure_claims_committed(loaded, worker_prefix=prefix)
            children = _start_all(committed)
    checkpoint_sha = checkpoint_chain.get("latest_checkpoint_sha256")
    if not recursive.is_sha256(checkpoint_sha):
        raise InitialBatchDispatchError("checkpoint replay did not expose its manifest")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "bundle_sha256": committed["bundle"]["bundle_sha256"],
            "plan_sha256": committed["plan"]["record_sha256"],
            "initial_ledger_sha256": committed["ledger"]["record_sha256"],
            "parent_checkpoint_sha256": parent_receipt["record_sha256"],
            "checkpoint_manifest_sha256": checkpoint_sha,
            "children": children,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
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
    if args.action != "dispatch":  # pragma: no cover - argparse guards this
        raise InitialBatchDispatchError("unsupported action")
    result = dispatch_initial_batch(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        InitialBatchDispatchError,
        compat.LiveSessionCompatError,
        recovery.RecursiveCheckpointRecoveryError,
        batch.BatchDispatchError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
