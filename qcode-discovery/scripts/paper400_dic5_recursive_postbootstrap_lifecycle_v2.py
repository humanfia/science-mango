#!/usr/bin/env python3
"""Versioned proof lifecycle for post-bootstrap recursive child batches.

Some early recursive bundles authenticated one fast child through the recovery
queue ledger, then atomically claimed the remaining siblings through the
post-bootstrap batch dispatcher.  Their queue is therefore no longer the
pristine hash bound by the frozen supervisor, and it is not an
``initial-batch-dispatch-v1`` bundle either.  Re-running either lifecycle
would be unsafe.

This sidecar first replays the immutable post-bootstrap plan, its commit, and
the complete recovery-ledger prefix.  It seals that already-authenticated
queue as a one-time baseline.  Later ordinary child certification uses a new,
append-only transaction namespace rooted at that baseline.  The frozen bundle,
the recovery ledger, and child start records are never changed by this module.
It neither starts nor resumes a solver, releases an uncertified lease, or
deletes data.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import sys
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v2 as normal_v2
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-postbootstrap-lifecycle-v2"
SIDECAR_DIR = Path("postbootstrap-lifecycle-v2")
BASELINE = SIDECAR_DIR / "000000-baseline.json"
LOCK = Path(".postbootstrap-lifecycle-v2.lock")
TRANSITIONS = SIDECAR_DIR / "queue-transitions"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
BASELINE_KIND = "paper400-dic5-recursive-postbootstrap-lifecycle-baseline-v2"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-postbootstrap-lifecycle-parent-aggregate-v2"
RESULT_KIND = "paper400-dic5-recursive-postbootstrap-lifecycle-tick-v2"


class PostbootstrapLifecycleV2Error(RuntimeError):
    """A post-bootstrap queue handoff cannot be replayed exactly."""


_BASE_SOURCE_BINDING = base._source_binding


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "postbootstrap_lifecycle_v2": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "postbootstrap_batch_dispatch": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "initial_batch_lifecycle_v1_base": _BASE_SOURCE_BINDING(),
        "normal_child_validation_v2": normal_v2._source_binding(),
    }


def _safe_sidecar(bundle: Path) -> Path:
    try:
        return batch._safe_sidecar_dir(bundle, SIDECAR_DIR)
    except batch.BatchDispatchError as exc:
        raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle sidecar is unsafe") from exc


def _postbootstrap_plan_and_commit(
    loaded: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    """Replay the immutable all-sibling claim plan and its historical commit."""

    root = Path(loaded["root"])
    plan_path = root / batch.PLAN
    commit_path = root / batch.COMMIT
    if any(path.is_symlink() or not path.exists() for path in (plan_path, commit_path)):
        raise PostbootstrapLifecycleV2Error("post-bootstrap plan or commit is absent")
    try:
        plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
        records = recovery._read_queue_ledger_records(loaded)
    except (batch.BatchDispatchError, recovery.RecursiveCheckpointRecoveryError) as exc:
        raise PostbootstrapLifecycleV2Error("post-bootstrap queue history is not replayable") from exc
    if not records:
        raise PostbootstrapLifecycleV2Error("post-bootstrap queue lacks its recovery bootstrap")

    value = supervisor._read_json(commit_path)
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "plan_sha256",
        "queue_sha256", "queue_event_sequence", "queue_ledger_sha256",
        "hardness_only", "solver_terminal_claim", "source_binding", "record_sha256",
    }
    final = plan["steps"][-1]["after_queue"]
    matching = [
        record for record in records
        if record.get("after_queue_sha256") == final.get("queue_sha256")
        and record.get("after_event_sequence") == final.get("event_sequence")
    ]
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != batch.SCHEMA_VERSION
        or value.get("kind") != batch.COMMIT_KIND
        or value.get("gate") != batch.GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("plan_sha256") != plan.get("record_sha256")
        or value.get("queue_sha256") != final.get("queue_sha256")
        or value.get("queue_event_sequence") != final.get("event_sequence")
        or len(matching) != 1
        or value.get("queue_ledger_sha256") != matching[0].get("record_sha256")
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != batch._source_binding()
    ):
        raise PostbootstrapLifecycleV2Error("post-bootstrap batch commit is malformed")
    return plan, dict(value), records


def _baseline_value(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], commit: Mapping[str, Any],
    records: list[Mapping[str, Any]], queue: Mapping[str, Any],
) -> dict[str, Any]:
    if not records:
        raise PostbootstrapLifecycleV2Error("baseline lacks a recovery ledger")
    receipt = recovery._require_checkpoint_receipt(loaded)
    last = records[-1]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": BASELINE_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "root": str(loaded["root"]),
            "root_identity": supervisor._root_identity(Path(loaded["root"])),
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "postbootstrap_plan_sha256": plan["record_sha256"],
            "postbootstrap_commit_sha256": commit["record_sha256"],
            "recovery_queue_ledger_sha256": last["record_sha256"],
            "recovery_queue_sha256": queue["queue_sha256"],
            "recovery_queue_event_sequence": queue["event_sequence"],
            "baseline_queue": copy.deepcopy(dict(queue)),
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _read_baseline(bundle: Path) -> dict[str, Any] | None:
    path = bundle / BASELINE
    if path.is_symlink():
        raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle baseline is a symlink")
    if not path.exists():
        return None
    value = supervisor._read_json(path)
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "root", "root_identity",
        "parent_checkpoint_sha256", "postbootstrap_plan_sha256", "postbootstrap_commit_sha256",
        "recovery_queue_ledger_sha256", "recovery_queue_sha256",
        "recovery_queue_event_sequence", "baseline_queue", "hardness_only",
        "solver_terminal_claim", "source_binding", "record_sha256",
    }
    queue = value.get("baseline_queue")
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != BASELINE_KIND
        or value.get("gate") != GATE
        or value.get("root") != str(bundle)
        or not supervisor._same(value.get("root_identity"), supervisor._root_identity(bundle))
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(queue, dict)
        or type(value.get("recovery_queue_event_sequence")) is not int
        or any(
            not recursive.is_sha256(value.get(key))
            for key in (
                "bundle_sha256", "parent_checkpoint_sha256", "postbootstrap_plan_sha256",
                "postbootstrap_commit_sha256", "recovery_queue_ledger_sha256",
                "recovery_queue_sha256",
            )
        )
    ):
        raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle baseline is malformed")
    try:
        recursive._validate_queue(queue)
    except recursive.RecursiveSplitError as exc:
        raise PostbootstrapLifecycleV2Error("baseline queue is malformed") from exc
    if (
        queue.get("queue_sha256") != value.get("recovery_queue_sha256")
        or queue.get("event_sequence") != value.get("recovery_queue_event_sequence")
    ):
        raise PostbootstrapLifecycleV2Error("baseline queue does not bind its recorded state")
    return dict(value)


@contextlib.contextmanager
def _baseline_queue_view(bundle: Path, queue: Mapping[str, Any]) -> Iterator[None]:
    """Let the recovery loader re-validate an immutable pre-lifecycle view.

    The recovery loader deliberately rejects queue changes not represented in
    its own ledger.  Once this lifecycle has made a later transaction, the
    on-disk queue cannot be passed to that loader directly.  Supplying only
    the sealed baseline queue while it replays the static and recovery prefix
    preserves every one of its checks without touching the real queue file.
    """

    original = recursive.load_split_queue
    expected = (bundle / supervisor.QUEUE).resolve()

    def load_baseline(path: Path) -> dict[str, Any]:
        try:
            same = Path(path).resolve() == expected
        except OSError as exc:
            raise PostbootstrapLifecycleV2Error("cannot resolve queue path during baseline replay") from exc
        if same:
            return copy.deepcopy(dict(queue))
        return original(path)

    recursive.load_split_queue = load_baseline
    try:
        yield
    finally:
        recursive.load_split_queue = original


def _load_recovery_prefix(
    bundle: Path, *, control_root: Path, baseline: Mapping[str, Any] | None,
) -> dict[str, Any]:
    try:
        if baseline is None:
            return recovery._load_recovery_bundle(bundle, control_root=control_root)
        with _baseline_queue_view(bundle, baseline["baseline_queue"]):
            return recovery._load_recovery_bundle(bundle, control_root=control_root)
    except (recovery.RecursiveCheckpointRecoveryError, supervisor.RecursiveSplitSupervisorError) as exc:
        raise PostbootstrapLifecycleV2Error("static bundle or recovery prefix no longer replays") from exc


def _load_postbootstrap_batch(
    bundle: Path, *, control_root: Path,
) -> dict[str, Any]:
    """Adapt a post-bootstrap queue handoff to the reviewed lifecycle core."""

    target = Path(bundle)
    baseline = _read_baseline(target)
    loaded = _load_recovery_prefix(target, control_root=control_root, baseline=baseline)
    if loaded.get("queue_progress_bootstrap_required") is True:
        raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle requires an authenticated queue bootstrap")
    plan, commit, records = _postbootstrap_plan_and_commit(loaded)
    baseline_queue = loaded["queue"]
    expected = _baseline_value(
        loaded, plan=plan, commit=commit, records=records, queue=baseline_queue,
    )
    if baseline is None:
        sidecar = _safe_sidecar(target)
        path = sidecar / BASELINE.name
        if path.exists() or path.is_symlink():
            if path.is_symlink() or supervisor._read_json(path) != expected:
                raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle baseline conflicts with replay")
        else:
            supervisor._publish_json(path, expected)
        baseline = expected
    elif baseline != expected:
        raise PostbootstrapLifecycleV2Error("post-bootstrap lifecycle baseline changed")

    # From this point onward the real queue may contain only this lifecycle's
    # append-only suffix.  The base lifecycle verifies that suffix against the
    # immutable queue retained above.
    current = recursive.load_split_queue(target / supervisor.QUEUE)
    return {
        **loaded,
        "queue": current,
        "plan": plan,
        "initial_ledger": baseline,
        "initial_commit": commit,
        "initial_queue": baseline_queue,
        "initial_final_queue": baseline_queue,
        "postbootstrap_baseline": baseline,
    }


def _aggregate_postbootstrap_if_complete(loaded: Mapping[str, Any]) -> dict[str, Any] | None:
    """Aggregate every authenticated sibling without assuming one plan format."""

    root = Path(loaded["root"])
    queue = recursive.load_split_queue(root / supervisor.QUEUE)
    status = recursive.split_queue_status(root / supervisor.QUEUE)
    if status.get("status") != recursive.QUEUE_STATUS_COMPLETE:
        return None

    workers: dict[str, dict[str, Any]] = {}
    try:
        records = supervisor._worker_records(loaded)
    except supervisor.RecursiveSplitSupervisorError as exc:
        raise PostbootstrapLifecycleV2Error("post-bootstrap worker records are malformed") from exc
    for _path, worker in records:
        item_id = worker.get("item_id")
        if type(item_id) is not str or item_id in workers:
            raise PostbootstrapLifecycleV2Error("complete queue has ambiguous worker records")
        workers[item_id] = worker

    item_ids = {item.get("item_id") for item in queue.get("items", []) if isinstance(item, dict)}
    if len(item_ids) != len(queue.get("items", [])) or set(workers) != item_ids:
        raise PostbootstrapLifecycleV2Error("complete queue does not have one worker per child")
    certificates: list[dict[str, Any]] = []
    for item in queue["items"]:
        worker = workers[item["item_id"]]
        child_root = Path(worker.get("child_root", ""))
        if (
            worker.get("leaf_id") != item.get("leaf_id")
            or worker.get("leaf_sha256") != item.get("leaf_sha256")
            or child_root != root / supervisor.CHILDREN_DIR / item.get("path", "")
        ):
            raise PostbootstrapLifecycleV2Error("complete child worker no longer binds its leaf")
        certificates.append(supervisor._read_json(child_root / supervisor.child_runner.CERTIFICATE))
    aggregate = recursive.aggregate_child_certificates(loaded["manifest"], certificates)
    if aggregate.get("status") != "PARENT_CUBE_UNSAT":
        raise PostbootstrapLifecycleV2Error("complete post-bootstrap queue did not aggregate to parent UNSAT")
    expected = supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PARENT_AGGREGATE_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "postbootstrap_batch_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "lifecycle_baseline_sha256": loaded["postbootstrap_baseline"]["record_sha256"],
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
    if path.exists() or path.is_symlink():
        if path.is_symlink() or supervisor._read_json(path) != expected:
            raise PostbootstrapLifecycleV2Error("stored post-bootstrap parent aggregate conflicts with replay")
    else:
        supervisor._publish_json(path, expected)
    supervisor._release_cpus(Path(loaded["control_root"]), loaded["reservation"])
    return expected


@contextlib.contextmanager
def _runtime() -> Iterator[None]:
    """Run the reviewed transaction core with post-bootstrap bindings."""

    replacements: dict[str, Any] = {
        "GATE": GATE,
        "LOCK": LOCK,
        "TRANSITIONS": TRANSITIONS,
        "PREPARES": PREPARES,
        "RECORDS": RECORDS,
        "PARENT_AGGREGATE_KIND": PARENT_AGGREGATE_KIND,
        "RESULT_KIND": RESULT_KIND,
        "_source_binding": _source_binding,
        "_load_initial_batch": _load_postbootstrap_batch,
        "_aggregate_if_complete": _aggregate_postbootstrap_if_complete,
    }
    saved = {name: getattr(base, name) for name in replacements}
    old_verify_final = supervisor.child_runner.verify_final_root
    try:
        for name, value in replacements.items():
            setattr(base, name, value)
        supervisor.child_runner.verify_final_root = normal_v2.verify_normal_final_root_v2
        yield
    finally:
        supervisor.child_runner.verify_final_root = old_verify_final
        for name, value in saved.items():
            setattr(base, name, value)


def tick_bundle(bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT) -> dict[str, Any]:
    """Advance one post-bootstrap bundle without changing its recovery prefix."""

    target = Path(bundle)
    try:
        with batch._batch_lock(target):
            with _runtime():
                return base.tick_bundle(target, control_root=control_root)
    except batch.BatchDispatchError as exc:
        raise PostbootstrapLifecycleV2Error("post-bootstrap dispatcher lock is unavailable") from exc


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
        raise PostbootstrapLifecycleV2Error("unsupported lifecycle action")
    result = tick_bundle(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        PostbootstrapLifecycleV2Error,
        normal_v2.InitialBatchLifecycleV2Error,
        base.InitialBatchLifecycleError,
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
