#!/usr/bin/env python3
"""Visibility-safe batch launch for post-bootstrap recursive children.

This is the successor to the v1 post-bootstrap dispatcher.  It retains the
v1 durable queue-plan format so that claims, worker records, and transition
ledger replay remain exact, but closes one launch-time observation race:
after an external frozen child runner reports an unsealed start commit, v2
asks that same frozen runner once more to seal a now-visible live session.
Only if a stopped proof transport passes the exact fast-terminal context check
does v2 write the ordinary fast-terminal orphan receipt.

All pending children are still claimed and receive durable intents before any
child is materialised or launched.  The retry happens only after every child
``Popen`` has been issued, so one quick completion cannot suppress a sibling.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
import time
from collections.abc import Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_postbootstrap_live_start_recovery_v1 as live_recovery
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-postbootstrap-batch-dispatch-v2"
RESULT_KIND = "paper400-dic5-recursive-postbootstrap-batch-dispatch-result-v2"


class BatchDispatchV2Error(RuntimeError):
    """The v2 visibility-safe start phase cannot be proved recoverable."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "batch_dispatch_v2_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "v1_plan_and_commit": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "live_visibility_recovery": live_recovery._source_binding(),
    }


def _retry_visible_live_session(child_root: Path, *, cpu: int) -> dict[str, Any] | None:
    """Seal a live session or prove the original fast signal is quiescent.

    ``None`` means only that the frozen recovery helper established the exact
    stopped-proof context required for the normal fast-terminal path.  It is
    never an UNSAT claim by itself.
    """

    try:
        return live_recovery._recover_live_or_exact_fast(child_root, cpu=cpu)
    except live_recovery.LiveStartRecoveryError as exc:
        raise BatchDispatchV2Error("frozen child visibility retry failed") from exc


def _start_all_v2(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Run v1's durable startup phases with a live-visibility retry."""

    bundle = Path(loaded["root"])
    starts = batch._safe_sidecar_dir(bundle, batch.STARTS_DIR)
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    entries: list[dict[str, Any]] = []
    for step in plan["steps"]:
        worker = step["worker"]
        item = batch._queue_item(queue, step["item_id"])
        if item.get("state") != "CLAIMED":
            raise BatchDispatchV2Error("batch item left CLAIMED state before start")
        intent = batch._start_intent_value(plan, step)
        key = f"{step['ordinal']:04d}-{worker['token'][:16]}"
        intent_path = starts / f"{key}.intent.json"
        started_path = starts / f"{key}.started.json"
        if intent_path.exists() or intent_path.is_symlink():
            if supervisor._read_json(intent_path) != intent:
                raise BatchDispatchV2Error("child start intent changed")
        else:
            supervisor._publish_json(intent_path, intent)
        entries.append(
            {
                "step": step,
                "worker": worker,
                "item": item,
                "intent": intent,
                "started_path": started_path,
                "child_root": Path(worker["child_root"]),
                "claim": batch._claim_at_step(step),
            }
        )

    results: list[dict[str, Any]] = []
    failures: list[str] = []
    launches: list[dict[str, Any]] = []
    # No solver is launched until every child has an immutable intent.
    for entry in entries:
        worker, item, child_root = entry["worker"], entry["item"], entry["child_root"]
        if batch._existing_fast_orphan(loaded, item_id=item["item_id"], worker=worker):
            results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
            continue
        started_path = entry["started_path"]
        if started_path.exists() or started_path.is_symlink():
            session = batch._sealed_session_after_external_start(child_root)
            expected = batch._start_receipt_value(entry["intent"], session)
            batch._publish_started_receipt(started_path, expected)
            results.append({
                "item_id": item["item_id"], "state": "RUNNING",
                "started_sha256": expected["record_sha256"],
            })
            continue
        try:
            if child_root.is_symlink():
                raise BatchDispatchV2Error("child root is a symlink")
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
            batch._write_orphan(
                loaded, worker=worker, claim=entry["claim"], child_root=child_root, error=error,
            )
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        launches.append(entry)

    processes: list[tuple[dict[str, Any], Any]] = []
    # Every child process is created before any result, retry, or proof-state
    # observation is made for an earlier sibling.
    for entry in launches:
        try:
            process = batch._spawn_child_start(entry["child_root"], cpu=entry["item"]["cpu_ids"][0])
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            batch._write_orphan(
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
                raise BatchDispatchV2Error("child start process has no exit status")
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            batch._write_orphan(
                loaded, worker=entry["worker"], claim=entry["claim"],
                child_root=entry["child_root"], error=error,
            )
            results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
            failures.append(item["item_id"])
            continue
        if returncode == 0:
            try:
                session = batch._sealed_session_after_external_start(entry["child_root"])
                started = batch._start_receipt_value(entry["intent"], session)
                batch._publish_started_receipt(entry["started_path"], started)
            except BaseException as exc:
                error = f"{type(exc).__name__}: {exc}"
                results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
                failures.append(item["item_id"])
                continue
            results.append({
                "item_id": item["item_id"], "state": "RUNNING",
                "started_sha256": started["record_sha256"],
            })
            continue

        error = batch._external_start_error(returncode, stderr or b"")
        if error == recovery.FAST_START_ERROR:
            try:
                session = _retry_visible_live_session(
                    entry["child_root"], cpu=entry["item"]["cpu_ids"][0],
                )
            except BaseException as exc:
                recovery_error = f"{type(exc).__name__}: {exc}"
                results.append({
                    "item_id": item["item_id"], "state": "START_ERROR", "error": recovery_error,
                })
                failures.append(item["item_id"])
                continue
            if session is not None:
                started = batch._start_receipt_value(entry["intent"], session)
                batch._publish_started_receipt(entry["started_path"], started)
                results.append({
                    "item_id": item["item_id"],
                    "state": "LIVE_SESSION_SEALED_AFTER_VISIBILITY_RETRY",
                    "started_sha256": started["record_sha256"],
                })
                continue
            # Exact stopped context was checked above.  Preserve the frozen
            # runner's original signal for normal DRAT/LRAT/fresh recovery.
            batch._write_orphan(
                loaded, worker=entry["worker"], claim=entry["claim"],
                child_root=entry["child_root"], error=error,
            )
            results.append({"item_id": item["item_id"], "state": "FAST_TERMINAL_ORPHAN"})
            continue

        batch._write_orphan(
            loaded, worker=entry["worker"], claim=entry["claim"],
            child_root=entry["child_root"], error=error,
        )
        results.append({"item_id": item["item_id"], "state": "START_ERROR", "error": error})
        failures.append(item["item_id"])
    if failures:
        raise BatchDispatchV2Error(
            "one or more child starts need audit after all siblings were attempted: " + ",".join(failures)
        )
    return results


def _result_value(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], checkpoint_receipt: Mapping[str, Any],
    checkpoint_chain: Mapping[str, Any], children: list[dict[str, Any]],
) -> dict[str, Any]:
    checkpoint_sha = checkpoint_chain.get("latest_checkpoint_sha256")
    if not recursive.is_sha256(checkpoint_sha):
        raise BatchDispatchV2Error("checkpoint replay did not expose its manifest")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "parent_checkpoint_sha256": checkpoint_receipt["record_sha256"],
            "checkpoint_manifest_sha256": checkpoint_sha,
            "children": children,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def dispatch_pending_batch(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT, worker_prefix: str | None = None,
) -> dict[str, Any]:
    """Commit a v1-compatible batch plan and execute its visibility-safe v2 start."""

    target = Path(bundle)
    with batch._batch_lock(target):
        try:
            loaded = batch._require_postbootstrap_bundle(target, control_root=control_root)
        except (recovery.RecursiveCheckpointRecoveryError, supervisor.RecursiveSplitSupervisorError):
            batch._recover_interrupted_final_queue(target)
            loaded = batch._require_postbootstrap_bundle(target, control_root=control_root)
        checkpoint_receipt = recovery._require_checkpoint_receipt(loaded)
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            _observation, checkpoint_chain = recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            sidecar = batch._safe_sidecar_dir(target, batch.SIDECAR_DIR)
            plan_path = sidecar / batch.PLAN.name
            if plan_path.exists() or plan_path.is_symlink():
                plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
            else:
                prefix = worker_prefix or f"recursive-batch-v2-{os.uname().nodename}-{os.getpid()}"
                plan = batch._plan_value(loaded, worker_prefix=prefix, now=time.time())
                supervisor._publish_json(plan_path, plan)
            replay = batch._ensure_claims_committed(
                target, control_root=control_root, plan=plan, loaded=loaded,
            )
            children = _start_all_v2(replay, plan)
            result = _result_value(
                replay,
                plan=plan,
                checkpoint_receipt=checkpoint_receipt,
                checkpoint_chain=checkpoint_chain,
                children=children,
            )
            return result


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
        BatchDispatchV2Error,
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
