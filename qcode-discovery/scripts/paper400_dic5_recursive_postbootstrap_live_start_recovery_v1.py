#!/usr/bin/env python3
"""Seal live recursive children misobserved during a batch start race.

The post-bootstrap batch dispatcher deliberately treats the frozen child's
``unsealed child start commit is not live and bound`` exception as an
unresolved fast-terminal signal.  That exception can also occur in the narrow
interval between controller launch and PID visibility.  This companion never
interprets the signal as UNSAT.  It revisits only an exact, already-recorded
batch orphan under the parent checkpoint lock and asks the frozen child runner
to recover its own start session.  A live session is sealed and recorded; a
still-inactive child is left untouched for the normal fast-terminal proof
recovery path.

No queue claim, CPU lease, parent transport, proof, or checkpoint data is
modified.  In particular, the original orphan receipt is retained as
forensic evidence and is never treated as a terminal proof.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import os
import sys
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-postbootstrap-live-start-recovery-v1"
SIDECAR_DIR = Path("postbootstrap-batch-live-start-recovery-v1")
RECEIPT_KIND = "paper400-dic5-recursive-postbootstrap-live-start-recovery-receipt-v1"
RECOVERY_REASON = "FAST_START_SIGNAL_RECHECKED_AFTER_CONTROLLER_PID_VISIBILITY"


class LiveStartRecoveryError(RuntimeError):
    """An alleged batch fast-start race is not exactly recoverable."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "live_start_recovery_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "batch_dispatch": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
    }


@contextlib.contextmanager
def _recovery_lock(bundle: Path) -> Iterator[None]:
    with batch._batch_lock(bundle):
        yield


def _safe_sidecar_dir(bundle: Path) -> Path:
    return batch._safe_sidecar_dir(bundle, SIDECAR_DIR)


def _step_paths(bundle: Path, step: Mapping[str, Any]) -> tuple[Path, Path]:
    worker = step["worker"]
    starts = bundle / batch.STARTS_DIR
    key = f"{step['ordinal']:04d}-{worker['token'][:16]}"
    return starts / f"{key}.intent.json", starts / f"{key}.started.json"


def _receipt_path(bundle: Path, step: Mapping[str, Any]) -> Path:
    worker = step["worker"]
    return _safe_sidecar_dir(bundle) / f"{step['ordinal']:04d}-{worker['token'][:16]}.json"


def _receipt_value(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], step: Mapping[str, Any],
    intent: Mapping[str, Any], orphan: Mapping[str, Any], session: Mapping[str, Any],
    checkpoint_receipt: Mapping[str, Any], checkpoint_chain: Mapping[str, Any],
) -> dict[str, Any]:
    worker = step["worker"]
    session_sha = session.get("record_sha256")
    if not recursive.is_sha256(session_sha):
        raise LiveStartRecoveryError("recovered child session is not sealed")
    if not recursive.is_sha256(orphan.get("worker_sha256")):
        raise LiveStartRecoveryError("recorded fast orphan is not sealed")
    checkpoint_sha = checkpoint_chain.get("latest_checkpoint_sha256")
    if not recursive.is_sha256(checkpoint_sha):
        raise LiveStartRecoveryError("checkpoint replay did not expose its manifest")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RECEIPT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "parent_checkpoint_sha256": checkpoint_receipt["record_sha256"],
            "checkpoint_manifest_sha256": checkpoint_sha,
            "item_id": step["item_id"],
            "worker_sha256": worker["worker_sha256"],
            "orphan_worker_sha256": orphan["worker_sha256"],
            "start_intent_sha256": intent["record_sha256"],
            "child_root": worker["child_root"],
            "expected_single_cpu": worker["cpu_ids"][0],
            "session_sha256": session_sha,
            "recovery_reason": RECOVERY_REASON,
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
            raise LiveStartRecoveryError(f"{label} changed after publication")
        return
    supervisor._publish_json(path, value)


def _recover_step(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], step: Mapping[str, Any],
    checkpoint_receipt: Mapping[str, Any], checkpoint_chain: Mapping[str, Any],
) -> dict[str, Any]:
    """Attempt only frozen-runner session sealing for one recorded batch orphan."""

    bundle = Path(loaded["root"])
    worker = step["worker"]
    item_id = step["item_id"]
    intent_path, started_path = _step_paths(bundle, step)
    expected_intent = batch._start_intent_value(plan, step)
    if not intent_path.exists() or intent_path.is_symlink():
        raise LiveStartRecoveryError("batch start intent is absent")
    intent = supervisor._read_json(intent_path)
    if intent != expected_intent:
        raise LiveStartRecoveryError("batch start intent is no longer bound")

    try:
        item, _worker_path, recovered_worker, orphan, _queue = recovery._worker_context(
            loaded, item_id=item_id, require_live_claim=True,
        )
    except recovery.RecursiveCheckpointRecoveryError as exc:
        raise LiveStartRecoveryError("batch fast orphan is not exact") from exc
    if recovered_worker != worker or item.get("path") != step.get("path"):
        raise LiveStartRecoveryError("batch step no longer binds the recorded orphan")

    child_root = Path(worker["child_root"])
    if started_path.exists() or started_path.is_symlink():
        session = batch._sealed_session_after_external_start(child_root)
        started = batch._start_receipt_value(intent, session)
        _publish_exact(started_path, started, label="batch started receipt")
        state = "ALREADY_SEALED"
    else:
        try:
            # The frozen runner is the sole authority that can inspect a
            # START_RECOVERY_REQUIRED root and seal a live session.  It never
            # creates a second controller generation for a live runtime.
            session = supervisor.child_runner.start_root(child_root, cpu=worker["cpu_ids"][0])
        except supervisor.child_runner.RecursiveChildRunnerError as exc:
            if f"{type(exc).__name__}: {exc}" == recovery.FAST_START_ERROR:
                return {
                    "item_id": item_id,
                    "state": "FAST_TERMINAL_STILL_UNRESOLVED",
                    "hardness_only": True,
                    "solver_terminal_claim": False,
                }
            raise LiveStartRecoveryError("frozen child start recovery did not seal a live session") from exc
        started = batch._start_receipt_value(intent, session)
        _publish_exact(started_path, started, label="batch started receipt")
        state = "LIVE_SESSION_SEALED"

    receipt = _receipt_value(
        loaded,
        plan=plan,
        step=step,
        intent=intent,
        orphan=orphan,
        session=session,
        checkpoint_receipt=checkpoint_receipt,
        checkpoint_chain=checkpoint_chain,
    )
    _publish_exact(_receipt_path(bundle, step), receipt, label="live-start recovery receipt")
    return {
        "item_id": item_id,
        "state": state,
        "session_sha256": session["record_sha256"],
        "receipt_sha256": receipt["record_sha256"],
        "hardness_only": True,
        "solver_terminal_claim": False,
    }


def recover_live_starts(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Recover every exact v1 batch fast-start orphan that is actually live."""

    target = Path(bundle)
    with _recovery_lock(target):
        loaded = recovery._load_recovery_bundle(target, control_root=control_root)
        if loaded.get("queue_progress_bootstrap_required") is True:
            raise LiveStartRecoveryError("batch live-start recovery requires a v1 queue bootstrap")
        checkpoint_receipt = recovery._require_checkpoint_receipt(loaded)
        plan_path = target / batch.PLAN
        if not plan_path.exists() or plan_path.is_symlink():
            raise LiveStartRecoveryError("batch plan is absent")
        plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            _observation, checkpoint_chain = recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            recovery._require_dispatchable_queue_state(loaded)
            children = [
                _recover_step(
                    loaded,
                    plan=plan,
                    step=step,
                    checkpoint_receipt=checkpoint_receipt,
                    checkpoint_chain=checkpoint_chain,
                )
                for step in plan["steps"]
            ]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-postbootstrap-live-start-recovery-result-v1",
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "parent_checkpoint_sha256": checkpoint_receipt["record_sha256"],
            "checkpoint_manifest_sha256": checkpoint_chain["latest_checkpoint_sha256"],
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
    recover = sub.add_parser("recover-live", allow_abbrev=False)
    recover.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = recover_live_starts(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        LiveStartRecoveryError,
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
