#!/usr/bin/env python3
"""Independently seal every live sibling after a v1 batch-start observation race.

This successor is intentionally a sidecar: existing v1 plans, queue claims,
workers, start intents, and orphan receipts remain immutable.  It fixes two
operational shortcomings of the first recovery helper:

* a controller whose ``start.commit`` uses ``config_manifest_sha256`` can be
  attested through the dedicated compatibility sealer without altering the
  frozen child runner; and
* one stopped or ambiguous sibling cannot prevent later live siblings from
  receiving their ordinary session receipts.

It never starts a new solver, changes a queue item, releases a lease, treats
stdout as a proof, or deletes any data.  An exact inactive fast-start context
is merely reported for the normal certification path.
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
from scripts import paper400_dic5_recursive_live_session_compat_v1 as compat
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-postbootstrap-live-start-recovery-v2"
SIDECAR_DIR = Path("postbootstrap-batch-live-start-recovery-v2")
RECEIPT_KIND = "paper400-dic5-recursive-postbootstrap-live-start-recovery-receipt-v2"
RESULT_KIND = "paper400-dic5-recursive-postbootstrap-live-start-recovery-result-v2"
RECOVERY_REASON = "STRICT_CONFIG_MANIFEST_SCHEMA_COMPATIBILITY_ATTESTATION"


class LiveStartRecoveryV2Error(RuntimeError):
    """A recorded orphan cannot be reconciled safely."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "live_start_recovery_v2_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "batch_dispatch": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "live_session_compat": compat._source_binding(),
    }


@contextlib.contextmanager
def _recovery_lock(bundle: Path) -> Iterator[None]:
    """Serialize with any v1 plan/claim publication for this bundle."""

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


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        existing = supervisor._read_json(path)
        if existing != value:
            raise LiveStartRecoveryV2Error(f"{label} changed after publication")
        return
    supervisor._publish_json(path, value)


def _receipt_value(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], step: Mapping[str, Any],
    intent: Mapping[str, Any], orphan: Mapping[str, Any], session: Mapping[str, Any],
    checkpoint_receipt: Mapping[str, Any], checkpoint_chain: Mapping[str, Any],
) -> dict[str, Any]:
    worker = step["worker"]
    session_sha = session.get("record_sha256")
    checkpoint_sha = checkpoint_chain.get("latest_checkpoint_sha256")
    if not recursive.is_sha256(session_sha):
        raise LiveStartRecoveryV2Error("compatibility-sealed child session is malformed")
    if not recursive.is_sha256(orphan.get("worker_sha256")):
        raise LiveStartRecoveryV2Error("recorded batch orphan is malformed")
    if not recursive.is_sha256(checkpoint_sha):
        raise LiveStartRecoveryV2Error("checkpoint replay did not expose its manifest")
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


def _exact_stopped_fast_context(child_root: Path) -> bool:
    """Return true only after the normal fast-terminal preconditions replay."""

    try:
        loaded = supervisor.child_runner._load_static(child_root)
        recovery._fast_start_context(child_root, loaded)
    except (
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.child_runner.RecursiveChildRunnerError,
    ):
        return False
    return True


def _recover_step(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], step: Mapping[str, Any],
    checkpoint_receipt: Mapping[str, Any], checkpoint_chain: Mapping[str, Any],
) -> dict[str, Any]:
    """Reconcile exactly one existing orphan without affecting its siblings."""

    bundle = Path(loaded["root"])
    worker = step["worker"]
    item_id = step["item_id"]
    intent_path, started_path = _step_paths(bundle, step)
    expected_intent = batch._start_intent_value(plan, step)
    if not intent_path.exists() or intent_path.is_symlink():
        raise LiveStartRecoveryV2Error("batch start intent is absent")
    if supervisor._read_json(intent_path) != expected_intent:
        raise LiveStartRecoveryV2Error("batch start intent no longer binds this worker")
    try:
        item, _worker_path, recovered_worker, orphan, _queue = recovery._worker_context(
            loaded, item_id=item_id, require_live_claim=True,
        )
    except recovery.RecursiveCheckpointRecoveryError as exc:
        raise LiveStartRecoveryV2Error("batch orphan no longer matches the live queue") from exc
    if recovered_worker != worker or item.get("path") != step.get("path"):
        raise LiveStartRecoveryV2Error("batch plan/worker/item binding changed")
    child_root = Path(worker["child_root"])
    if started_path.exists() or started_path.is_symlink():
        session = batch._sealed_session_after_external_start(child_root)
        started = batch._start_receipt_value(expected_intent, session)
        _publish_exact(started_path, started, label="batch started receipt")
        state = "ALREADY_SEALED"
    else:
        try:
            compat_result = compat.seal_live_session(child_root, cpu=worker["cpu_ids"][0])
        except compat.LiveSessionCompatError as exc:
            if _exact_stopped_fast_context(child_root):
                return {
                    "item_id": item_id,
                    "state": "FAST_TERMINAL_STILL_UNRESOLVED",
                    "hardness_only": True,
                    "solver_terminal_claim": False,
                }
            return {
                "item_id": item_id,
                "state": "RECOVERY_DEFERRED",
                "error": f"{type(exc).__name__}: {exc}",
                "hardness_only": True,
                "solver_terminal_claim": False,
            }
        session = compat_result["session"]
        started = batch._start_receipt_value(expected_intent, session)
        _publish_exact(started_path, started, label="batch started receipt")
        state = compat_result["state"]
    receipt = _receipt_value(
        loaded, plan=plan, step=step, intent=expected_intent, orphan=orphan,
        session=session, checkpoint_receipt=checkpoint_receipt, checkpoint_chain=checkpoint_chain,
    )
    _publish_exact(_receipt_path(bundle, step), receipt, label="compatibility recovery receipt")
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
    """Process each recorded sibling, preserving progress after a deferred one."""

    target = Path(bundle)
    with _recovery_lock(target):
        loaded = recovery._load_recovery_bundle(target, control_root=control_root)
        if loaded.get("queue_progress_bootstrap_required") is True:
            raise LiveStartRecoveryV2Error("recovery requires an authenticated v1 queue bootstrap")
        checkpoint_receipt = recovery._require_checkpoint_receipt(loaded)
        plan_path = target / batch.PLAN
        if not plan_path.exists() or plan_path.is_symlink():
            raise LiveStartRecoveryV2Error("batch plan is absent")
        plan = batch._validate_plan(loaded, supervisor._read_json(plan_path))
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            _observation, checkpoint_chain = recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            recovery._require_dispatchable_queue_state(loaded)
            children: list[dict[str, Any]] = []
            for step in plan["steps"]:
                try:
                    children.append(
                        _recover_step(
                            loaded, plan=plan, step=step,
                            checkpoint_receipt=checkpoint_receipt,
                            checkpoint_chain=checkpoint_chain,
                        )
                    )
                except LiveStartRecoveryV2Error as exc:
                    children.append(
                        {
                            "item_id": step["item_id"],
                            "state": "RECOVERY_DEFERRED",
                            "error": f"{type(exc).__name__}: {exc}",
                            "hardness_only": True,
                            "solver_terminal_claim": False,
                        }
                    )
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
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
    if args.action != "recover-live":  # pragma: no cover - argparse guards this
        raise LiveStartRecoveryV2Error("unsupported action")
    result = recover_live_starts(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        LiveStartRecoveryV2Error,
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
