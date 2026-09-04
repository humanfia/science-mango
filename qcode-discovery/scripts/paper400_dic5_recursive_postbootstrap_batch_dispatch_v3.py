#!/usr/bin/env python3
"""Claim and concurrently start post-bootstrap siblings with schema bridging.

The v2 batch dispatcher correctly makes every child claim and ``Popen``
durable before observing a sibling result.  Its visibility retry delegates to
the frozen recursive runner, however, and that runner cannot seal a start
whose frozen controller binds configuration through ``start.claim``.  This
sidecar retains v2's all-sibling launch order and v1 queue-plan ledger while
using the narrowly attested compatibility sealer for that one live schema.

It never interprets a fast start signal as UNSAT: a stopped child is still
left as the normal exact fast-terminal orphan, and a live child is accepted
only after PID, start-tick, affinity, limits, controller claim, and config
bindings have all been rechecked by the compatibility sealer.
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
from scripts import paper400_dic5_recursive_live_session_compat_v1 as compat
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v2 as v2
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 3
GATE = "paper400-dic5-recursive-postbootstrap-batch-dispatch-v3"
RESULT_KIND = "paper400-dic5-recursive-postbootstrap-batch-dispatch-result-v3"


class BatchDispatchV3Error(RuntimeError):
    """The schema-compatible batch start cannot be proven recoverable."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "batch_dispatch_v3_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "v2_concurrent_launch_logic": v2._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
        "live_session_compat": compat._source_binding(),
    }


def _exact_stopped_fast_context(child_root: Path) -> bool:
    """Accept a fast fallback only after the ordinary stopped-proof checks."""

    try:
        loaded = supervisor.child_runner._load_static(child_root)
        recovery._fast_start_context(child_root, loaded)
    except (
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.child_runner.RecursiveChildRunnerError,
    ):
        return False
    return True


def _retry_visible_live_session(child_root: Path, *, cpu: int) -> dict[str, Any] | None:
    """Seal a live schema-bridged session, or prove exact stopped fast state."""

    try:
        return compat.seal_live_session(child_root, cpu=cpu)["session"]
    except compat.LiveSessionCompatError as exc:
        if _exact_stopped_fast_context(child_root):
            return None
        raise BatchDispatchV3Error("child start was neither exact live nor exact stopped fast") from exc


def _start_all_v3(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Reuse the reviewed v2 launch order with only its retry seam replaced.

    The v2 function has no process-global effects except resolving this module
    global.  The replacement is scoped to this process and restored even on an
    error; every external child start remains a distinct subprocess.  Keeping
    the audited v2 launch implementation avoids a second, subtly divergent
    all-``Popen`` loop while the v3 result receipt accurately binds both
    sources.
    """

    previous = v2._retry_visible_live_session
    v2._retry_visible_live_session = _retry_visible_live_session
    try:
        return v2._start_all_v2(loaded, plan)
    finally:
        v2._retry_visible_live_session = previous


def _result_value(
    loaded: Mapping[str, Any], *, plan: Mapping[str, Any], checkpoint_receipt: Mapping[str, Any],
    checkpoint_chain: Mapping[str, Any], children: list[dict[str, Any]],
) -> dict[str, Any]:
    checkpoint_sha = checkpoint_chain.get("latest_checkpoint_sha256")
    if not recursive.is_sha256(checkpoint_sha):
        raise BatchDispatchV3Error("checkpoint replay did not expose its manifest")
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
    """Commit a v1-compatible queue plan and concurrently start all siblings."""

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
                prefix = worker_prefix or f"recursive-batch-v3-{os.uname().nodename}-{os.getpid()}"
                plan = batch._plan_value(loaded, worker_prefix=prefix, now=time.time())
                supervisor._publish_json(plan_path, plan)
            replay = batch._ensure_claims_committed(
                target, control_root=control_root, plan=plan, loaded=loaded,
            )
            children = _start_all_v3(replay, plan)
            return _result_value(
                replay, plan=plan, checkpoint_receipt=checkpoint_receipt,
                checkpoint_chain=checkpoint_chain, children=children,
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
        raise BatchDispatchV3Error("unsupported action")
    result = dispatch_pending_batch(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        BatchDispatchV3Error,
        v2.BatchDispatchV2Error,
        batch.BatchDispatchError,
        compat.LiveSessionCompatError,
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
