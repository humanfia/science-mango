#!/usr/bin/env python3
"""Lifecycle v3 for a fully attested initial-batch affinity recovery.

The ordinary initial-batch lifecycle correctly refuses arbitrary orphan
receipts.  A retained affinity-inheritance orphan is not a fast-terminal
proof, though, and a completed v1 affinity-recovery sidecar proves that every
sibling subsequently obtained a normal sealed start session.  This versioned
lifecycle leaves the orphan untouched and bypasses it only after replaying
that all-sibling completion record.  It otherwise retains lifecycle v2's
fresh terminal validation and its isolated queue-transaction namespace.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import sys
from collections.abc import Iterator
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_initial_batch_affinity_recovery_v1 as affinity
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v2 as v2
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 3
GATE = "paper400-dic5-recursive-initial-batch-lifecycle-v3"
LOCK = Path(".initial-batch-lifecycle-v3.lock")
TRANSITIONS = initial.SIDECAR_DIR / "queue-transitions-v3"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
TRANSITION_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-v3"
PREPARE_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-prepare-v3"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-initial-batch-parent-aggregate-v3"
RESULT_KIND = "paper400-dic5-recursive-initial-batch-lifecycle-tick-v3"


class InitialBatchLifecycleV3Error(RuntimeError):
    """A v3 affinity-recovery lifecycle prerequisite was malformed."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "initial_batch_lifecycle_v3": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "initial_batch_lifecycle_v2": v2._source_binding(),
        "affinity_recovery": affinity._source_binding(),
    }


@contextlib.contextmanager
def _v3_runtime() -> Iterator[None]:
    """Run the proven v1 state machine with v3 records and one narrow gate."""

    replacements: dict[str, Any] = {
        "GATE": GATE,
        "LOCK": LOCK,
        "TRANSITIONS": TRANSITIONS,
        "PREPARES": PREPARES,
        "RECORDS": RECORDS,
        "TRANSITION_KIND": TRANSITION_KIND,
        "PREPARE_KIND": PREPARE_KIND,
        "PARENT_AGGREGATE_KIND": PARENT_AGGREGATE_KIND,
        "RESULT_KIND": RESULT_KIND,
        "_source_binding": _source_binding,
    }
    saved = {name: getattr(base, name) for name in replacements}
    old_verify_final = supervisor.child_runner.verify_final_root
    old_fast_orphan = base._is_fast_orphan

    def _is_fast_or_completed_affinity_recovery(loaded: dict[str, Any], *, item_id: str) -> bool:
        try:
            if affinity.completed_recovery_for_item(loaded, item_id=item_id):
                return False
        except affinity.InitialBatchAffinityRecoveryError as exc:
            raise InitialBatchLifecycleV3Error(
                "affinity recovery sidecar is not a complete replayable start recovery"
            ) from exc
        return old_fast_orphan(loaded, item_id=item_id)

    try:
        for name, value in replacements.items():
            setattr(base, name, value)
        supervisor.child_runner.verify_final_root = v2.verify_normal_final_root_v2
        base._is_fast_orphan = _is_fast_or_completed_affinity_recovery
        yield
    finally:
        base._is_fast_orphan = old_fast_orphan
        supervisor.child_runner.verify_final_root = old_verify_final
        for name, value in saved.items():
            setattr(base, name, value)


def tick_bundle(bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT) -> dict[str, Any]:
    """Advance one safe v3 lifecycle transaction."""

    with _v3_runtime():
        return base.tick_bundle(bundle, control_root=control_root)


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
        raise InitialBatchLifecycleV3Error("unsupported lifecycle action")
    result = tick_bundle(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        InitialBatchLifecycleV3Error,
        base.InitialBatchLifecycleError,
        affinity.InitialBatchAffinityRecoveryError,
        initial.InitialBatchDispatchError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
