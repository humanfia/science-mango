#!/usr/bin/env python3
"""Versioned lifecycle adapter for v2 incomplete-child retry roots.

The queue transaction and proof-validation logic in the v1 retry lifecycle is
already independently exercised.  This adapter reuses it only through a
process-local namespace: its retry handoff reader is switched to the v2
attempt handoff, and every resulting transition, validation, and aggregate is
sealed under a distinct v2 gate.  No v1 on-disk record is changed.
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
from scripts import paper400_dic5_recursive_incomplete_child_restart_lifecycle_v1 as implementation
from scripts import paper400_dic5_recursive_incomplete_child_restart_v2 as restart
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-incomplete-child-restart-lifecycle-v2"
LOCK = Path(".incomplete-child-restart-lifecycle-v2.lock")
TRANSITIONS = restart.SIDECAR_DIR / "queue-transitions-retry-v2"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
TRANSITION_KIND = "paper400-dic5-recursive-incomplete-child-retry-queue-transition-v2"
PREPARE_KIND = "paper400-dic5-recursive-incomplete-child-retry-queue-transition-prepare-v2"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-incomplete-child-retry-parent-aggregate-v2"
RESULT_KIND = "paper400-dic5-recursive-incomplete-child-retry-lifecycle-tick-v2"
VALIDATION_KIND = "paper400-dic5-recursive-incomplete-child-retry-fresh-validation-v2"


class IncompleteChildRestartLifecycleV2Error(RuntimeError):
    """The v2 lifecycle adaptation cannot replay safely."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    implementation_source = Path(implementation.__file__).resolve(strict=True)
    implementation_payload = supervisor._stable_bytes(implementation_source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "incomplete_child_restart_lifecycle_v2": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "v1_lifecycle_engine": {
            "path": str(implementation_source),
            "sha256": hashlib.sha256(implementation_payload).hexdigest(),
        },
        "restart_handoff_v2": restart._source_binding(),
    }


@contextlib.contextmanager
def _v2_runtime() -> Iterator[None]:
    """Install v2 sources and namespaces only for this one tick process."""

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
        "VALIDATION_KIND": VALIDATION_KIND,
        "_source_binding": _source_binding,
        "restart": restart,
    }
    saved = {name: getattr(implementation, name) for name in replacements}
    try:
        for name, value in replacements.items():
            setattr(implementation, name, value)
        yield
    finally:
        for name, value in saved.items():
            setattr(implementation, name, value)


def tick_bundle(bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT) -> dict[str, Any]:
    with _v2_runtime():
        return implementation.tick_bundle(bundle, control_root=control_root)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    tick = sub.add_parser("tick", allow_abbrev=False)
    tick.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = tick_bundle(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        IncompleteChildRestartLifecycleV2Error,
        implementation.IncompleteChildRestartLifecycleError,
        restart.IncompleteChildRestartV2Error,
        recursive.RecursiveSplitError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
