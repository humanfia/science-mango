#!/usr/bin/env python3
"""Versioned lifecycle repair for simultaneous initial recursive launches.

The frozen child runner's ``verify_final_root`` builds a new validation record
with the old ``validation_sha256`` field already present.  The recursive
sealer correctly rejects that second sealing attempt.  Existing child session
records bind the frozen runner by hash, so this sidecar never edits it.

Instead, this v2 sidecar performs the same read-only terminal validation
steps, seals a distinct v2 validation record, and runs the already-audited v1
initial-batch lifecycle under a versioned transaction namespace.  It never
starts or resumes a solver, releases an uncertified lease, or deletes data.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import sys
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-initial-batch-lifecycle-v2"
LOCK = Path(".initial-batch-lifecycle-v2.lock")
TRANSITIONS = initial.SIDECAR_DIR / "queue-transitions-v2"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
TRANSITION_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-v2"
PREPARE_KIND = "paper400-dic5-recursive-initial-batch-queue-transition-prepare-v2"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-initial-batch-parent-aggregate-v2"
RESULT_KIND = "paper400-dic5-recursive-initial-batch-lifecycle-tick-v2"
VALIDATION_KIND = "paper400-dic5-recursive-child-fresh-final-validation-v2"


class InitialBatchLifecycleV2Error(RuntimeError):
    """A v2 normal-terminal replay prerequisite was malformed or changed."""


_BASE_SOURCE_BINDING = base._source_binding


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    child_source = PROJECT / "scripts" / "run_paper400_dic5_recursive_child_resume_proof_v1.py"
    child_payload = supervisor._stable_bytes(child_source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "initial_batch_lifecycle_v2": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "frozen_child_runner": {
            "path": str(child_source),
            "sha256": hashlib.sha256(child_payload).hexdigest(),
        },
        "initial_batch_lifecycle_v1_base": _BASE_SOURCE_BINDING(),
    }


def verify_normal_final_root_v2(root: Path) -> dict[str, Any]:
    """Freshly replay an ordinary terminal child without the v1 reseal bug.

    This intentionally mirrors ``child_runner.verify_final_root``.  The
    persisted certificate and v1 validation are independently replayed before
    and after the new DRAT/LRAT replays.  The only semantic difference is that
    the old validation digest is stored under a non-conflicting field name.
    """

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    with runner._root_lock(target, exclusive=False):
        loaded = runner._load_static(target)
        session = runner._load_session(target, loaded)
        claim, certificate, stored_validation = runner._validated_certificate(
            target, loaded, session,
        )
        replay = runner._revalidate_terminal_claim(
            target,
            loaded,
            session,
            claim,
            require_stopped_snapshot=True,
            fresh_replay=True,
        )
        fresh_drat = replay.get("fresh_drat")
        fresh_lrat = replay.get("fresh_lrat")
        if (
            not isinstance(fresh_drat, dict)
            or not isinstance(fresh_lrat, dict)
            or fresh_drat.get("verified") is not True
            or fresh_lrat.get("verified") is not True
        ):
            raise InitialBatchLifecycleV2Error("normal child fresh DRAT/LRAT replay is incomplete")

        # Re-read the immutable records after both checkers finish.  This is
        # stronger than merely trusting the earlier in-memory view.
        final_loaded = runner._load_static(target)
        final_session = runner._load_session(target, final_loaded)
        final_claim, final_certificate, final_stored_validation = runner._validated_certificate(
            target, final_loaded, final_session,
        )
        if (
            final_loaded["static"].get("static_sha256")
            != loaded["static"].get("static_sha256")
            or final_session.get("record_sha256") != session.get("record_sha256")
            or final_claim != claim
            or final_certificate != certificate
            or final_stored_validation != stored_validation
        ):
            raise InitialBatchLifecycleV2Error("normal child evidence changed during fresh replay")

        return supervisor.seal(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": VALIDATION_KIND,
                "gate": GATE,
                "root": str(target),
                "static_sha256": final_loaded["static"]["static_sha256"],
                "session_sha256": final_session["record_sha256"],
                "terminal_claim_sha256": final_claim["terminal_claim_sha256"],
                "certificate_sha256": final_certificate["certificate_sha256"],
                # Do not reuse ``validation_sha256`` here: that is the
                # self-hash field of this new v2 record.
                "stored_validation_sha256": final_stored_validation["validation_sha256"],
                "fresh_drat": dict(fresh_drat),
                "fresh_lrat": dict(fresh_lrat),
                "valid": True,
                "strict_proof_unsat": True,
                "fresh_proof_replay": True,
                "source_toolchain_fresh": True,
                "failures": [],
                "global_distance_claim": None,
                "publication_certificate": False,
                "upload_authorized": False,
                "source_binding": _source_binding(),
            },
            "validation_sha256",
        )


@contextlib.contextmanager
def _v2_runtime() -> Iterator[None]:
    """Run the v1 state machine with v2 records and normal validation.

    This process-local adaptation keeps the extensively tested v1 transaction
    code intact while ensuring every record identifies the v2 implementation.
    It is restored even if a checker or queue operation raises.
    """

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
    try:
        for name, value in replacements.items():
            setattr(base, name, value)
        supervisor.child_runner.verify_final_root = verify_normal_final_root_v2
        yield
    finally:
        supervisor.child_runner.verify_final_root = old_verify_final
        for name, value in saved.items():
            setattr(base, name, value)


def tick_bundle(bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT) -> dict[str, Any]:
    """Advance one v2 lifecycle tick with no changes to frozen sources."""

    with _v2_runtime():
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
        raise InitialBatchLifecycleV2Error("unsupported lifecycle action")
    result = tick_bundle(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        InitialBatchLifecycleV2Error,
        base.InitialBatchLifecycleError,
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
