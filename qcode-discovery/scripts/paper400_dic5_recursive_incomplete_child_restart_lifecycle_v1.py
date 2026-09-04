#!/usr/bin/env python3
"""Certification lifecycle for immutable incomplete-child retry roots.

``paper400_dic5_recursive_incomplete_child_restart_v1`` preserves a stopped,
failed partial proof and starts a distinct retry root for every affected
frontier leaf.  This module is the only sidecar that may convert those retry
proofs into queue certifications.  It preserves the initial lifecycle's
prepared/committed queue transaction protocol, but adds an exact binding from
every certification to the forensic handoff, retry intent, retry session, and
retry root.

The old child roots remain evidence only.  They are never resumed, removed,
or interpreted as a terminal proof.  CPU leases are released only after all
frontier certificates aggregate to an authenticated parent result.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
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
from scripts import paper400_dic5_recursive_incomplete_child_restart_v1 as restart
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


# Base queue records intentionally retain schema version 1, matching the
# audited initial all-claim transition machine.  This new gate/version is what
# identifies the retry-root semantics.
SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-incomplete-child-restart-lifecycle-v1"
LOCK = Path(".incomplete-child-restart-lifecycle-v1.lock")
TRANSITIONS = restart.SIDECAR_DIR / "queue-transitions-retry-v1"
PREPARES = TRANSITIONS / "prepares"
RECORDS = TRANSITIONS / "records"
TRANSITION_KIND = "paper400-dic5-recursive-incomplete-child-retry-queue-transition-v1"
PREPARE_KIND = "paper400-dic5-recursive-incomplete-child-retry-queue-transition-prepare-v1"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-incomplete-child-retry-parent-aggregate-v1"
RESULT_KIND = "paper400-dic5-recursive-incomplete-child-retry-lifecycle-tick-v1"
VALIDATION_KIND = "paper400-dic5-recursive-incomplete-child-retry-fresh-validation-v1"


class IncompleteChildRestartLifecycleError(RuntimeError):
    """A retry-root certificate or queue transition is not replayable."""


_BASE_SOURCE_BINDING = base._source_binding


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    child_source = PROJECT / "scripts" / "run_paper400_dic5_recursive_child_resume_proof_v1.py"
    child_payload = supervisor._stable_bytes(child_source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "incomplete_child_restart_lifecycle": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "restart_handoff": restart._source_binding(),
        "initial_batch_lifecycle_base": _BASE_SOURCE_BINDING(),
        "frozen_child_runner": {
            "path": str(child_source),
            "sha256": hashlib.sha256(child_payload).hexdigest(),
        },
    }


def _entry_for_item(loaded: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    handoff = loaded.get("restart_handoff")
    if not isinstance(handoff, dict) or not isinstance(handoff.get("entries"), list):
        raise IncompleteChildRestartLifecycleError("retry handoff is absent from lifecycle state")
    matches = [entry for entry in handoff["entries"] if entry.get("entry", {}).get("item_id") == item_id]
    if len(matches) != 1:
        raise IncompleteChildRestartLifecycleError("retry handoff has no unique child entry")
    return matches[0]


def _retry_evidence(
    loaded: Mapping[str, Any], item_id: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], Path]:
    """Return the validated restart entry, forensic, intent, receipt, and root."""

    evidence = _entry_for_item(loaded, item_id)
    entry = evidence.get("entry")
    forensic = evidence.get("forensic")
    intent = evidence.get("intent")
    started = evidence.get("started")
    session = evidence.get("session")
    if not all(isinstance(value, dict) for value in (entry, forensic, intent, started, session)):
        raise IncompleteChildRestartLifecycleError("retry handoff evidence is malformed")
    root = Path(entry["retry_child_root"])
    return dict(entry), dict(forensic), dict(intent), dict(started), root


def _verify_retry_final(root: Path) -> dict[str, Any]:
    """Freshly replay a completed retry proof without altering its evidence."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    with runner._root_lock(target, exclusive=False):
        child_loaded = runner._load_static(target)
        session = runner._load_session(target, child_loaded)
        claim, certificate, stored_validation = runner._validated_certificate(target, child_loaded, session)
        replay = runner._revalidate_terminal_claim(
            target,
            child_loaded,
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
            raise IncompleteChildRestartLifecycleError("retry proof has no complete fresh DRAT/LRAT replay")
        final_loaded = runner._load_static(target)
        final_session = runner._load_session(target, final_loaded)
        final_claim, final_certificate, final_stored_validation = runner._validated_certificate(
            target, final_loaded, final_session,
        )
        if (
            final_loaded["static"].get("static_sha256") != child_loaded["static"].get("static_sha256")
            or final_session.get("record_sha256") != session.get("record_sha256")
            or final_claim != claim
            or final_certificate != certificate
            or final_stored_validation != stored_validation
        ):
            raise IncompleteChildRestartLifecycleError("retry terminal evidence changed during fresh replay")
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


def _retry_certificate(
    loaded: Mapping[str, Any], item_id: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], Path]:
    """Bind a retry certificate to its retained queue claim and handoff receipt."""

    entry, forensic, intent, started, root = _retry_evidence(loaded, item_id)
    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    try:
        item, worker, _original_root = base._worker_for_item(
            loaded, queue, item_id, require_live_claim=False,
        )
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartLifecycleError("retry queue worker binding is invalid") from exc
    runner = supervisor.child_runner
    target = runner._safe_root(root)
    with runner._root_lock(target, exclusive=False):
        child_loaded = restart._validate_retry_static(loaded, entry)
        session = runner._load_session(target, child_loaded)
        certificate = supervisor._read_json(target / runner.CERTIFICATE)
    if (
        entry.get("forensic_sha256") != forensic.get("forensic_sha256")
        or intent.get("forensic_sha256") != forensic.get("forensic_sha256")
        or started.get("retry_session_sha256") != session.get("record_sha256")
        or session.get("record_sha256") != entry.get("retry_session_sha256", session.get("record_sha256"))
        or session.get("expected_single_cpu") != worker.get("cpu_ids", [None])[0]
        or certificate.get("leaf_id") != item.get("leaf_id")
        or certificate.get("leaf_sha256") != item.get("leaf_sha256")
        or certificate.get("child_cnf_sha256") != item.get("child_cnf_sha256")
        or certificate.get("child_dimacs_sha256") != item.get("child_dimacs_sha256")
        or certificate.get("child_num_variables") != item.get("child_num_variables")
        or certificate.get("child_num_clauses") != item.get("child_num_clauses")
        or certificate.get("child_dimacs_bytes") != item.get("child_dimacs_bytes")
    ):
        raise IncompleteChildRestartLifecycleError("retry certificate lost its exact original-leaf binding")
    validation = _verify_retry_final(target)
    return entry, forensic, started, certificate, validation


def _begin_restart_certification(
    loaded: Mapping[str, Any], state: Mapping[str, Any], *, item_id: str,
    certificate: Mapping[str, Any], validation: Mapping[str, Any],
) -> dict[str, Any]:
    if state.get("pending") is not None:
        raise IncompleteChildRestartLifecycleError("cannot prepare a second retry queue mutation")
    before = state["committed_queue"]
    try:
        item, worker, _original_root = base._worker_for_item(
            loaded, before, item_id, require_live_claim=True,
        )
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartLifecycleError("retry certification lost its claimed worker") from exc
    entry, forensic, started, stored_certificate, fresh_validation = _retry_certificate(loaded, item_id)
    if stored_certificate != certificate or fresh_validation != validation:
        raise IncompleteChildRestartLifecycleError("retry proof evidence changed before queue certification")
    timestamp = time.time()
    binding = {
        "worker_id": worker["worker_id"],
        "token": worker["token"],
        "worker_sha256": worker["worker_sha256"],
        "queue_item_sha256_before": item["item_sha256"],
        "timestamp": timestamp,
        "proof_mode": "NORMAL",
        "certificate": copy.deepcopy(dict(certificate)),
        "validation": copy.deepcopy(dict(validation)),
        "restart_plan_sha256": loaded["restart_handoff"]["plan"]["restart_plan_sha256"],
        "forensic_sha256": forensic["forensic_sha256"],
        "retry_child_root": entry["retry_child_root"],
        "retry_started_sha256": started["record_sha256"],
        "retry_session_sha256": started["retry_session_sha256"],
    }
    after = base._expected_certified_queue(
        before,
        item_id=item_id,
        worker_id=worker["worker_id"],
        token=worker["token"],
        certificate=certificate,
        validation=validation,
        timestamp=timestamp,
    )
    prepared = base._prepare_value(
        loaded,
        sequence=len(state["records"]),
        previous_record_sha256=state["previous_record_sha256"],
        action="CERTIFY_CHILD",
        item_id=item_id,
        before=before,
        after=after,
        binding=binding,
    )
    base._publish_exact(
        base._prepare_path(Path(loaded["root"]), prepared["sequence"]),
        prepared,
        label="retry child certification prepare",
    )
    return base._read_transition_state(loaded)


def _revalidate_restart_certification(
    loaded: Mapping[str, Any], prepared: Mapping[str, Any],
) -> None:
    """Freshly recheck a retry proof before a prepared queue write completes."""

    binding = prepared.get("binding")
    if not isinstance(binding, dict):
        raise IncompleteChildRestartLifecycleError("prepared retry certification has no binding")
    item_id = prepared.get("item_id")
    if type(item_id) is not str or binding.get("proof_mode") != "NORMAL":
        raise IncompleteChildRestartLifecycleError("prepared retry certification has an invalid proof mode")
    before = prepared.get("before_queue")
    if not isinstance(before, dict):
        raise IncompleteChildRestartLifecycleError("prepared retry certification has no prior queue")
    try:
        item, worker, _original_root = base._worker_for_item(
            loaded, before, item_id, require_live_claim=True,
        )
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartLifecycleError("prepared retry certification lost worker ownership") from exc
    entry, forensic, started, certificate, validation = _retry_certificate(loaded, item_id)
    expected = {
        "worker_id": worker["worker_id"],
        "token": worker["token"],
        "worker_sha256": worker["worker_sha256"],
        "queue_item_sha256_before": item["item_sha256"],
        "restart_plan_sha256": loaded["restart_handoff"]["plan"]["restart_plan_sha256"],
        "forensic_sha256": forensic["forensic_sha256"],
        "retry_child_root": entry["retry_child_root"],
        "retry_started_sha256": started["record_sha256"],
        "retry_session_sha256": started["retry_session_sha256"],
    }
    if any(binding.get(key) != value for key, value in expected.items()):
        raise IncompleteChildRestartLifecycleError("prepared retry certification handoff binding changed")
    if binding.get("certificate") != certificate:
        raise IncompleteChildRestartLifecycleError("prepared retry certificate changed")
    stored_validation = binding.get("validation")
    if not isinstance(stored_validation, dict):
        raise IncompleteChildRestartLifecycleError("prepared retry validation is absent")
    # The validation includes fresh checker receipts, so its exact digest is
    # expected to change at every replay.  Its semantic proof requirements are
    # nevertheless checked again against the current certificate and queue.
    if not recursive._queue_certificate_complete(certificate, item, stored_validation):
        raise IncompleteChildRestartLifecycleError("prepared retry certificate is no longer complete")
    if not recursive._queue_certificate_complete(certificate, item, validation):
        raise IncompleteChildRestartLifecycleError("fresh retry replay is no longer complete")


def _apply_prepared_transition(
    loaded: Mapping[str, Any], state: Mapping[str, Any],
) -> dict[str, Any]:
    """Complete an interrupted retry lifecycle mutation after fresh replay."""

    prepared = state.get("pending")
    if prepared is None:
        return dict(state)
    current = state["current_queue"]
    before = prepared["before_queue"]
    after = prepared["after_queue"]
    binding = prepared["binding"]
    if current == before:
        if prepared["action"] == "CERTIFY_CHILD":
            _revalidate_restart_certification(loaded, prepared)
            actual = recursive.certify_queue_item(
                Path(loaded["root"]) / supervisor.QUEUE,
                item_id=prepared["item_id"],
                worker_id=binding["worker_id"],
                token=binding["token"],
                certificate=binding["certificate"],
                validation=binding["validation"],
                now=float(binding["timestamp"]),
            )
        elif prepared["action"] == "RENEW_CLAIM":
            actual = recursive.renew_queue_item(
                Path(loaded["root"]) / supervisor.QUEUE,
                item_id=prepared["item_id"],
                worker_id=binding["worker_id"],
                token=binding["token"],
                lease_seconds=float(binding["lease_seconds"]),
                now=float(binding["timestamp"]),
            )
        else:
            raise IncompleteChildRestartLifecycleError("prepared retry transition action is unsupported")
        if actual != after:
            raise IncompleteChildRestartLifecycleError("retry queue mutation did not match its prepared transition")
    elif current == after:
        if prepared["action"] == "CERTIFY_CHILD":
            _revalidate_restart_certification(loaded, prepared)
    else:
        raise IncompleteChildRestartLifecycleError("retry queue differs from its prepared transition")
    transition = base._transition_value(loaded, prepared)
    base._publish_exact(
        base._transition_path(Path(loaded["root"]), prepared["sequence"]),
        transition,
        label="retry queue transition",
    )
    return base._read_transition_state(loaded)


def _tick_claimed_item(
    loaded: Mapping[str, Any], state: Mapping[str, Any], *, item_id: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Observe a retry child; only a fresh terminal replay can certify it."""

    queue = state["committed_queue"]
    try:
        item, worker, _original_root = base._worker_for_item(
            loaded, queue, item_id, require_live_claim=True,
        )
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartLifecycleError("retry claimed item is malformed") from exc
    if item["claim"]["lease_expires_at"] - time.time() < supervisor.RENEW_BEFORE_SECONDS:
        state = base._begin_renewal(loaded, state, item_id=item_id)
        state = _apply_prepared_transition(loaded, state)
        return state, {"item_id": item_id, "action": "LEASE_RENEWED"}
    entry, _forensic, _intent, _started, root = _retry_evidence(loaded, item_id)
    if entry.get("cpu_ids") != worker.get("cpu_ids"):
        raise IncompleteChildRestartLifecycleError("retry child CPU no longer matches its retained queue lease")
    status = supervisor.child_runner.status_root(root, verify_hashes=False)
    observed = status.get("state")
    if observed in {"INACTIVE_UNCHECKPOINTED", "CHECKPOINTED"}:
        supervisor.child_runner.harvest_stopped_root(root)
        status = supervisor.child_runner.status_root(root, verify_hashes=False)
        observed = status.get("state")
    if observed == "PROOF_CARRYING_CHILD_UNSAT":
        entry, forensic, started, certificate, validation = _retry_certificate(loaded, item_id)
        state = _begin_restart_certification(
            loaded, state, item_id=item_id, certificate=certificate, validation=validation,
        )
        state = _apply_prepared_transition(loaded, state)
        return state, {
            "item_id": item_id,
            "action": "CERTIFIED",
            "certificate_sha256": certificate["certificate_sha256"],
            "forensic_sha256": forensic["forensic_sha256"],
            "retry_started_sha256": started["record_sha256"],
        }
    return state, {"item_id": item_id, "action": "OBSERVED", "state": observed}


def _aggregate_if_complete(loaded: Mapping[str, Any]) -> dict[str, Any] | None:
    root = Path(loaded["root"])
    status = recursive.split_queue_status(root / supervisor.QUEUE)
    if status.get("status") != recursive.QUEUE_STATUS_COMPLETE:
        return None
    queue = recursive.load_split_queue(root / supervisor.QUEUE)
    certificates: list[dict[str, Any]] = []
    for item in queue["items"]:
        item_id = item["item_id"]
        entry, _forensic, _started, certificate, validation = _retry_certificate(loaded, item_id)
        if not recursive._queue_certificate_complete(certificate, item, validation):
            raise IncompleteChildRestartLifecycleError("complete retry queue includes an incomplete certificate")
        if entry.get("item_id") != item_id:
            raise IncompleteChildRestartLifecycleError("complete retry queue has a mismatched handoff entry")
        certificates.append(certificate)
    aggregate = recursive.aggregate_child_certificates(loaded["manifest"], certificates)
    if aggregate.get("status") != "PARENT_CUBE_UNSAT":
        raise IncompleteChildRestartLifecycleError("complete retry frontier did not aggregate to parent UNSAT")
    expected = supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PARENT_AGGREGATE_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "restart_plan_sha256": loaded["restart_handoff"]["plan"]["restart_plan_sha256"],
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
    base._publish_exact(root / supervisor.PARENT_AGGREGATE, expected, label="retry parent aggregate")
    supervisor._release_cpus(Path(loaded["control_root"]), loaded["reservation"])
    return expected


@contextlib.contextmanager
def _runtime() -> Iterator[None]:
    """Use the proven initial queue ledger under a distinct retry namespace."""

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
    try:
        for name, value in replacements.items():
            setattr(base, name, value)
        yield
    finally:
        for name, value in saved.items():
            setattr(base, name, value)


def tick_bundle(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Progress one retry-root lifecycle tick without touching original roots."""

    target = Path(bundle)
    with _runtime():
        with initial._dispatch_lock(target):
            with base._lifecycle_lock(target):
                loaded = base._load_initial_batch(target, control_root=control_root)
                # Recheck the stopped original roots on each tick: a resumed or
                # modified old transport is an audit stop, never hidden by the
                # retry path.
                handoff = restart.load_restart(
                    loaded, require_started=True, recheck_original=True,
                )
                loaded = {**loaded, "restart_handoff": handoff}
                parent_root = Path(loaded["audit"]["parent_root"])
                with recovery._legacy_shared_lock(parent_root):
                    recovery._checked_checkpointed_parent(loaded)
                    state = base._read_transition_state(loaded)
                    aggregate_path = Path(loaded["root"]) / supervisor.PARENT_AGGREGATE
                    if not aggregate_path.exists() and not aggregate_path.is_symlink():
                        with supervisor._catalog_lock(Path(loaded["control_root"])):
                            recovery._require_reserved_cpu_leases(loaded)
                    state = _apply_prepared_transition(loaded, state)
                    actions: list[dict[str, Any]] = []
                    for item in recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)["items"]:
                        if item.get("state") != "CLAIMED":
                            continue
                        state, action = _tick_claimed_item(loaded, state, item_id=item["item_id"])
                        actions.append(action)
                        if action["action"] in {"LEASE_RENEWED", "CERTIFIED"}:
                            break
                    aggregate = _aggregate_if_complete(loaded)
                    queue_status = recursive.split_queue_status(Path(loaded["root"]) / supervisor.QUEUE)
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "restart_plan_sha256": loaded["restart_handoff"]["plan"]["restart_plan_sha256"],
            "queue_status": queue_status,
            "actions": actions,
            "aggregate": aggregate,
            "complete": queue_status.get("status") == recursive.QUEUE_STATUS_COMPLETE,
            "hardness_only": aggregate is None,
            "solver_terminal_claim": aggregate is not None,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


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
        IncompleteChildRestartLifecycleError,
        restart.IncompleteChildRestartError,
        base.InitialBatchLifecycleError,
        initial.InitialBatchDispatchError,
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
