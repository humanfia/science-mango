from __future__ import annotations

import copy
import hashlib
import json
from itertools import product
from pathlib import Path

import numpy as np
import pytest

from evaluation.bb_code import build_bb_code
from evaluation.distance_milp import (
    CssExactReplayResult,
    compute_distance_milp,
    get_code_matrices,
)
from evaluation.evaluator import evaluate_candidate_milp
import humanize.audit_state as audit_state_module
from humanize.audit_state import (
    AuditOutcome,
    AuditStateError,
    classify_evaluation,
    seal_audit_attempt_evidence,
)
from humanize.state import code_key


@pytest.fixture(scope="module")
def real_explicit_threshold_proof(tmp_path_factory):
    ell, m = 2, 2
    a_terms = [(0, 0), (0, 1)]
    b_terms = [(1, 0), (1, 1)]
    code = build_bb_code(ell, m, a_terms, b_terms)
    run_dir = tmp_path_factory.mktemp("formal-css-threshold")
    candidate_key = code_key({
        "ell": ell,
        "m": m,
        "A_terms": a_terms,
        "B_terms": b_terms,
    })
    checkpoint = run_dir / "milp-checkpoints" / f"{candidate_key}.json"
    identity = {
        "family": "css-bb",
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
    }
    weight, details = compute_distance_milp(
        code,
        timeout_per_logical=5,
        total_timeout=30,
        early_stop=4,
        checkpoint_path=checkpoint,
        hard_timeout_per_logical=10,
        checkpoint_identity=identity,
    )
    weight = int(weight)
    n, k = int(code.num_qudits), int(code.dimension)
    assert (n, k, weight) == (8, 4, 2)
    assert details["exact"] is False
    witness = copy.deepcopy(details["minimum_direction_witness"])
    row = {
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": n,
        "k": k,
        "d": weight,
        "fom": k * weight * weight / n,
        "stage": "milp_low_d",
        "d_is_exact": False,
        "distance_trusted": True,
        "distance_status": "upper_bound",
        "milp_attempted": True,
        "milp_solver_attempted": True,
        "fom_target": 12.0,
        "fom_target_numerator": 12,
        "fom_target_denominator": 1,
        "fom_rejection_cutoff": 4,
        "challenge_rejection_cutoff": 4,
        "minimum_passing_distance": 5,
        "milp_effective_early_stop": 4,
        "milp_early_stop_objective": "challenge_final_gate",
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": True,
        "threshold_rejection_proven": True,
        "threshold_proof_lhs": k * weight * weight,
        "threshold_proof_rhs": 12 * n,
        "threshold_proof_distance": weight,
        "threshold_proof_source": "milp_feasible_upper_bound",
        "threshold_proof_witness": copy.deepcopy(witness),
        "milp_details": details,
        "audit_evaluator_invocation": {
            "schema_version": 2,
            "checkpoint_path": str(checkpoint),
            "resume": True,
            "timeout_per_logical": 5,
            "total_timeout": 30,
            "hard_timeout_per_logical": 10.0,
        },
    }
    row["candidate_key"] = code_key(row)
    attempt = {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 5,
            "total": 30,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
    }
    row["audit_attempt"] = seal_audit_attempt_evidence(
        row,
        attempt,
        run_dir=run_dir,
        evidence_root=run_dir / "milp-checkpoints" / "evidence",
    )
    return row, checkpoint


def test_real_bb_explicit_threshold_witness_replays(real_explicit_threshold_proof):
    row, _checkpoint = real_explicit_threshold_proof
    assert classify_evaluation(row) is AuditOutcome.THRESHOLD_REJECTED


@pytest.mark.parametrize(
    "mutation",
    (
        "missing",
        "details_mismatch",
        "weight",
        "nonbinary",
        "bits",
        "side",
        "index",
    ),
)
def test_real_bb_explicit_threshold_witness_tampering_is_rejected(
    real_explicit_threshold_proof, mutation,
):
    base, _checkpoint = real_explicit_threshold_proof
    row = copy.deepcopy(base)
    witness = row["threshold_proof_witness"]
    if mutation == "missing":
        row.pop("threshold_proof_witness")
    elif mutation == "details_mismatch":
        row["milp_details"]["minimum_direction_witness"]["index"] = 1
    elif mutation == "weight":
        witness["weight"] -= 1
        row["milp_details"]["minimum_direction_witness"] = copy.deepcopy(witness)
    elif mutation == "nonbinary":
        witness["bits"][0] = 2
        row["milp_details"]["minimum_direction_witness"] = copy.deepcopy(witness)
    elif mutation == "bits":
        witness["bits"][0] ^= 1
        row["milp_details"]["minimum_direction_witness"] = copy.deepcopy(witness)
    elif mutation == "side":
        witness["side"] = "Q"
        row["milp_details"]["minimum_direction_witness"] = copy.deepcopy(witness)
    else:
        witness["index"] = 4
        row["milp_details"]["minimum_direction_witness"] = copy.deepcopy(witness)

    with pytest.raises(AuditStateError):
        classify_evaluation(row)


@pytest.mark.parametrize(
    "field",
    (
        "path",
        "sha256",
        "bytes",
        "checkpoint_kind",
        "checkpoint_schema_version",
        "checkpoint_status",
        "proof_binding_sha256",
    ),
)
def test_schema2_snapshot_descriptor_tampering_fails_closed(
    real_explicit_threshold_proof, field,
):
    row, _checkpoint = real_explicit_threshold_proof
    row = copy.deepcopy(row)
    evidence = row["audit_attempt"]["evidence"]
    if field == "path":
        evidence[field] = str(Path(evidence[field]).with_name("forged.json"))
    elif field == "sha256":
        evidence[field] = "0" * 64
    elif field in {"bytes", "checkpoint_schema_version"}:
        evidence[field] += 1
    else:
        evidence[field] = "forged"
    with pytest.raises(AuditStateError):
        classify_evaluation(row)


@pytest.mark.parametrize("mutation", ("candidate_n", "budget", "witness"))
def test_schema2_semantic_snapshot_tampering_fails_after_outer_rehash(
    real_explicit_threshold_proof, mutation,
):
    base, _checkpoint = real_explicit_threshold_proof
    row = copy.deepcopy(base)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    if mutation == "candidate_n":
        checkpoint["proof_binding"]["n"] += 1
        unsigned = dict(checkpoint["proof_binding"])
        unsigned.pop("binding_sha256")
        checkpoint["proof_binding"]["binding_sha256"] = hashlib.sha256(
            json.dumps(
                unsigned,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
                allow_nan=False,
            ).encode()
        ).hexdigest()
    elif mutation == "budget":
        checkpoint["run_parameters"]["timeout_per_logical_s"] += 1
    else:
        record = next(iter(checkpoint["direction_results"].values()))
        record["witness"][0] ^= 1
    payload = (
        json.dumps(
            checkpoint,
            sort_keys=True,
            ensure_ascii=False,
            indent=2,
            allow_nan=False,
        )
        + "\n"
    ).encode()
    digest = hashlib.sha256(payload).hexdigest()
    forged = original.with_name(f"{digest}.json")
    forged.write_bytes(payload)
    evidence = row["audit_attempt"]["evidence"]
    evidence.update({
        "path": str(forged),
        "sha256": digest,
        "bytes": len(payload),
        "proof_binding_sha256": checkpoint["proof_binding"][
            "binding_sha256"
        ],
    })
    with pytest.raises(AuditStateError):
        classify_evaluation(row)


def test_working_checkpoint_rewrite_does_not_change_immutable_evidence(
    real_explicit_threshold_proof,
):
    row, checkpoint = real_explicit_threshold_proof
    original = checkpoint.read_bytes()
    checkpoint.write_text(json.dumps({"status": "forged"}) + "\n")
    try:
        assert classify_evaluation(row) is AuditOutcome.THRESHOLD_REJECTED
    finally:
        checkpoint.write_bytes(original)


@pytest.mark.parametrize(
    "mutation",
    ("candidate_key", "n", "soft", "hard", "invocation_budget"),
)
def test_schema2_attempt_identity_and_budget_tampering_fails_closed(
    real_explicit_threshold_proof, mutation,
):
    row, _checkpoint = real_explicit_threshold_proof
    row = copy.deepcopy(row)
    if mutation == "candidate_key":
        row["audit_attempt"]["candidate_key"] = "0" * 20
    elif mutation == "n":
        row["audit_attempt"]["n"] += 1
    elif mutation == "soft":
        row["audit_attempt"]["soft"] += 1
    elif mutation == "hard":
        row["audit_attempt"]["hard"] += 1
    else:
        row["audit_evaluator_invocation"]["total_timeout"] += 1
    with pytest.raises(AuditStateError):
        classify_evaluation(row)


def test_seal_rejects_symlink_working_checkpoint(
    real_explicit_threshold_proof, tmp_path,
):
    base, checkpoint = real_explicit_threshold_proof
    row = copy.deepcopy(base)
    row.pop("audit_attempt")
    run_dir = tmp_path / "run"
    checkpoint_root = run_dir / "milp-checkpoints"
    checkpoint_root.mkdir(parents=True)
    target = checkpoint_root / "target.json"
    target.write_bytes(checkpoint.read_bytes())
    working = checkpoint_root / f"{row['candidate_key']}.json"
    working.symlink_to(target)
    row["milp_details"]["checkpoint_path"] = str(working)
    row["audit_evaluator_invocation"]["checkpoint_path"] = str(working)
    with pytest.raises(AuditStateError, match="symlink|safe regular"):
        seal_audit_attempt_evidence(
            row,
            {
                "schema_version": 1,
                "round": 1,
                "kind": "new",
                "attempt": 1,
                "multiplier": 1,
                "soft": 5,
                "total": 30,
                "hard": 10.0,
                "checkpoint": str(working),
            },
            run_dir=run_dir,
            evidence_root=checkpoint_root / "evidence",
        )


def test_schema2_snapshot_symlink_is_rejected(
    real_explicit_threshold_proof,
):
    row, _checkpoint = real_explicit_threshold_proof
    snapshot = Path(row["audit_attempt"]["evidence"]["path"])
    backup = snapshot.with_suffix(".backup")
    snapshot.rename(backup)
    snapshot.symlink_to(backup)
    try:
        with pytest.raises(AuditStateError, match="symlink|safe regular"):
            classify_evaluation(row)
    finally:
        snapshot.unlink()
        backup.rename(snapshot)


def test_tighter_bp_distance_does_not_discard_formal_css_proof(
    real_explicit_threshold_proof,
):
    from main import merge_bp_milp_result

    formal, checkpoint = real_explicit_threshold_proof
    milp = copy.deepcopy(formal)
    milp.pop("audit_attempt")
    bp = {
        key: copy.deepcopy(milp[key])
        for key in ("ell", "m", "A_terms", "B_terms", "n", "k")
    }
    bp.update({
        "d": 1,
        "fom": bp["k"] / bp["n"],
        "score": bp["k"] / bp["n"],
        "stage": "refined_estimate",
        "d_is_exact": False,
        "distance_trusted": True,
    })
    merged = merge_bp_milp_result(bp, milp)
    assert merged["distance_source"] == "bp_osd"
    assert merged["d"] == 1
    merged["candidate_key"] = code_key(merged)
    merged["audit_attempt"] = seal_audit_attempt_evidence(
        merged,
        {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 5,
            "total": 30,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
        },
        run_dir=checkpoint.parents[1],
        evidence_root=checkpoint.parent / "evidence",
    )
    assert classify_evaluation(merged) is AuditOutcome.THRESHOLD_REJECTED


def _formal_exact_css_row(tmp_path):
    ell, m = 2, 2
    a_terms = [(0, 0), (0, 1)]
    b_terms = [(1, 0), (1, 1)]
    code = build_bb_code(ell, m, a_terms, b_terms)
    candidate_key = code_key({
        "ell": ell,
        "m": m,
        "A_terms": a_terms,
        "B_terms": b_terms,
    })
    checkpoint = tmp_path / "milp-checkpoints" / f"{candidate_key}.json"
    identity = {
        "family": "css-bb",
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
    }
    distance, details = compute_distance_milp(
        code,
        timeout_per_logical=5,
        total_timeout=30,
        early_stop=None,
        checkpoint_path=checkpoint,
        hard_timeout_per_logical=10,
        checkpoint_identity=identity,
    )
    assert details["exact"] is True
    row = {
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "d": int(distance),
        "fom": int(code.dimension) * int(distance) ** 2 / int(code.num_qudits),
        "encoding_rate": int(code.dimension) / int(code.num_qudits),
        "stage": "milp_exact",
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
        "milp_attempted": True,
        "milp_solver_attempted": True,
        "milp_effective_early_stop": None,
        "threshold_rejection_proven": False,
        "milp_details": details,
        "audit_evaluator_invocation": {
            "schema_version": 2,
            "checkpoint_path": str(checkpoint),
            "resume": True,
            "timeout_per_logical": 5,
            "total_timeout": 30,
            "hard_timeout_per_logical": 10.0,
        },
    }
    row["score"] = row["fom"]
    row["candidate_key"] = code_key(row)
    row["audit_attempt"] = seal_audit_attempt_evidence(
        row,
        {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 5,
            "total": 30,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
        },
        run_dir=tmp_path,
        evidence_root=tmp_path / "milp-checkpoints" / "evidence",
    )
    return row, code


def test_schema2_exact_css_checkpoint_replays_all_directions(tmp_path):
    row, _code = _formal_exact_css_row(tmp_path)
    assert classify_evaluation(row) is AuditOutcome.EXACT

    missing_witness = copy.deepcopy(row)
    missing_witness["milp_details"]["minimum_direction_witness"] = None
    with pytest.raises(AuditStateError):
        classify_evaluation(missing_witness)

    forged_exact = copy.deepcopy(row)
    forged_exact["milp_details"]["num_logicals_checked"] -= 1
    with pytest.raises(AuditStateError):
        classify_evaluation(forged_exact)

    for field in ("fom", "score", "encoding_rate"):
        forged_metric = copy.deepcopy(row)
        forged_metric[field] += 1.0
        with pytest.raises(AuditStateError, match=f"{field} disagrees"):
            classify_evaluation(forged_metric)


def _replace_evidence_snapshot(row, checkpoint):
    original = Path(row["audit_attempt"]["evidence"]["path"])
    payload = (
        json.dumps(
            checkpoint,
            sort_keys=True,
            ensure_ascii=False,
            indent=2,
            allow_nan=False,
        )
        + "\n"
    ).encode()
    digest = hashlib.sha256(payload).hexdigest()
    rewritten = original.with_name(f"{digest}.json")
    rewritten.write_bytes(payload)
    row["audit_attempt"]["evidence"].update({
        "path": str(rewritten),
        "sha256": digest,
        "bytes": len(payload),
        "checkpoint_status": checkpoint["status"],
    })


def _maximum_feasible_direction(checks, logical):
    n = int(checks.shape[1])
    best = None
    for raw in product((0, 1), repeat=n):
        vector = np.asarray(raw, dtype=np.uint8)
        if (
            np.any((checks @ vector) % 2)
            or int(np.dot(logical, vector) % 2) != 1
        ):
            continue
        if best is None or int(np.sum(vector)) > int(np.sum(best)):
            best = vector
    assert best is not None
    return [int(value) for value in best]


def test_schema2_forged_optimal_status_cannot_create_exact_lower_bound(tmp_path):
    row, code = _formal_exact_css_row(tmp_path)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    hx, hz, lx, lz = get_code_matrices(code)
    proofs = []
    for direction_id, record in checkpoint["direction_results"].items():
        side = record["side"]
        index = int(record["index"])
        checks = hx if side == "Z" else hz
        logical = lx[index] if side == "Z" else lz[index]
        witness = _maximum_feasible_direction(checks, logical)
        weight = sum(witness)
        assert weight == 6
        record["weight"] = weight
        record["witness"] = witness
        record["status"] = "optimal"
        record["optimal"] = True
        proofs.append((
            weight,
            0 if side == "Z" else 1,
            index,
            {
                "side": side,
                "index": index,
                "weight": weight,
                "bits": witness,
            },
        ))

    row["d"] = 6
    row["fom"] = row["k"] * 36 / row["n"]
    if "score" in row:
        row["score"] = row["fom"]
    row["milp_details"]["d_x"] = 6
    row["milp_details"]["d_z"] = 6
    row["milp_details"]["minimum_direction_witness"] = min(
        proofs, key=lambda item: item[:3]
    )[-1]
    _replace_evidence_snapshot(row, checkpoint)

    with pytest.raises(AuditStateError, match="optimal_weight_mismatch"):
        classify_evaluation(row)


def test_schema2_exact_replay_unavailable_stays_unresolved(
    tmp_path, monkeypatch
):
    row, _code = _formal_exact_css_row(tmp_path)
    audit_state_module._EXACT_REPLAY_CACHE.clear()

    def unavailable(*_args, **_kwargs):
        return CssExactReplayResult(
            status="unavailable",
            reason="test_solver_unavailable",
            checked_directions=0,
            total_directions=2 * row["k"],
            elapsed_s=0.0,
        )

    monkeypatch.setattr(
        "evaluation.distance_milp.replay_css_exact_directions",
        unavailable,
    )
    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


def test_schema2_exact_replay_unavailable_is_retried_in_same_process(
    tmp_path, monkeypatch
):
    row, _code = _formal_exact_css_row(tmp_path)
    audit_state_module._EXACT_REPLAY_CACHE.clear()
    calls = 0

    def unavailable_then_exact(*_args, **_kwargs):
        nonlocal calls
        calls += 1
        total = 2 * row["k"]
        return CssExactReplayResult(
            status="unavailable" if calls == 1 else "exact",
            reason="transient_solver_outage" if calls == 1 else "verified",
            checked_directions=0 if calls == 1 else total,
            total_directions=total,
            elapsed_s=0.0,
        )

    monkeypatch.setattr(
        "evaluation.distance_milp.replay_css_exact_directions",
        unavailable_then_exact,
    )
    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    assert classify_evaluation(row) is AuditOutcome.EXACT
    assert calls == 2


def test_exact_replay_uses_cumulative_retry_total_budget(
    tmp_path, monkeypatch
):
    row, _code = _formal_exact_css_row(tmp_path)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    checkpoint["run_parameters"].update({
        "timeout_per_logical_s": 20.0,
        "total_timeout_s": 120.0,
        "hard_timeout_per_logical_s": 40.0,
    })
    row["audit_evaluator_invocation"].update({
        "timeout_per_logical": 20,
        "total_timeout": 120,
        "hard_timeout_per_logical": 40.0,
    })
    row["audit_attempt"].update({
        "kind": "retry",
        "attempt": 3,
        "multiplier": 4,
        "soft": 20,
        "total": 120,
        "hard": 40.0,
    })
    _replace_evidence_snapshot(row, checkpoint)
    observed = {}
    audit_state_module._EXACT_REPLAY_CACHE.clear()

    def unavailable(_code, _records, **budgets):
        observed.update(budgets)
        return CssExactReplayResult(
            status="unavailable",
            reason="test_solver_unavailable",
            checked_directions=0,
            total_directions=2 * row["k"],
            elapsed_s=0.0,
        )

    monkeypatch.setattr(
        "evaluation.distance_milp.replay_css_exact_directions",
        unavailable,
    )
    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    assert observed == {
        "timeout_per_logical": 20,
        "total_timeout": 210,
        "hard_timeout_per_logical": 40.0,
    }


def test_exact_replay_unavailable_keeps_valid_threshold_upper_bound(
    tmp_path, monkeypatch
):
    row, _code = _formal_exact_css_row(tmp_path)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    checkpoint["run_parameters"]["early_stop"] = 4
    row.update({
        "fom_target": 12.0,
        "fom_target_numerator": 12,
        "fom_target_denominator": 1,
        "fom_rejection_cutoff": 4,
        "challenge_rejection_cutoff": 4,
        "minimum_passing_distance": 5,
        "milp_effective_early_stop": 4,
        "milp_early_stop_objective": "challenge_final_gate",
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": True,
        "threshold_rejection_proven": True,
        "threshold_proof_lhs": row["k"] * row["d"] ** 2,
        "threshold_proof_rhs": 12 * row["n"],
        "threshold_proof_distance": row["d"],
        "threshold_proof_source": "milp_exact",
        "threshold_proof_witness": copy.deepcopy(
            row["milp_details"]["minimum_direction_witness"]
        ),
    })
    _replace_evidence_snapshot(row, checkpoint)
    audit_state_module._EXACT_REPLAY_CACHE.clear()

    monkeypatch.setattr(
        "evaluation.distance_milp.replay_css_exact_directions",
        lambda *_args, **_kwargs: CssExactReplayResult(
            status="unavailable",
            reason="test_solver_unavailable",
            checked_directions=0,
            total_directions=2 * row["k"],
            elapsed_s=0.0,
        ),
    )
    assert classify_evaluation(row) is AuditOutcome.THRESHOLD_REJECTED


def test_self_dual_d2_formal_result_can_be_sealed_and_replayed(tmp_path):
    terms = [(3, 0), (0, 1), (0, 2)]
    defining = {
        "ell": 6,
        "m": 6,
        "A_terms": terms,
        "B_terms": terms,
    }
    checkpoint = (
        tmp_path
        / "milp-checkpoints"
        / f"{code_key(defining)}.json"
    )
    row = evaluate_candidate_milp(
        6,
        6,
        terms,
        terms,
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_checkpoint_path=checkpoint,
        milp_hard_timeout_per_logical=10,
    )
    row["candidate_key"] = code_key(row)
    row["audit_attempt"] = seal_audit_attempt_evidence(
        row,
        {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 30,
            "total": 120,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
        },
        run_dir=tmp_path,
        evidence_root=tmp_path / "milp-checkpoints" / "evidence",
    )

    assert row["stage"] == "symplectic_low_d"
    assert classify_evaluation(row) is AuditOutcome.EXACT


def test_all_optimal_checkpoint_status_must_be_exact(tmp_path):
    row, _code = _formal_exact_css_row(tmp_path)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    checkpoint["status"] = "unresolved"
    row["milp_details"]["checkpoint_status"] = "unresolved"
    _replace_evidence_snapshot(row, checkpoint)

    with pytest.raises(AuditStateError, match="status=exact"):
        classify_evaluation(row)


def test_old_verifier_exact_evidence_is_retried_after_source_upgrade(tmp_path):
    row, _code = _formal_exact_css_row(tmp_path)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    implementation = checkpoint["proof_binding"]["implementation"]
    implementation["distance_milp_py_sha256"] = "0" * 64
    unsigned_implementation = dict(implementation)
    unsigned_implementation.pop("fingerprint_sha256", None)
    implementation["fingerprint_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned_implementation,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    binding = checkpoint["proof_binding"]
    unsigned_binding = dict(binding)
    unsigned_binding.pop("binding_sha256", None)
    binding["binding_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned_binding,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    row["audit_attempt"]["evidence"]["proof_binding_sha256"] = binding[
        "binding_sha256"
    ]
    _replace_evidence_snapshot(row, checkpoint)

    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


@pytest.fixture(scope="module")
def real_symplectic_threshold_proof(tmp_path_factory):
    run_dir = tmp_path_factory.mktemp("formal-symplectic-threshold")
    defining = {
        "ell": 12,
        "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    }
    checkpoint = (
        run_dir
        / "milp-checkpoints"
        / f"{code_key(defining)}.json"
    )
    row = evaluate_candidate_milp(
        12,
        6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
        milp_target_fom=12.0,
        milp_timeout_per_logical=5,
        milp_total_timeout=30,
        milp_checkpoint_path=checkpoint,
        milp_hard_timeout_per_logical=10,
    )
    assert row["stage"] == "symplectic_low_d"
    assert row["d_is_exact"] is False
    row["candidate_key"] = code_key(row)
    row["milp_attempted"] = True
    row["audit_attempt"] = seal_audit_attempt_evidence(
        row,
        {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 5,
            "total": 30,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
        },
        run_dir=run_dir,
        evidence_root=run_dir / "milp-checkpoints" / "evidence",
    )
    return row


def test_schema2_symplectic_threshold_replays_real_dual(
    real_symplectic_threshold_proof,
):
    assert (
        classify_evaluation(real_symplectic_threshold_proof)
        is AuditOutcome.THRESHOLD_REJECTED
    )


def test_tighter_bp_distance_preserves_formal_symplectic_proof(
    real_symplectic_threshold_proof,
):
    from main import merge_bp_milp_result

    formal = real_symplectic_threshold_proof
    milp = copy.deepcopy(formal)
    milp.pop("audit_attempt")
    checkpoint = Path(milp["milp_details"]["checkpoint_path"])
    bp = {
        key: copy.deepcopy(milp[key])
        for key in ("ell", "m", "A_terms", "B_terms", "n", "k")
    }
    bp.update({
        "d": int(milp["d"]) - 1,
        "stage": "refined_estimate",
        "d_is_exact": False,
        "distance_trusted": True,
    })
    bp["fom"] = bp["k"] * bp["d"] ** 2 / bp["n"]
    bp["score"] = bp["fom"]
    merged = merge_bp_milp_result(bp, milp)
    assert merged["distance_source"] == "bp_osd"
    assert merged["d_symplectic"] == milp["d_symplectic"]
    merged["candidate_key"] = code_key(merged)
    merged["audit_attempt"] = seal_audit_attempt_evidence(
        merged,
        {
            "schema_version": 1,
            "round": 1,
            "kind": "new",
            "attempt": 1,
            "multiplier": 1,
            "soft": 5,
            "total": 30,
            "hard": 10.0,
            "checkpoint": str(checkpoint),
        },
        run_dir=checkpoint.parents[1],
        evidence_root=checkpoint.parent / "evidence",
    )
    assert classify_evaluation(merged) is AuditOutcome.THRESHOLD_REJECTED


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("side", "Q"),
        ("index", 999),
        ("dual_side", "Q"),
        ("dual_index", 999),
        ("weight", 1),
    ),
)
def test_schema2_symplectic_witness_mutations_fail_closed(
    real_symplectic_threshold_proof, field, value,
):
    row = copy.deepcopy(real_symplectic_threshold_proof)
    row["symplectic_weight_witness"][field] = value
    row["threshold_proof_witness"] = copy.deepcopy(
        row["symplectic_weight_witness"]
    )
    row["milp_details"]["symplectic_weight_witness"] = copy.deepcopy(
        row["symplectic_weight_witness"]
    )
    with pytest.raises(AuditStateError):
        classify_evaluation(row)


def test_symplectic_dual_tamper_fails_after_all_outer_hashes_are_recomputed(
    real_symplectic_threshold_proof,
):
    row = copy.deepcopy(real_symplectic_threshold_proof)
    original = Path(row["audit_attempt"]["evidence"]["path"])
    checkpoint = json.loads(original.read_text())
    checkpoint["symplectic_witness"]["dual_index"] = 999
    binding = checkpoint["proof_binding"]
    binding["witness_sha256"] = hashlib.sha256(
        json.dumps(
            checkpoint["symplectic_witness"],
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    unsigned = dict(binding)
    unsigned.pop("binding_sha256")
    binding["binding_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    payload = (
        json.dumps(
            checkpoint,
            sort_keys=True,
            ensure_ascii=False,
            indent=2,
            allow_nan=False,
        )
        + "\n"
    ).encode()
    digest = hashlib.sha256(payload).hexdigest()
    forged = original.with_name(f"{digest}.json")
    forged.write_bytes(payload)
    row["audit_attempt"]["evidence"].update({
        "path": str(forged),
        "sha256": digest,
        "bytes": len(payload),
        "proof_binding_sha256": binding["binding_sha256"],
    })
    with pytest.raises(AuditStateError, match="logical/dual replay"):
        classify_evaluation(row)
