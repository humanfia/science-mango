from main import merge_bp_milp_result


def _bp(d=8):
    return {"d": d, "d_is_exact": False, "stage": "refined_estimate", "score": 8.0}


def _milp(d=6, *, checked=24, optimal=24, total=24, exact=True):
    return {
        "d": d,
        "d_is_exact": exact,
        "stage": "milp_exact" if exact else "milp_incumbent",
        "milp_details": {
            "exact": exact,
            "num_logicals_checked": checked,
            "logicals_optimal": optimal,
            "total_logicals": total,
        },
    }


def test_fully_covered_milp_is_exact():
    result = merge_bp_milp_result(_bp(), _milp())
    assert result["d"] == 6
    assert result["d_is_exact"] is True
    assert result["distance_source"] == "milp_exact"
    assert result["milp_attempted"] is True


def test_partial_milp_is_never_promoted_to_exact():
    result = merge_bp_milp_result(_bp(), _milp(6, checked=7, optimal=7))
    assert result["d"] == 6
    assert result["d_is_exact"] is False
    assert result["distance_source"] == "milp_incumbent"


def test_tighter_bp_upper_bound_wins_over_milp_incumbent():
    milp = _milp(10, exact=False, checked=8, optimal=7)
    witness = {
        "side": "Z",
        "index": 0,
        "weight": 10,
        "bits": [1] * 10,
    }
    milp["milp_details"]["minimum_direction_witness"] = witness
    invocation = {
        "schema_version": 2,
        "checkpoint_path": "/proof/working.json",
        "resume": True,
        "hard_timeout_per_logical": 330.0,
    }
    symplectic = {
        "side": "Z",
        "index": 0,
        "weight": 10,
        "bits": [1] * 10,
        "dual_side": "X",
        "dual_index": 0,
    }
    milp.update({
        "fom_target": 12.0,
        "fom_rejection_cutoff": 16,
        "challenge_rejection_cutoff": 16,
        "milp_effective_early_stop": 16,
        "milp_solver_attempted": True,
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": True,
        "threshold_rejection_proven": True,
        "threshold_proof_distance": 10,
        "threshold_proof_source": "milp_feasible_upper_bound",
        "threshold_proof_witness": witness,
        "audit_evaluator_invocation": invocation,
        "symplectic_weight_witness": symplectic,
        "d_symplectic": 10,
    })
    result = merge_bp_milp_result(_bp(8), milp)
    assert result["d"] == 8
    assert result["d_is_exact"] is False
    assert result["distance_source"] == "bp_osd"
    assert result["milp_effective_early_stop"] == 16
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_distance"] == 10
    assert result["threshold_proof_source"] == "milp_feasible_upper_bound"
    assert result["threshold_proof_witness"] == witness
    assert result["audit_evaluator_invocation"] == invocation
    assert result["symplectic_weight_witness"] == symplectic
    assert result["d_symplectic"] == 10
    assert (
        result["milp_details"]["minimum_direction_witness"] == witness
    )


def test_bp_merge_preserves_independent_milp_proof_trust():
    bp = _bp(8)
    bp["distance_trusted"] = False
    milp = _milp(10, exact=False, checked=8, optimal=7)
    milp.update(
        {
            "distance_trusted": True,
            "threshold_rejection_proven": True,
        }
    )

    trusted = merge_bp_milp_result(bp, milp)
    assert trusted["distance_source"] == "bp_osd"
    assert trusted["distance_trusted"] is False
    assert trusted["threshold_proof_trusted"] is True

    milp["distance_trusted"] = False
    untrusted = merge_bp_milp_result(bp, milp)
    assert untrusted["threshold_proof_trusted"] is False
