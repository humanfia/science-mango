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
    result = merge_bp_milp_result(_bp(8), _milp(10, exact=False, checked=8, optimal=7))
    assert result["d"] == 8
    assert result["d_is_exact"] is False
    assert result["distance_source"] == "bp_osd"
