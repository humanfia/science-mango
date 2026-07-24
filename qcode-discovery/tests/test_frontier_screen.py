from scripts.screen_frontier_candidate import classify_results
from scripts.screen_frontier_xor import (
    classify_xor_results,
    verify_bb_translation_symmetry,
)


def result(objective, *, success=True, gap=0.0, verified=True):
    return {
        "objective": objective,
        "success": success,
        "mip_gap": gap,
        "witness_verified": verified,
    }


def test_low_verified_witness_rejects_immediately():
    assert classify_results(
        [result(14, success=False, gap=0.8)],
        required_distance=15,
        expected_directions=32,
    ) == "REJECTED"


def test_all_optimal_safe_directions_prove_threshold():
    assert classify_results(
        [result(15), result(18)],
        required_distance=15,
        expected_directions=2,
    ) == "THRESHOLD_PROVEN"


def test_all_bounded_models_infeasible_prove_threshold():
    directions = [
        {
            "threshold_infeasible": True,
            "max_weight": 14,
            "operator": None,
        },
    ] * 2
    assert classify_results(
        directions,
        required_distance=15,
        expected_directions=2,
    ) == "THRESHOLD_PROVEN"


def test_xor_sector_low_witness_rejects():
    sectors = [{
        "sector": "Z",
        "objective": 14,
        "witness_verified": True,
    }]
    assert classify_xor_results(
        sectors, required_distance=15, threshold_only=True,
    ) == "REJECTED"


def test_both_xor_sectors_infeasible_prove_threshold():
    sectors = [
        {"sector": name, "threshold_infeasible": True, "max_weight": 14}
        for name in ("X", "Z")
    ]
    assert classify_xor_results(
        sectors, required_distance=15, threshold_only=True,
    ) == "THRESHOLD_PROVEN"


def test_both_xor_sectors_exact_prove_distance():
    sectors = [
        {
            "sector": name,
            "exact": True,
            "witness_verified": True,
            "objective": 15,
        }
        for name in ("X", "Z")
    ]
    assert classify_xor_results(
        sectors, required_distance=15, threshold_only=False,
    ) == "EXACT_PROVEN"


def test_partial_safe_incumbent_remains_unresolved():
    assert classify_results(
        [result(18, success=False, gap=0.7)],
        required_distance=15,
        expected_directions=2,
    ) == "UNRESOLVED"


def test_anchored_xor_proof_requires_verified_symmetry_coverage():
    sectors = [
        {
            "sector": name,
            "threshold_infeasible": True,
            "max_weight": 14,
            "anchor_indices": [0, 36],
        }
        for name in ("X", "Z")
    ]
    assert classify_xor_results(
        sectors, required_distance=15, threshold_only=True,
    ) == "UNRESOLVED"
    assert classify_xor_results(
        sectors,
        required_distance=15,
        threshold_only=True,
        symmetry_coverage_verified=True,
    ) == "THRESHOLD_PROVEN"


def test_known_bb_translation_orbits_are_verified():
    audit = verify_bb_translation_symmetry({
        "ell": 6,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
    })
    assert audit["verified"] is True
    assert audit["method"] == "bb-torus-translation-row-set-v1"
    assert audit["orbit_representatives"] == [0, 36]
    assert audit["orbit_sizes"] == [36, 36]
    assert all(
        generator["hx_row_set_preserved"]
        and generator["hz_row_set_preserved"]
        for generator in audit["generators"]
    )
