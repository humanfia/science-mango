"""Tests for the strict structural-novelty gate."""

from evaluation.structural_dedup import (
    check_css_static_eligibility,
    check_css_structural_novelty,
    deduplicate_css_results,
)


def test_exact_gross_code_is_known():
    result = check_css_structural_novelty(
        12, 6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    assert result["checked"] is True
    assert result["novel"] is False
    assert result["matched_reference"] == "Gross [[144,12,12]]"
    assert result["explicit_isomorphism"]["verified"] is True


def test_non_diagonal_reencoding_of_bravyi_is_known():
    result = check_css_structural_novelty(
        12, 12,
        [(3, 0), (0, 1), (0, 2)],
        [(3, 3), (1, 0), (2, 0)],
    )
    assert result["novel"] is False
    assert result["matched_reference"] == "Bravyi [[288,12,18]]"
    assert result["explicit_isomorphism"]["hx_preserved"] is True
    assert result["explicit_isomorphism"]["hz_preserved"] is True


def test_different_known_parameters_are_not_false_match():
    result = check_css_structural_novelty(
        12, 6,
        [(0, 0), (0, 1), (0, 2)],
        [(0, 0), (1, 0), (2, 0)],
    )
    assert result["checked"] is True
    assert result["novel"] is True
    assert result["matched_reference"] is None


def test_within_run_reencoding_is_replayed_and_deduplicated():
    base = {
        "ell": 12, "m": 6, "n": 144, "k": 8, "d": 4,
        "A_terms": [(0, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (1, 0), (2, 0)],
    }
    shifted = {
        "ell": 12, "m": 6, "n": 144, "k": 8, "d": 4,
        "A_terms": [(1, 0), (1, 1), (1, 2)],
        "B_terms": [(1, 0), (2, 0), (3, 0)],
    }
    kept, rejected = deduplicate_css_results([base, shifted])
    assert len(kept) == 1
    assert len(rejected) == 1
    audit = rejected[0]["structural_novelty"]
    assert audit["relation"] == "within_run_css_tanner_permutation_equivalent"
    assert audit["explicit_isomorphism"]["verified"] is True
    assert audit["explicit_isomorphism"]["hx_preserved"] is True
    assert audit["explicit_isomorphism"]["hz_preserved"] is True


def test_disconnected_humanize_leader_fails_tier0_before_bliss_or_milp():
    static = check_css_static_eligibility(
        12, 12,
        [(0, 0), (0, 2), (0, 4)],
        [(0, 0), (2, 0), (4, 0)],
    )
    assert static["eligible"] is False
    assert static["checks"]["connected_tanner_graph"] is False
    assert static["tanner_components"] == 4

    row = {
        "ell": 12, "m": 12, "n": 288, "k": 32, "d": 20,
        "fom": 44.44444444444444,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (2, 0), (4, 0)],
    }
    kept, rejected = deduplicate_css_results([row])
    assert kept == []
    assert len(rejected) == 1
    assert rejected[0]["structural_rejection"] == "static_ineligible"
    assert rejected[0]["structural_novelty"]["checked"] is False
