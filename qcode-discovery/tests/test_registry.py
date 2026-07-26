"""Tests for the versioned CSS/non-CSS known-code registry."""

from evaluation.bb_code import build_bb_code
from evaluation.pbb_code import build_pbb_code
from evaluation.registry import check_code_novelty, load_registry


def test_registry_integrity_and_coverage():
    registry = load_registry()
    assert registry["summary"]["css"] >= 30
    assert registry["summary"]["noncss"] >= 300


def test_known_gross_code_is_in_expanded_registry():
    code = build_bb_code(
        12, 6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    audit = check_code_novelty(code, code_type="css")
    assert audit["novel"] is False
    assert audit["matched_entries"]


def test_known_pbb_catalog_code_is_in_expanded_registry():
    registry = load_registry()
    entry = next(row for row in registry["entries"] if row["code_type"] == "noncss")
    construction = entry["construction"]
    code = build_pbb_code(
        construction["ell"], construction["m"],
        construction["A_terms"], construction["B_terms"],
        construction["C_terms"], construction["D_terms"],
    )
    audit = check_code_novelty(code, code_type="noncss")
    assert audit["novel"] is False
    assert audit["matched_entries"]
