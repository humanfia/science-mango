from __future__ import annotations

import itertools
from pathlib import Path

import numpy as np

from evaluation.bb_code import build_bb_code
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import SAT_EVIDENCE_KIND, SAT_EVIDENCE_SCHEMA_VERSION
from evaluation.twobga_subsystem import (
    derive_twobga_subsystem_problem,
    gf2_nullspace,
    gf2_rank,
)
from scripts import screen_frontier_twobga as twobga_screen


def _candidate(ell, m, a_terms, b_terms, *, digest="candidate"):
    code = build_bb_code(ell, m, a_terms, b_terms)
    return {
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "required_distance": 2,
        "canonical_digest": digest,
    }


def _minimum_predicate_weight(checks: np.ndarray, detectors: np.ndarray) -> int:
    n = int(checks.shape[1])
    for weight in range(1, n + 1):
        for support in itertools.combinations(range(n), weight):
            vector = np.zeros(n, dtype=np.uint8)
            vector[list(support)] = 1
            if not np.any((checks @ vector) & 1) and np.any(
                (detectors @ vector) & 1
            ):
                return weight
    return n + 1


def _matrices(candidate):
    code = build_bb_code(
        candidate["ell"],
        candidate["m"],
        candidate["A_terms"],
        candidate["B_terms"],
    )
    hx, hz, lx, lz = get_code_matrices(code)
    return code, hx, hz, lx, lz


def _sealed_unsat(max_weight: int) -> dict:
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "outcome": "unsat",
        "decision_complete": True,
        "threshold_infeasible": True,
        "max_weight": max_weight,
        "operator": None,
        "objective": None,
    }
    evidence["evidence_sha256"] = twobga_screen._canonical_sha256(evidence)
    return evidence


def _sealed_sat(max_weight: int, objective: int) -> dict:
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "outcome": "sat",
        "decision_complete": True,
        "threshold_infeasible": False,
        "max_weight": max_weight,
        "objective": objective,
    }
    evidence["evidence_sha256"] = twobga_screen._canonical_sha256(evidence)
    return evidence


def _unit(unit_id: str, evidence: dict, *, verified=False) -> dict:
    return {
        "unit_id": unit_id,
        "solver_evidence": evidence,
        "witness_verified": verified,
    }


def test_nullspace_and_rank_are_exactly_over_gf2():
    matrix = np.array([[1, 1, 0], [0, 1, 1], [1, 0, 1]], dtype=np.uint8)
    # The three rows are real-linearly independent but sum to zero over GF(2).
    assert np.linalg.matrix_rank(matrix.astype(float)) == 3
    assert gf2_rank(matrix) == 2
    nullspace = gf2_nullspace(matrix)
    assert nullspace.shape == (1, 3)
    assert not np.any((matrix @ nullspace.T) & 1)


def test_eligible_problem_uses_centers_and_compresses_to_ks():
    candidate = _candidate(
        2,
        3,
        [(0, 0), (0, 1)],
        [(0, 0), (1, 1)],
    )
    code, hx, hz, _, _ = _matrices(candidate)
    problem = derive_twobga_subsystem_problem(
        hx,
        hz,
        ell=2,
        m=3,
        expected_n=int(code.num_qudits),
        expected_k=int(code.dimension),
    )
    assert problem.eligible is True
    assert problem.report["subsystem_k"] == 1
    assert problem.report["rank_defects"] == {"delta_x": 0, "delta_z": 0}
    assert problem.x_detectors.shape == problem.z_detectors.shape == (1, 6)
    assert _minimum_predicate_weight(
        problem.x_checks, problem.x_detectors,
    ) == 2
    assert _minimum_predicate_weight(
        problem.z_checks, problem.z_detectors,
    ) == 1


def test_bare_gauge_checks_are_forbidden_by_dressed_regression():
    candidate = _candidate(
        5,
        2,
        [(0, 0), (4, 0)],
        [(3, 1), (2, 1)],
    )
    code, hx, hz, _, _ = _matrices(candidate)
    problem = derive_twobga_subsystem_problem(
        hx,
        hz,
        ell=5,
        m=2,
        expected_n=int(code.num_qudits),
        expected_k=int(code.dimension),
    )
    assert problem.eligible is True
    dressed = min(
        _minimum_predicate_weight(problem.x_checks, problem.x_detectors),
        _minimum_predicate_weight(problem.z_checks, problem.z_detectors),
    )
    bare = min(
        _minimum_predicate_weight(problem.z_gauge, problem.x_detectors),
        _minimum_predicate_weight(problem.x_gauge, problem.z_detectors),
    )
    assert dressed == 1
    assert bare == 5
    assert problem.report["sectors"]["X"]["distance_semantics"] == (
        "dressed-logical-center-quotient"
    )


def test_rank_defect_candidate_is_ineligible_before_sat(monkeypatch, tmp_path):
    candidate = _candidate(
        15,
        12,
        [(0, 10), (0, 11), (6, 0)],
        [(0, 3), (7, 0), (14, 0)],
        digest="40bc",
    )
    candidate["required_distance"] = 24

    def forbidden_solver(*args, **kwargs):
        raise AssertionError("ineligible candidate must not start SAT")

    monkeypatch.setattr(twobga_screen, "solve_css_sector_sat", forbidden_solver)
    artifact = twobga_screen.screen_twobga_candidate(
        candidate,
        output=tmp_path / "artifact.json",
        timeout=1,
        workers=1,
        threshold_only=False,
    )
    assert artifact["status"] == "INELIGIBLE"
    assert artifact["expected_units"] == artifact["terminal_units"] == 0
    assert artifact["theorem_eligibility"]["subsystem_k"] == 0
    assert artifact["theorem_eligibility"]["rank_defects"] == {
        "delta_x": 4,
        "delta_z": 4,
    }
    assert Path(tmp_path / "artifact.json").exists()


def test_auxiliary_sat_witness_never_rejects_original_candidate():
    auxiliary_sat = _sealed_sat(1, 1)
    units = {
        "aux-lower-X": _unit("aux-lower-X", auxiliary_sat, verified=True),
        "aux-lower-Z": _unit("aux-lower-Z", _sealed_unsat(1)),
    }
    assert twobga_screen.classify_twobga_units(
        units, required_distance=2, threshold_only=True,
    ) == twobga_screen.TWOBGA_BOUND_INSUFFICIENT_STATUS
    artifact = twobga_screen._artifact(
        {"required_distance": 2},
        theorem_report={"eligible": True},
        units=units,
        threshold_only=True,
        started=0.0,
        original_logical_detector=None,
        original_translation_symmetry=None,
    )
    assert artifact["status"] == "BOUND_INSUFFICIENT"
    assert artifact["auxiliary_witnesses"] == [units["aux-lower-X"]]


def test_threshold_screen_runs_both_dressed_auxiliary_sectors(
    monkeypatch, tmp_path,
):
    candidate = _candidate(
        2,
        3,
        [(0, 0), (0, 1)],
        [(0, 0), (1, 1)],
        digest="eligible",
    )
    calls = []

    def fake_solver(checks, detectors, **kwargs):
        calls.append((
            kwargs["sector"],
            np.asarray(checks).copy(),
            np.asarray(detectors).copy(),
            tuple(kwargs["anchor_indices"]),
        ))
        return _sealed_unsat(int(kwargs["max_weight"]))

    monkeypatch.setattr(
        twobga_screen, "validate_candidate_parameters", lambda *args: None,
    )
    monkeypatch.setattr(twobga_screen, "solve_css_sector_sat", fake_solver)
    artifact = twobga_screen.screen_twobga_candidate(
        candidate,
        output=tmp_path / "eligible.json",
        timeout=1,
        workers=2,
        threshold_only=True,
    )
    assert artifact["status"] == "THRESHOLD_PROVEN"
    assert artifact["expected_units"] == artifact["terminal_units"] == 2
    assert {sector for sector, *_ in calls} == {"X", "Z"}
    assert all(detectors.shape == (1, 6) for _, _, detectors, _ in calls)
    assert all(anchors == (0,) for *_, anchors in calls)
    # This asymmetric fixture has different center ranks.  It catches any
    # attempt to reuse the original BB X/Z isometry for the subsystem.
    assert {checks.shape[0] for _, checks, _, _ in calls} == {0, 1}


def test_both_auxiliary_unsat_and_original_witness_prove_exact_threshold():
    original_witness = _sealed_sat(2, 2)
    units = {
        "aux-lower-X": _unit("aux-lower-X", _sealed_unsat(1)),
        "aux-lower-Z": _unit("aux-lower-Z", _sealed_unsat(1)),
        "original-upper-X": _unit(
            "original-upper-X", original_witness, verified=True,
        ),
    }
    assert twobga_screen.classify_twobga_units(
        units, required_distance=2, threshold_only=False,
    ) == "EXACT_PROVEN"
    assert twobga_screen.classify_twobga_units(
        {key: value for key, value in units.items() if key != "aux-lower-Z"},
        required_distance=2,
        threshold_only=False,
    ) == "UNRESOLVED"


def test_exact_mode_terminal_upper_unsat_is_a_nonretryable_exactness_gap():
    lower = {
        "aux-lower-X": _unit("aux-lower-X", _sealed_unsat(1)),
        "aux-lower-Z": _unit("aux-lower-Z", _sealed_unsat(1)),
    }
    exact_mode = {
        **lower,
        "original-upper-X": _unit(
            "original-upper-X", _sealed_unsat(2),
        ),
    }
    assert twobga_screen.classify_twobga_units(
        exact_mode,
        required_distance=2,
        threshold_only=False,
    ) == twobga_screen.TWOBGA_EXACTNESS_GAP_STATUS
    assert twobga_screen.classify_twobga_units(
        exact_mode,
        required_distance=2,
        threshold_only=True,
    ) == "THRESHOLD_PROVEN"

    retryable_upper = {
        **lower,
        "original-upper-X": _unit(
            "original-upper-X",
            {
                "outcome": "timeout",
                "decision_complete": False,
                "retryable": True,
            },
        ),
    }
    assert twobga_screen.classify_twobga_units(
        retryable_upper,
        required_distance=2,
        threshold_only=False,
    ) == "UNRESOLVED"


def test_only_original_low_witness_can_reject():
    units = {
        "original-upper-X": _unit(
            "original-upper-X",
            {"outcome": "sat", "objective": 1, "max_weight": 2},
            verified=True,
        ),
    }
    assert twobga_screen.classify_twobga_units(
        units, required_distance=2, threshold_only=False,
    ) == "REJECTED"
