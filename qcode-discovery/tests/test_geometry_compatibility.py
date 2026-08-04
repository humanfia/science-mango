"""Cross-layer compatibility and isolation tests for BB outer geometry."""

from __future__ import annotations

import json

import numpy as np

import evaluation.distance_sat as distance_sat
import evaluation.sector_certificate as sector_certificate
from evaluation.bb_code import build_bb_code
from evaluation.distance_milp import get_code_matrices
from evaluation.evaluator import (
    _load_milp_cache,
    _milp_cache_key,
    _milp_cache_record,
    _milp_cache_run_parameters,
    evaluate_candidate_milp,
)
from evaluation.final_gate import _matrix_sha256, evaluate_final_gate
from evaluation.proof_triage import candidate_identity
from evaluation.results import _code_key as result_code_key
from evaluation.structural_dedup import (
    annotate_css_result,
    structural_screen_input_sha256,
)
from humanize.audit_state import _candidate_snapshot
from humanize.reviewer import _upper_bound_neutral_advisory
from humanize.state import EliteArchive, archive_cell, code_key
from scripts import screen_frontier_sat as sat_screen
from scripts.audit_candidate_pool import (
    _construction_candidate,
    rank_candidate_files,
)
from scripts.screen_frontier_xor import verify_bb_translation_symmetry


_ELL = 6
_M = 6
_A = [[0, 0], [1, 0], [0, 1]]
_B = [[0, 0], [2, 0], [0, 2]]
_ZERO_GEOMETRY = {
    "schema_version": 1,
    "family": "twisted_torus",
    "twist": 0,
}
_TWISTED_GEOMETRY = {
    "schema_version": 1,
    "family": "twisted_torus",
    "twist": 1,
}


def _candidate(*, geometry=None) -> dict:
    row = {
        "ell": _ELL,
        "m": _M,
        "n": 2 * _ELL * _M,
        "k": 8,
        "d": 4,
        "fom": 8 * 4 * 4 / (2 * _ELL * _M),
        "score": 8 * 4 * 4 / (2 * _ELL * _M),
        "A_terms": _A,
        "B_terms": _B,
    }
    if geometry is not None:
        row["geometry"] = geometry
    return row


def _milp_key(row: dict) -> tuple:
    return _milp_cache_key(
        row["ell"],
        row["m"],
        row["A_terms"],
        row["B_terms"],
        geometry=row.get("geometry"),
    )


def _q6_threshold_then_timeout_solver(
    checks,
    logicals,
    *,
    max_weight,
    sector,
    partition_index=None,
    anchor_indices=(),
    zero_anchor_indices=(),
    one_anchor_index=None,
    anchor_cube_sha256=None,
    cardinality_encoding="seqcounter",
    solver="cadical195",
    checkpoint_identity=None,
    timeout=1.0,
    hard_timeout_s=None,
    **_kwargs,
):
    """Return matrix-bound test evidence without launching a SAT child."""

    checks = np.asarray(checks, dtype=np.uint8) & 1
    logicals = np.asarray(logicals, dtype=np.uint8) & 1
    binding = distance_sat._instance_binding(
        checks,
        logicals,
        max_weight=int(max_weight),
        sector=str(sector),
        encoding=str(cardinality_encoding),
        solver_name=str(solver),
        checkpoint_identity=checkpoint_identity,
        partition_index=partition_index,
        anchor_indices=tuple(anchor_indices or ()),
        zero_anchor_indices=tuple(zero_anchor_indices or ()),
        one_anchor_index=one_anchor_index,
        anchor_cube_sha256=anchor_cube_sha256,
    )
    wall = float(timeout if hard_timeout_s is None else hard_timeout_s)
    evidence = distance_sat._base_evidence(
        binding=binding,
        hard_timeout_s=wall,
    )
    if int(max_weight) == 18:
        evidence.update({
            "outcome": "unsat",
            "decision_complete": True,
            "threshold_infeasible": True,
            "success": False,
            "retryable": False,
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "elapsed_s": 0.0,
        })
    else:
        evidence.update({
            "outcome": "hard_timeout",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": "synthetic Stage-4 timeout after Stage-3 threshold",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "elapsed_s": 0.0,
        })
    return distance_sat._seal_evidence(evidence)


def test_missing_geometry_and_explicit_q0_preserve_all_legacy_identities():
    legacy = _candidate()
    explicit_zero = _candidate(geometry=_ZERO_GEOMETRY)
    expected_terms_a = ((0, 0), (0, 1), (1, 0))
    expected_terms_b = ((0, 0), (0, 2), (2, 0))
    expected_tuple_key = (6, 6, expected_terms_a, expected_terms_b)

    # The fixed values below were produced by the pre-geometry
    # qcode-low-weight-oracle worktree.  Equality between the two new inputs
    # alone would not catch an accidental migration of every legacy key.
    assert code_key(legacy) == code_key(explicit_zero)
    assert code_key(legacy) == "73d103d281f537e0b47c"
    assert archive_cell(legacy) == archive_cell(explicit_zero)
    assert archive_cell(legacy) == (
        "n=72|rate=2|pattern=5.0|terms=3"
    )
    assert result_code_key(legacy) == result_code_key(explicit_zero)
    assert result_code_key(legacy) == expected_tuple_key
    assert _milp_key(legacy) == _milp_key(explicit_zero)
    assert _milp_key(legacy) == expected_tuple_key
    assert candidate_identity(legacy) == candidate_identity(explicit_zero)
    assert structural_screen_input_sha256(legacy) == (
        structural_screen_input_sha256(explicit_zero)
    )

    expected_translation_report = {
        "method": "bb-torus-translation-row-set-v1",
        "verified": True,
        "shape": [6, 6],
        "block_size": 36,
        "orbit_representatives": [0, 36],
        "orbit_sizes": [36, 36],
        "generators": [
            {
                "axis": "x",
                "order": 6,
                "hx_row_set_preserved": True,
                "hz_row_set_preserved": True,
                "permutation_sha256": (
                    "ea3ef36387707e447991016d06a1c0b212c47eaa57ec6d585e17993777cceab4"
                ),
            },
            {
                "axis": "y",
                "order": 6,
                "hx_row_set_preserved": True,
                "hz_row_set_preserved": True,
                "permutation_sha256": (
                    "ac7256be47857768e173a51ce11fcf0be88c9c0081b3f96f070042448149efc2"
                ),
            },
        ],
    }
    assert verify_bb_translation_symmetry(legacy) == expected_translation_report
    assert (
        verify_bb_translation_symmetry(explicit_zero)
        == expected_translation_report
    )


def test_nonzero_twist_isolated_from_q0_keys_caches_and_archive(tmp_path):
    legacy = _candidate()
    twisted = _candidate(geometry=_TWISTED_GEOMETRY)

    assert code_key(twisted) != code_key(legacy)
    assert result_code_key(twisted) != result_code_key(legacy)
    assert _milp_key(twisted) != _milp_key(legacy)
    assert archive_cell(twisted) != archive_cell(legacy)
    assert candidate_identity(twisted) != candidate_identity(legacy)
    assert structural_screen_input_sha256(twisted) != (
        structural_screen_input_sha256(legacy)
    )

    # Exercise the actual archive map, not only its formatting helper.  The
    # same ell/m/A/B under two quotient geometries must occupy two cells.
    archive = EliteArchive(tmp_path / "elite.json")
    archive.update([legacy, twisted], 1)
    assert len(archive.cells) == 2
    assert {row["candidate_key"] for row in archive.cells.values()} == {
        code_key(legacy),
        code_key(twisted),
    }

    translation = verify_bb_translation_symmetry(twisted)
    assert translation["verified"] is True
    assert translation["method"] == "bb-quotient-translation-row-set-v2"
    assert translation["geometry"] == {
        **_TWISTED_GEOMETRY,
        "ell": 6,
        "m": 6,
    }
    assert translation["relation_basis"] == [[0, 6], [6, 1]]
    assert translation != verify_bb_translation_symmetry(legacy)


def test_archive_uses_bounded_twist_classes_instead_of_one_cell_per_q():
    primitive_q1 = _candidate(geometry=_TWISTED_GEOMETRY)
    primitive_q5 = _candidate(geometry={
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 5,
    })
    composite_q2 = _candidate(geometry={
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 2,
    })
    composite_q3 = _candidate(geometry={
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 3,
    })

    assert archive_cell(primitive_q1) == archive_cell(primitive_q5)
    assert archive_cell(composite_q2) == archive_cell(composite_q3)
    assert archive_cell(primitive_q1) != archive_cell(composite_q2)
    assert "geometry_twist_class=1" in archive_cell(primitive_q1)
    assert "geometry_twist_class=2" in archive_cell(composite_q2)


def test_reviewer_and_history_snapshot_retain_canonical_twist_geometry():
    twisted = _candidate(geometry=_TWISTED_GEOMETRY)

    advisory = _upper_bound_neutral_advisory(twisted)
    _key, _digest, snapshot = _candidate_snapshot(twisted)

    assert advisory["geometry"] == _TWISTED_GEOMETRY
    assert snapshot["geometry"] == _TWISTED_GEOMETRY


def test_persisted_q0_milp_cache_cannot_serve_nonzero_twist(tmp_path):
    legacy = _candidate()
    explicit_zero = _candidate(geometry=_ZERO_GEOMETRY)
    twisted = _candidate(geometry=_TWISTED_GEOMETRY)
    quick = evaluate_candidate_milp(
        _ELL,
        _M,
        _A,
        _B,
        quick=True,
    )
    cutoff = int(quick["d_symplectic"])
    result = evaluate_candidate_milp(
        _ELL,
        _M,
        _A,
        _B,
        milp_early_stop=cutoff,
    )
    assert result["stage"] == "symplectic_low_d"
    parameters = _milp_cache_run_parameters(
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_early_stop=cutoff,
    )
    record = _milp_cache_record(
        result,
        run_parameters=parameters,
        saved_at=123.0,
    )
    cache_path = tmp_path / "milp.jsonl"
    cache_path.write_text(json.dumps(record, sort_keys=True) + "\n")

    zero_key = _milp_key(explicit_zero)
    zero_cache = _load_milp_cache(
        str(cache_path),
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_early_stop=cutoff,
        requested_keys={zero_key},
    )
    assert zero_key == _milp_key(legacy)
    assert zero_key in zero_cache

    twist_key = _milp_key(twisted)
    twist_cache = _load_milp_cache(
        str(cache_path),
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_early_stop=cutoff,
        requested_keys={twist_key},
    )
    assert twist_key != zero_key
    assert twist_cache == {}


def _known_answer_artifact() -> dict:
    rows = []
    for label, n, k, distance in (
        ("[[72,12,6]]", 72, 12, 6),
        ("[[90,8,10]]", 90, 8, 10),
        ("[[144,12,12]]", 144, 12, 12),
    ):
        total = 2 * k
        rows.append({
            "label": label,
            "status": "passed",
            "observed": {"n": n, "k": k, "d": distance},
            "checks": {"valid": True, "distance": True},
            "milp": {
                "exact": True,
                "total_logicals": total,
                "num_logicals_checked": total,
                "logicals_optimal": total,
                "logicals_incumbent": 0,
            },
        })
    return {
        "schema_version": 1,
        "gate": "qldpc-known-answer-baselines",
        "passed": True,
        "summary": {"passed": 3, "total": 3},
        "baselines": rows,
    }


def test_q6_lightweight_evaluator_to_final_gate_rebuild(tmp_path):
    geometry = {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 6,
    }
    a_terms = [(1, 0), (2, 0), (0, 3)]
    b_terms = [(0, 1), (0, 2), (3, 0)]

    evaluated = evaluate_candidate_milp(
        6,
        30,
        a_terms,
        b_terms,
        geometry=geometry,
        quick=True,
    )
    assert evaluated["stage"] == "quick_k_only"
    assert (evaluated["n"], evaluated["k"]) == (360, 12)
    assert evaluated["geometry"] == geometry

    screened = annotate_css_result(evaluated)
    assert screened["static_eligibility"]["eligible"] is True
    assert screened["structural_novelty"]["novel"] is False
    assert screened["structural_novelty"]["matched_reference"] == (
        "Bravyi [[360,12,<=24]]"
    )

    translation = verify_bb_translation_symmetry(screened)
    assert translation["verified"] is True
    assert translation["relation_basis"] == [[0, 30], [6, 6]]
    assert [item["order"] for item in translation["generators"]] == [30, 30]

    known_answer_path = tmp_path / "known_answers.json"
    known_answer_path.write_text(json.dumps(_known_answer_artifact()))
    final = evaluate_final_gate(
        screened,
        known_answer_artifact=known_answer_path,
    )

    assert final["checks"]["candidate_rebuild"] is True
    assert final["checks"]["css_commutation"] is True
    assert final["checks"]["reported_n_matches"] is True
    assert final["checks"]["reported_k_matches"] is True
    assert final["candidate"]["n"] == 360
    assert final["candidate"]["k"] == 12
    assert final["candidate"]["geometry"] == geometry
    # This fixture is a known Bravyi re-encoding, so a sound end-to-end gate
    # must rebuild it successfully and then reject it as non-novel.
    assert final["accepted"] is False
    assert final["checks"]["structural_audit_reproduced"] is False


def test_q6_stage2_rank_to_stage3_handoff_and_stage4_matrix_replay(
    tmp_path,
    monkeypatch,
):
    geometry = {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 6,
    }
    a_terms = [[1, 0], [2, 0], [0, 3]]
    b_terms = [[0, 1], [0, 2], [3, 0]]
    stage1_path = tmp_path / "stage1.jsonl"
    stage1_path.write_text(json.dumps({
        "ell": 6,
        "m": 30,
        "A_terms": a_terms,
        "B_terms": b_terms,
        "geometry": geometry,
        # Stage 2 must ignore these forged derived values and rebuild them
        # under the quotient geometry.
        "n": 2,
        "k": 1,
    }) + "\n")

    ranked, counts = rank_candidate_files([stage1_path])
    assert counts["eligible_candidates"] == 1
    assert len(ranked) == 1
    stage2 = ranked[0]
    assert (stage2["n"], stage2["k"], stage2["required_distance"]) == (
        360,
        12,
        19,
    )
    assert stage2["geometry"] == geometry
    assert stage2["authoritative_geometry"]["geometry"] == {
        **geometry,
        "ell": 6,
        "m": 30,
    }

    candidate = _construction_candidate(stage2, "6" * 64)
    assert candidate["geometry"] == geometry
    monkeypatch.setattr(
        sat_screen,
        "solve_css_sector_sat",
        _q6_threshold_then_timeout_solver,
    )
    artifact = sat_screen.screen_sat_candidate(
        candidate,
        output=tmp_path / "stage3.json",
        timeout=1,
        workers=1,
        coverage_mode="global",
        resume=False,
    )
    assert artifact["status"] == "THRESHOLD_PROVEN"
    assert artifact["candidate"]["geometry"] == geometry
    assert artifact["lower_bound_threshold"] == 18

    handed_off = sector_certificate.claim_from_sector_sat_artifact(artifact)
    assert handed_off["geometry"] == geometry
    assert handed_off[sector_certificate.REQUEST_FIELD][
        "stage3_status"
    ] == "THRESHOLD_PROVEN"

    known_answer_path = tmp_path / "known_answers.json"
    known_answer_path.write_text(json.dumps(_known_answer_artifact()))
    certificate = sector_certificate.build_sector_sat_certificate(
        handed_off,
        known_answer_artifact=known_answer_path,
        timeout_per_logical=1,
        total_timeout=30,
        solver_workers=1,
        sector_solver=_q6_threshold_then_timeout_solver,
    )
    assert certificate["claim"]["geometry"] == geometry
    assert certificate["sector_exact"]["lower_resumed_from_stage3"] is True

    twisted_code = build_bb_code(
        6,
        30,
        a_terms,
        b_terms,
        geometry=geometry,
    )
    twisted_hx, twisted_hz, _, _ = get_code_matrices(twisted_code)
    expected_hashes = {
        "hx": _matrix_sha256(twisted_hx),
        "hz": _matrix_sha256(twisted_hz),
    }
    rectangular_code = build_bb_code(6, 30, a_terms, b_terms)
    rectangular_hx, rectangular_hz, _, _ = get_code_matrices(
        rectangular_code,
    )
    rectangular_hashes = {
        "hx": _matrix_sha256(rectangular_hx),
        "hz": _matrix_sha256(rectangular_hz),
    }
    assert expected_hashes != rectangular_hashes
    assert certificate["matrix_sha256"] == expected_hashes
