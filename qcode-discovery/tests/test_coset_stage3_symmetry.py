"""Focused Stage-3 coverage tests for compact coset constructions."""

from __future__ import annotations

import time
from copy import deepcopy

import numpy as np
import pytest

import evaluation.construction as construction_adapter
import evaluation.sector_certificate as sector_certificate
from evaluation.coset_action_catalog import list_action_descriptors
from evaluation.coset_two_block import build_coset_two_block
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
)
from evaluation.final_gate import minimum_winning_distance
from evaluation.sector_certificate import (
    REQUEST_FIELD,
    claim_from_sector_sat_artifact,
)
from scripts.audit_direction_pool import expected_proof_units
from scripts.screen_frontier_sat import (
    _artifact,
    _proof_plan,
    _unit_key,
    build_anchor_cover_cubes,
    verify_construction_symmetry,
    verify_css_logical_detectors,
)


PAPER_ACTION_ID = "coset2bga-l224-m53-s1-degree112-v1"


@pytest.fixture(scope="module")
def published_stage3_problem():
    descriptor = next(
        item
        for item in list_action_descriptors()
        if item["action_id"] == PAPER_ACTION_ID
    )
    code = build_coset_two_block(
        PAPER_ACTION_ID,
        descriptor["published_left_support"],
        descriptor["published_right_support"],
    )
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    candidate = {
        "source": "published-coset2bga-224-12-16",
        "construction": dict(code.construction),
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "required_distance": minimum_winning_distance(
            int(code.num_qudits), int(code.dimension),
        ),
        "canonical_digest": (
            "0305b690d57d72928d0b2770ce4389162d114fe189b58731f"
            "335ae1e229870ff"
        ),
    }
    return candidate, hx, hz, lx, lz


def _unsat_evidence(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    sector: str,
    max_weight: int,
    anchors: tuple[int, ...] = (),
    cube: dict | None = None,
) -> dict:
    backend = {
        "distribution": "python-sat",
        "version": "test",
        "solver": "test-solver",
    }
    zero_anchors: list[int] = []
    one_anchor: int | None = None
    cube_sha256: str | None = None
    instance = {
        "formulation": SAT_FORMULATION,
        "sector": sector,
        "max_weight": max_weight,
        "backend": deepcopy(backend),
        "cardinality_encoding": "seqcounter",
        "check_matrix_sha256": sector_certificate._array_sha256(
            "checks", checks,
        ),
        "target_logicals_sha256": sector_certificate._array_sha256(
            "logicals", logicals,
        ),
        "partition_index": None,
        "anchor_indices": list(anchors),
    }
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": SAT_FORMULATION,
        "sector": sector,
        "max_weight": max_weight,
        "partition_index": None,
        "anchor_indices": list(anchors),
        "backend": backend,
        "cardinality_encoding": "seqcounter",
        "decision_complete": True,
        "outcome": "unsat",
        "threshold_infeasible": True,
        "success": False,
        "operator": None,
        "objective": None,
        "logical_syndrome": None,
    }
    if cube is not None:
        zero_anchors = list(cube["zero_anchor_indices"])
        one_anchor = int(cube["one_anchor_index"])
        cube_sha256 = str(cube["cube_sha256"])
        clauses = [
            *([[-(index + 1)] for index in zero_anchors]),
            [one_anchor + 1],
        ]
        clauses_sha256 = sector_certificate._canonical_sha256(clauses)
        instance.update({
            "anchor_constraint_formulation": (
                "anchor-or-first-nonzero-unit-clauses-v1"
            ),
            "zero_anchor_indices": zero_anchors,
            "one_anchor_index": one_anchor,
            "anchor_cube_sha256": cube_sha256,
            "anchor_unit_clauses": clauses,
            "anchor_unit_clauses_sha256": clauses_sha256,
        })
        evidence["cnf"] = {
            "anchor_unit_clauses_sha256": clauses_sha256,
        }
    else:
        instance.update({
            "zero_anchor_indices": [],
            "one_anchor_index": None,
            "anchor_cube_sha256": None,
        })
    evidence.update({
        "zero_anchor_indices": zero_anchors,
        "one_anchor_index": one_anchor,
        "anchor_cube_sha256": cube_sha256,
    })
    instance["binding_sha256"] = sector_certificate._canonical_sha256(instance)
    evidence["instance"] = instance
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def _lower_unit(
    *,
    phase: str,
    sector: str,
    evidence: dict,
    cube: dict | None,
) -> dict:
    return {
        "unit_id": _unit_key(phase, sector, None, cube),
        "phase": phase,
        "sector": sector,
        "partition_index": None,
        "anchor_cube": None if cube is None else deepcopy(cube),
        "solver_evidence": evidence,
        "attempts": [],
    }


def test_published_fixture_has_eight_verified_orbits_and_twenty_units(
    published_stage3_problem,
):
    candidate, hx, hz, _lx, _lz = published_stage3_problem
    symmetry = verify_construction_symmetry(candidate, hx, hz)

    assert symmetry["verified"] is True
    assert symmetry["orbits_cover_all_qubits"] is True
    assert len(symmetry["orbits"]) == 8
    assert [len(orbit) for orbit in symmetry["orbits"]] == [28] * 8
    assert len(symmetry["orbit_representatives"]) == 8
    assert sorted(
        qubit for orbit in symmetry["orbits"] for qubit in orbit
    ) == list(range(224))

    cubes = build_anchor_cover_cubes(
        tuple(symmetry["orbit_representatives"]),
    )
    plan = _proof_plan("global", 12, ("X", "Z"), cubes)
    assert len(cubes) == 8
    assert len(plan) == 20
    assert sum(phase == "lower" for phase, *_rest in plan) == 16
    assert sum(phase == "lower-global" for phase, *_rest in plan) == 2
    assert sum(phase == "upper" for phase, *_rest in plan) == 2
    assert expected_proof_units(candidate, "sat-sectors") == 20


def test_tampered_symmetry_proposals_fall_back_to_four_global_units(
    published_stage3_problem,
    monkeypatch,
):
    candidate, hx, hz, _lx, _lz = published_stage3_problem
    proposals = deepcopy(
        construction_adapter.candidate_symmetry_generators(candidate),
    )
    for proposal in proposals:
        # Keep the qubit action intact but make every proposed row relabeling
        # non-bijective.  Matrix replay must reject rather than trust metadata.
        proposal["x_check_permutation"][0] = proposal[
            "x_check_permutation"
        ][1]
    monkeypatch.setattr(
        construction_adapter,
        "candidate_symmetry_generators",
        lambda _claim: deepcopy(proposals),
    )

    symmetry = verify_construction_symmetry(candidate, hx, hz)
    assert symmetry["verified"] is False
    assert symmetry["verified_generators"] == []
    assert len(symmetry["rejected_generators"]) == len(proposals)
    assert expected_proof_units(candidate, "sat-sectors") == 4
    assert len(_proof_plan("global", 12, ("X", "Z"), None)) == 4


def test_compact_stage3_handoff_accepts_anchor_cover_and_global_lane(
    published_stage3_problem,
):
    candidate, hx, hz, lx, lz = published_stage3_problem
    required = candidate["required_distance"]
    symmetry = verify_construction_symmetry(candidate, hx, hz)
    anchors = tuple(symmetry["orbit_representatives"])
    cubes = build_anchor_cover_cubes(anchors)
    detector = verify_css_logical_detectors(hx, hz, lx, lz)

    anchored_units = {}
    for sector in ("X", "Z"):
        checks, logicals = sector_certificate._sector_matrices(
            sector, hx, hz, lx, lz,
        )
        for cube in cubes:
            unit = _lower_unit(
                phase="lower",
                sector=sector,
                cube=cube,
                evidence=_unsat_evidence(
                    checks,
                    logicals,
                    sector=sector,
                    max_weight=required - 1,
                    anchors=anchors,
                    cube=cube,
                ),
            )
            anchored_units[unit["unit_id"]] = unit
    anchored_artifact = _artifact(
        candidate,
        mode="global",
        translation_symmetry=None,
        construction_symmetry=symmetry,
        logical_detector=detector,
        units=anchored_units,
        expected_units=20,
        started=time.monotonic(),
        proof_sectors=("X", "Z"),
        anchor_cover_cubes=cubes,
    )
    assert anchored_artifact["status"] == "THRESHOLD_PROVEN"
    assert anchored_artifact["expected_lower_decisions"] == 16
    anchored_claim = claim_from_sector_sat_artifact(anchored_artifact)
    anchored_request = anchored_claim[REQUEST_FIELD]
    assert anchored_request["use_construction_anchors"] is True
    assert anchored_request["use_translation_anchors"] is False
    assert anchored_request["construction_symmetry"] == symmetry
    assert anchored_request["translation_symmetry"] is None
    assert anchored_request["anchor_cover_cubes"] == cubes
    assert len(anchored_request["lower_bound_decisions"]) == 16

    # The redundant global-lower lane is independently complete and stronger
    # than the anchored cover.  Its handoff must discard unused anchors rather
    # than falsely claiming that the global decisions depended on symmetry.
    global_units = {}
    for sector in ("X", "Z"):
        checks, logicals = sector_certificate._sector_matrices(
            sector, hx, hz, lx, lz,
        )
        unit = _lower_unit(
            phase="lower-global",
            sector=sector,
            cube=None,
            evidence=_unsat_evidence(
                checks,
                logicals,
                sector=sector,
                max_weight=required - 1,
            ),
        )
        global_units[unit["unit_id"]] = unit
    global_artifact = _artifact(
        candidate,
        mode="global",
        translation_symmetry=None,
        construction_symmetry=symmetry,
        logical_detector=detector,
        units=global_units,
        expected_units=20,
        started=time.monotonic(),
        proof_sectors=("X", "Z"),
        anchor_cover_cubes=cubes,
    )
    assert global_artifact["status"] == "THRESHOLD_PROVEN"
    assert global_artifact["coverage_mode"] == "global"
    assert global_artifact["anchor_cover_cubes"] is None
    assert global_artifact["expected_lower_decisions"] == 2
    global_claim = claim_from_sector_sat_artifact(global_artifact)
    global_request = global_claim[REQUEST_FIELD]
    assert global_request["use_construction_anchors"] is False
    assert global_request["construction_symmetry"] is None
    assert global_request["anchor_cover_cubes"] is None
    assert len(global_request["lower_bound_decisions"]) == 2
