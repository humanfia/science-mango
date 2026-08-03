from __future__ import annotations

import time
from copy import deepcopy
from types import SimpleNamespace

import numpy as np

import evaluation.final_gate as final_gate
import evaluation.sector_certificate as sector_certificate
import humanize.pipeline as humanize_pipeline
import humanize.release_export as release_export
import scripts.screen_frontier_sat as sat_screen
import scripts.screen_frontier_xor as xor_screen
from evaluation.certificate import pack_vector
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
)
from evaluation.sector_certificate import (
    REQUEST_FIELD,
    build_sector_sat_certificate,
    claim_from_sector_sat_artifact,
    verify_sector_sat_certificate,
)


def _toy_problem():
    hx = np.asarray([[1, 1, 0, 0], [0, 0, 1, 1]], dtype=np.uint8)
    hz = np.asarray([[1, 1, 1, 1]], dtype=np.uint8)
    lx = np.asarray([[1, 0, 1, 0]], dtype=np.uint8)
    lz = np.asarray([[1, 1, 0, 0]], dtype=np.uint8)
    return SimpleNamespace(num_qudits=4, dimension=1), hx, hz, lx, lz


def _solver_evidence(
    checks,
    logicals,
    *,
    max_weight,
    sector,
    partition_index,
    anchors,
    cube=None,
):
    checks = np.asarray(checks, dtype=np.uint8)
    logicals = np.asarray(logicals, dtype=np.uint8)
    backend = {
        "distribution": "python-sat",
        "version": "test",
        "solver": "test-solver",
    }
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
        "partition_index": partition_index,
        "anchor_indices": list(anchors),
    }
    zero, one, cube_sha = [], None, None
    cnf = None
    if cube is not None:
        zero = list(cube["zero_anchor_indices"])
        one = int(cube["one_anchor_index"])
        cube_sha = cube["cube_sha256"]
        clauses = [[-(index + 1)] for index in zero] + [[one + 1]]
        clauses_sha = sector_certificate._canonical_sha256(clauses)
        instance.update({
            "anchor_constraint_formulation": (
                "anchor-or-first-nonzero-unit-clauses-v1"
            ),
            "zero_anchor_indices": zero,
            "one_anchor_index": one,
            "anchor_cube_sha256": cube_sha,
            "anchor_unit_clauses": clauses,
            "anchor_unit_clauses_sha256": clauses_sha,
        })
        cnf = {"anchor_unit_clauses_sha256": clauses_sha}
    else:
        instance.update({
            "zero_anchor_indices": [],
            "one_anchor_index": None,
            "anchor_cube_sha256": None,
        })
    instance["binding_sha256"] = sector_certificate._canonical_sha256(instance)
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": SAT_FORMULATION,
        "sector": sector,
        "max_weight": max_weight,
        "partition_index": partition_index,
        "anchor_indices": list(anchors),
        "zero_anchor_indices": zero,
        "one_anchor_index": one,
        "anchor_cube_sha256": cube_sha,
        "backend": backend,
        "cardinality_encoding": "seqcounter",
        "instance": instance,
        "decision_complete": True,
    }
    if cnf is not None:
        evidence["cnf"] = cnf
    if max_weight == 1:
        evidence.update({
            "outcome": "unsat",
            "threshold_infeasible": True,
            "success": False,
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    else:
        vector = np.asarray(
            [1, 0, 1, 0] if sector == "X" else [1, 1, 0, 0],
            dtype=np.uint8,
        )
        evidence.update({
            "outcome": "sat",
            "threshold_infeasible": False,
            "success": True,
            "operator": pack_vector(vector),
            "objective": int(vector.sum()),
            "logical_syndrome": ((logicals @ vector) & 1).astype(int).tolist(),
        })
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def test_real_stage3_anchor_cube_artifact_reaches_strict_release_contract(
    tmp_path,
    monkeypatch,
):
    problem = _toy_problem()
    _, hx, hz, lx, lz = problem
    symmetry = {
        "verified": True,
        "orbit_representatives": [0, 2],
        "report_sha256": "a" * 64,
    }
    monkeypatch.setattr(sector_certificate, "_matrices", lambda _claim: problem)
    monkeypatch.setattr(sector_certificate, "minimum_winning_distance", lambda n, k: 2)
    monkeypatch.setattr(final_gate, "minimum_winning_distance", lambda n, k: 2)
    monkeypatch.setattr(
        sector_certificate,
        "check_code_novelty",
        lambda *_args, **_kwargs: {"checked": True, "novel": True},
    )
    monkeypatch.setattr(
        sector_certificate,
        "evaluate_challenge_gate",
        lambda *_args, **_kwargs: {
            "accepted": True,
            "checks": {"typed_exact_sector_sat_proof": True},
            "failures": [],
        },
    )
    monkeypatch.setattr(
        xor_screen,
        "verify_bb_translation_symmetry",
        lambda _claim: deepcopy(symmetry),
    )

    anchors = (0, 2)
    cubes = sat_screen.build_anchor_cover_cubes(anchors)
    detector = sat_screen.verify_css_logical_detectors(hx, hz, lx, lz)
    candidate = {
        "ell": 1,
        "m": 2,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 4,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "anchor-cube-e2e",
    }
    units = {}
    for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx)):
        for cube in cubes:
            key = sat_screen._unit_key("lower", sector, 0, cube)
            units[key] = {
                "unit_id": key,
                "phase": "lower",
                "sector": sector,
                "partition_index": 0,
                "anchor_cube": deepcopy(cube),
                "solver_evidence": _solver_evidence(
                    checks,
                    logicals,
                    max_weight=1,
                    sector=sector,
                    partition_index=0,
                    anchors=anchors,
                    cube=cube,
                ),
                "attempts": [],
            }
    upper_key = sat_screen._unit_key("upper", "X", None)
    units[upper_key] = {
        "unit_id": upper_key,
        "phase": "upper",
        "sector": "X",
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": _solver_evidence(
            hz,
            lz,
            max_weight=2,
            sector="X",
            partition_index=None,
            anchors=anchors,
        ),
        "attempts": [],
    }
    expected_units = len(sat_screen._proof_plan(
        "first-nonzero", 1, ("X", "Z"), cubes,
    ))
    artifact = sat_screen._artifact(
        candidate,
        mode="first-nonzero",
        translation_symmetry=symmetry,
        logical_detector=detector,
        units=units,
        expected_units=expected_units,
        started=time.monotonic(),
        proof_sectors=("X", "Z"),
        anchor_cover_cubes=cubes,
    )
    assert artifact["status"] == "EXACT_PROVEN"
    assert artifact["artifact_sha256"] == sector_certificate._canonical_sha256(
        artifact, omit="artifact_sha256",
    )
    assert artifact["expected_lower_decisions"] == 4
    assert artifact["expected_lower_partitions"] == 2

    claim = claim_from_sector_sat_artifact(artifact)
    assert claim[REQUEST_FIELD]["anchor_cover_cubes"] == cubes

    def fast_solver(
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
        **_kwargs,
    ):
        cube = None
        if anchor_cube_sha256 is not None:
            cube = next(
                item
                for item in sat_screen.build_anchor_cover_cubes(
                    tuple(anchor_indices),
                )
                if item["cube_sha256"] == anchor_cube_sha256
            )
            assert cube["zero_anchor_indices"] == list(zero_anchor_indices)
            assert cube["one_anchor_index"] == one_anchor_index
        return _solver_evidence(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
            partition_index=partition_index,
            anchors=tuple(anchor_indices),
            cube=cube,
        )

    known = tmp_path / "known.json"
    known.write_text("{}\n", encoding="utf-8")
    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=4,
        sector_solver=fast_solver,
    )
    assert certificate["passed"] is True
    assert certificate["sector_exact"]["lower_resumed_from_stage3"] is True
    assert certificate["sector_exact"]["upper_resumed_from_stage3"] is True

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=4,
        sector_solver=fast_solver,
    )
    assert replay["passed"] is True
    assert replay["sector_decisions_verified"] == 4
    assert replay["logical_partitions_verified"] == 2
    assert replay["checks"]["anchor_cover_cubes"] is True

    assert humanize_pipeline._sector_sat_expected_lower_decisions(
        certificate,
        replay_checks=replay["checks"],
        replay_result=replay,
    ) == 4
    assert release_export._sector_sat_expected_lower_decisions(certificate) == 4
    required, valid = release_export._strict_replay_contract(
        certificate,
        replay,
        k=1,
    )
    assert required <= replay["checks"].keys()
    assert valid is True
