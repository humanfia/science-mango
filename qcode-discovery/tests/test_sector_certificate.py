from __future__ import annotations

import threading
import time
from copy import deepcopy
from types import SimpleNamespace

import numpy as np

import evaluation.final_gate as final_gate
import evaluation.sector_certificate as sector_certificate
from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.final_gate import _typed_exact_sector_check
from evaluation.certificate import pack_vector
from evaluation.certificate_dispatch import builder_for_claim, verifier_for_certificate
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
    solve_css_sector_sat,
)
from evaluation.sector_certificate import (
    CERTIFICATE_TYPE,
    REQUEST_FIELD,
    STAGE3_GATE,
    build_sector_sat_certificate,
    claim_from_sector_sat_artifact,
    verify_sector_sat_certificate,
)
from evaluation.target_policy import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    target_binding,
)
from scripts.screen_frontier_sat import (
    build_anchor_cover_cubes,
    verify_css_logical_detectors,
)


def _problem():
    hx = np.asarray([[1, 1, 0, 0], [0, 0, 1, 1]], dtype=np.uint8)
    hz = np.asarray([[1, 1, 1, 1]], dtype=np.uint8)
    lx = np.asarray([[1, 0, 1, 0]], dtype=np.uint8)
    lz = np.asarray([[1, 1, 0, 0]], dtype=np.uint8)
    code = SimpleNamespace(num_qudits=4, dimension=1)
    return code, hx, hz, lx, lz


def _fake_solver(
    checks,
    logicals,
    *,
    max_weight,
    sector,
    partition_index=None,
    anchor_indices=(),
    **_,
):
    checks = np.asarray(checks, dtype=np.uint8)
    logicals = np.asarray(logicals, dtype=np.uint8)
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": SAT_FORMULATION,
        "sector": sector,
        "max_weight": max_weight,
        "partition_index": partition_index,
        "anchor_indices": list(anchor_indices),
        "backend": {
            "distribution": "python-sat",
            "version": "test",
            "solver": "test-solver",
        },
        "instance": {
            "check_matrix_sha256": sector_certificate._array_sha256(
                "checks", checks,
            ),
            "target_logicals_sha256": sector_certificate._array_sha256(
                "logicals", logicals,
            ),
            "partition_index": partition_index,
            "anchor_indices": list(anchor_indices),
        },
        "decision_complete": True,
    }
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
            [1, 1, 0, 0] if sector == "Z" else [1, 0, 1, 0],
            dtype=np.uint8,
        )
        evidence.update({
            "outcome": "sat",
            "threshold_infeasible": False,
            "success": True,
            "operator": pack_vector(vector),
            "objective": 2,
            "logical_syndrome": ((logicals @ vector) & 1).astype(int).tolist(),
        })
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def _cube_fake_solver(
    checks,
    logicals,
    *,
    zero_anchor_indices=(),
    one_anchor_index=None,
    anchor_cube_sha256=None,
    **kwargs,
):
    evidence = _fake_solver(checks, logicals, **kwargs)
    zero_indices = [int(index) for index in zero_anchor_indices]
    evidence["zero_anchor_indices"] = zero_indices
    evidence["one_anchor_index"] = one_anchor_index
    evidence["anchor_cube_sha256"] = anchor_cube_sha256
    instance = evidence["instance"]
    if anchor_cube_sha256 is not None:
        unit_clauses = [
            *([[-(index + 1)] for index in zero_indices]),
            [int(one_anchor_index) + 1],
        ]
        instance.update({
            "anchor_constraint_formulation": (
                "anchor-or-first-nonzero-unit-clauses-v1"
            ),
            "zero_anchor_indices": zero_indices,
            "one_anchor_index": int(one_anchor_index),
            "anchor_cube_sha256": anchor_cube_sha256,
            "anchor_unit_clauses": unit_clauses,
            "anchor_unit_clauses_sha256": (
                sector_certificate._canonical_sha256(unit_clauses)
            ),
        })
        instance["binding_sha256"] = sector_certificate._canonical_sha256(
            instance,
        )
        evidence["cnf"] = {
            "anchor_unit_clauses_sha256": (
                sector_certificate._canonical_sha256(unit_clauses)
            ),
        }
    evidence.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(
        evidence,
    )
    return evidence


def _reseal_sector_certificate(certificate):
    proof = certificate["claim"]["exact_distance_proof"]
    proof.pop("proof_sha256", None)
    proof["proof_sha256"] = sector_certificate._canonical_sha256(proof)
    certificate["sector_exact"]["proof"] = deepcopy(proof)
    certificate["certificate_sha256"] = sector_certificate._certificate_sha256(
        certificate,
    )


def _retryable_timeout(evidence):
    evidence = deepcopy(evidence)
    evidence.update({
        "outcome": "hard_timeout",
        "decision_complete": False,
        "threshold_infeasible": False,
        "success": False,
        "retryable": True,
        "message": "test timeout",
        "operator": None,
        "objective": None,
        "logical_syndrome": None,
    })
    evidence.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def _trusted_replay_config(evidence, *, solver, encoding):
    evidence = deepcopy(evidence)
    backend = {
        **evidence["backend"],
        "solver": solver,
    }
    evidence["backend"] = backend
    evidence["cardinality_encoding"] = encoding
    instance = evidence["instance"]
    instance.update({
        "formulation": evidence["formulation"],
        "sector": evidence["sector"],
        "max_weight": evidence["max_weight"],
        "backend": dict(backend),
        "cardinality_encoding": encoding,
    })
    instance.pop("binding_sha256", None)
    instance["binding_sha256"] = sector_certificate._canonical_sha256(instance)
    evidence.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def _patch_problem(monkeypatch):
    problem = _problem()
    monkeypatch.setattr(sector_certificate, "_matrices", lambda _claim: problem)
    monkeypatch.setattr(
        sector_certificate,
        "minimum_winning_distance",
        lambda n, k: 2,
    )
    monkeypatch.setattr(
        final_gate,
        "minimum_winning_distance",
        lambda n, k: 2,
    )
    monkeypatch.setattr(
        sector_certificate,
        "check_code_novelty",
        lambda *_args, **_kwargs: {
            "checked": True,
            "novel": True,
            "canonical_digest": "digest",
            "registry_sha256": "registry",
        },
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


def _claim():
    return {
        "ell": 1,
        "m": 2,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 4,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "digest",
        REQUEST_FIELD: {"coverage_mode": "global"},
    }


def _steane_problem():
    checks = np.asarray([
        [1, 1, 1, 1, 0, 0, 0],
        [1, 1, 0, 0, 1, 1, 0],
        [1, 0, 1, 0, 1, 0, 1],
    ], dtype=np.uint8)
    logical = np.ones((1, 7), dtype=np.uint8)
    return SimpleNamespace(num_qudits=7, dimension=1), checks, checks, logical, logical


def _isometric_problem():
    hx = np.asarray([[1, 1, 0, 0]], dtype=np.uint8)
    hz = np.asarray([[0, 0, 1, 1]], dtype=np.uint8)
    lx = np.asarray([
        [1, 0, 0, 0],
        [0, 0, 1, 1],
    ], dtype=np.uint8)
    lz = np.asarray([
        [1, 1, 0, 0],
        [0, 0, 1, 0],
    ], dtype=np.uint8)
    code = SimpleNamespace(num_qudits=4, dimension=2)
    return code, hx, hz, lx, lz


def _isometric_claim():
    return {
        "ell": 1,
        "m": 2,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 4,
        "k": 2,
        "required_distance": 2,
        "canonical_digest": "isometric-digest",
        REQUEST_FIELD: {"coverage_mode": "global"},
    }


def _patch_isometric_problem(monkeypatch):
    _patch_problem(monkeypatch)
    problem = _isometric_problem()
    monkeypatch.setattr(sector_certificate, "_matrices", lambda _claim: problem)


def _isometric_solver(
    checks,
    logicals,
    *,
    max_weight,
    sector,
    **kwargs,
):
    evidence = _fake_solver(
        checks,
        logicals,
        max_weight=max_weight,
        sector=sector,
        **kwargs,
    )
    if max_weight == 1:
        return evidence
    vector = np.asarray(
        [0, 0, 1, 1] if sector == "X" else [1, 1, 0, 0],
        dtype=np.uint8,
    )
    logicals = np.asarray(logicals, dtype=np.uint8)
    evidence.update({
        "outcome": "sat",
        "threshold_infeasible": False,
        "success": True,
        "decision_complete": True,
        "retryable": False,
        "operator": pack_vector(vector),
        "objective": 2,
        "logical_syndrome": ((logicals @ vector) & 1).astype(int).tolist(),
    })
    evidence.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    return evidence


def _patch_steane_problem(monkeypatch):
    problem = _steane_problem()
    monkeypatch.setattr(sector_certificate, "_matrices", lambda _claim: problem)
    monkeypatch.setattr(
        sector_certificate,
        "minimum_winning_distance",
        lambda n, k: 2,
    )
    monkeypatch.setattr(
        final_gate,
        "minimum_winning_distance",
        lambda n, k: 2,
    )
    monkeypatch.setattr(
        sector_certificate,
        "check_code_novelty",
        lambda *_args, **_kwargs: {
            "checked": True,
            "novel": True,
            "canonical_digest": "steane-digest",
            "registry_sha256": "registry",
        },
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


def _steane_claim():
    return {
        "ell": 1,
        "m": 2,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 7,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "steane-digest",
        REQUEST_FIELD: {"coverage_mode": "global"},
    }


def _steane_solver_factory(calls):
    def solve(
        checks,
        logicals,
        *,
        max_weight,
        sector,
        partition_index=None,
        anchor_indices=(),
        checkpoint_path=None,
        resume=False,
        **_,
    ):
        checks = np.asarray(checks, dtype=np.uint8)
        logicals = np.asarray(logicals, dtype=np.uint8)
        calls.append({
            "sector": sector,
            "max_weight": max_weight,
            "checkpoint_path": (
                None if checkpoint_path is None else str(checkpoint_path)
            ),
            "resume": resume,
        })
        evidence = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "formulation": SAT_FORMULATION,
            "sector": sector,
            "max_weight": max_weight,
            "partition_index": partition_index,
            "anchor_indices": list(anchor_indices),
            "backend": {
                "distribution": "python-sat",
                "version": "test",
                "solver": "test-solver",
            },
            "instance": {
                "check_matrix_sha256": sector_certificate._array_sha256(
                    "checks", checks,
                ),
                "target_logicals_sha256": sector_certificate._array_sha256(
                    "logicals", logicals,
                ),
                "partition_index": partition_index,
                "anchor_indices": list(anchor_indices),
            },
            "decision_complete": True,
        }
        if max_weight <= 2:
            evidence.update({
                "outcome": "unsat",
                "threshold_infeasible": True,
                "success": False,
                "operator": None,
                "objective": None,
                "logical_syndrome": None,
            })
        else:
            vector = np.asarray([1, 1, 0, 0, 0, 0, 1], dtype=np.uint8)
            evidence.update({
                "outcome": "sat",
                "threshold_infeasible": False,
                "success": True,
                "operator": pack_vector(vector),
                "objective": 3,
                "logical_syndrome": (
                    (logicals @ vector) & 1
                ).astype(int).tolist(),
            })
        evidence["evidence_sha256"] = sector_certificate._canonical_sha256(
            evidence,
        )
        return evidence

    return solve


def test_sector_certificate_build_and_independent_rerun(tmp_path, monkeypatch):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")

    claim = _claim()
    claim[REQUEST_FIELD]["coverage_mode"] = "first-nonzero"
    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )

    assert certificate["certificate_type"] == CERTIFICATE_TYPE
    assert certificate["passed"] is True
    assert "milp" not in certificate
    assert certificate["sector_exact"]["expected_lower_decisions"] == 2
    assert certificate["claim"]["exact_distance_proof"]["distance"] == 2

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    assert replay["passed"] is True
    assert replay["sector_decisions_verified"] == 2
    assert "direction_count" not in replay["checks"]
    assert replay["checks"]["sat_rerun"] is True


def test_anchor_cube_cover_composes_only_after_every_cube_and_strict_rerun(
    tmp_path,
    monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    anchors = (0, 2)
    symmetry = {
        "verified": True,
        "orbit_representatives": list(anchors),
        "report_sha256": "a" * 64,
    }
    monkeypatch.setattr(
        "scripts.screen_frontier_xor.verify_bb_translation_symmetry",
        lambda _claim: deepcopy(symmetry),
    )
    claim = _claim()
    claim[REQUEST_FIELD].update({
        "coverage_mode": "first-nonzero",
        "use_translation_anchors": True,
        "translation_symmetry": deepcopy(symmetry),
        "anchor_cover_cubes": build_anchor_cover_cubes(anchors),
    })

    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=4,
        sector_solver=_cube_fake_solver,
    )

    proof = certificate["claim"]["exact_distance_proof"]
    assert certificate["passed"] is True
    assert proof["expected_lower_decisions"] == 4
    assert proof["completed_lower_decisions"] == 4
    assert proof["expected_lower_partitions"] == 2
    assert proof["completed_lower_partitions"] == 2
    assert certificate["sector_exact"]["expected_lower_decisions"] == 4
    assert certificate["sector_exact"]["completed_lower_partitions"] == 2
    assert {
        item["anchor_cube"]["cube_index"]
        for item in proof["lower_bound_decisions"]
    } == {0, 1}
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": sector_certificate._clean_claim(claim),
        "required_distance": 2,
        "coverage_mode": "first-nonzero",
        "lower_bound_threshold": 1,
        "anchor_cover_cubes": deepcopy(proof["anchor_cover_cubes"]),
        "expected_lower_decisions": 4,
        "completed_lower_decisions": 4,
        "expected_lower_partitions": 2,
        "completed_lower_partitions": 2,
        "lower_bound_decisions": deepcopy(proof["lower_bound_decisions"]),
        "upper_witness": deepcopy(proof["upper_witness"]),
        "translation_symmetry": deepcopy(symmetry),
        "logical_detector": deepcopy(proof["logical_detector"]),
        "xz_sector_isometry": None,
        "units": [],
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(
        artifact,
    )
    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off[REQUEST_FIELD]["anchor_cover_cubes"] == (
        proof["anchor_cover_cubes"]
    )
    assert len(handed_off[REQUEST_FIELD]["lower_bound_decisions"]) == 4
    _, hx, hz, lx, lz = _problem()
    assert _typed_exact_sector_check(
        certificate["claim"],
        distance=2,
        k=1,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    ) is True

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=4,
        sector_solver=_cube_fake_solver,
    )
    assert replay["passed"] is True
    assert replay["sector_decisions_verified"] == 4
    assert replay["sector_decisions_total"] == 4
    assert replay["logical_partitions_verified"] == 2
    assert replay["logical_partitions_total"] == 2


def test_anchor_cube_cover_missing_duplicate_and_binding_tampering_fail_closed(
    tmp_path,
    monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    anchors = (0, 2)
    symmetry = {
        "verified": True,
        "orbit_representatives": list(anchors),
        "report_sha256": "b" * 64,
    }
    monkeypatch.setattr(
        "scripts.screen_frontier_xor.verify_bb_translation_symmetry",
        lambda _claim: deepcopy(symmetry),
    )
    claim = _claim()
    claim[REQUEST_FIELD].update({
        "coverage_mode": "first-nonzero",
        "use_translation_anchors": True,
        "translation_symmetry": deepcopy(symmetry),
        "anchor_cover_cubes": build_anchor_cover_cubes(anchors),
    })
    original = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_cube_fake_solver,
    )
    _, hx, hz, lx, lz = _problem()

    cases = []
    missing = deepcopy(original)
    missing["claim"]["exact_distance_proof"][
        "lower_bound_decisions"
    ].pop()
    _reseal_sector_certificate(missing)
    cases.append(missing)

    duplicate = deepcopy(original)
    lower = duplicate["claim"]["exact_distance_proof"][
        "lower_bound_decisions"
    ]
    lower[-1] = deepcopy(lower[-2])
    _reseal_sector_certificate(duplicate)
    cases.append(duplicate)

    bad_binding = deepcopy(original)
    evidence = bad_binding["claim"]["exact_distance_proof"][
        "lower_bound_decisions"
    ][0]["solver_evidence"]
    instance = evidence["instance"]
    instance["anchor_unit_clauses"] = [[-4], [1]]
    instance["anchor_unit_clauses_sha256"] = (
        sector_certificate._canonical_sha256(instance["anchor_unit_clauses"])
    )
    instance.pop("binding_sha256", None)
    instance["binding_sha256"] = sector_certificate._canonical_sha256(instance)
    evidence.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = sector_certificate._canonical_sha256(evidence)
    _reseal_sector_certificate(bad_binding)
    cases.append(bad_binding)

    bad_cover = deepcopy(original)
    cover = bad_cover["claim"]["exact_distance_proof"]["anchor_cover_cubes"]
    cover[0]["one_anchor_index"] = 2
    cover[0].pop("cube_sha256", None)
    cover[0]["cube_sha256"] = sector_certificate._canonical_sha256(cover[0])
    _reseal_sector_certificate(bad_cover)
    cases.append(bad_cover)

    for certificate in cases:
        assert _typed_exact_sector_check(
            certificate["claim"],
            distance=2,
            k=1,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
        ) is False
        replay = verify_sector_sat_certificate(
            certificate,
            known_answer_artifact=known,
            timeout_per_logical=1,
            total_timeout=10,
            sector_solver=_cube_fake_solver,
        )
        assert replay["passed"] is False


def test_production_sat_cube_binding_is_accepted_by_certificate_validator():
    _, _, hz, _, lz = _problem()
    anchors = (0, 2)
    cube = build_anchor_cover_cubes(anchors)[1]
    evidence = solve_css_sector_sat(
        hz,
        lz,
        max_weight=1,
        timeout=10,
        sector="X",
        partition_index=0,
        anchor_indices=anchors,
        zero_anchor_indices=tuple(cube["zero_anchor_indices"]),
        one_anchor_index=cube["one_anchor_index"],
        anchor_cube_sha256=cube["cube_sha256"],
        solver="cadical195",
    )
    wrapper = {
        "sector": "X",
        "partition_index": 0,
        "anchor_cube": cube,
        "solver_evidence": evidence,
    }

    assert evidence["outcome"] == "unsat"
    assert sector_certificate._complete_unsat(
        wrapper,
        sector="X",
        max_weight=1,
        checks=hz,
        logicals=lz,
        expected_anchors=anchors,
        expected_anchor_cube=cube,
    ) is True


def test_lower_attempt_continues_after_retryable_solver_exception(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    calls = []

    def flaky_solver(checks, logicals, *, sector, **kwargs):
        calls.append({"sector": sector, "timeout": kwargs["timeout"]})
        if sector == "X":
            raise RuntimeError("transient backend failure")
        return _fake_solver(
            checks,
            logicals,
            sector=sector,
            **kwargs,
        )

    claim = _claim()
    claim[REQUEST_FIELD]["coverage_mode"] = "first-nonzero"
    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=9,
        total_timeout=10,
        sector_solver=flaky_solver,
    )

    assert [item["sector"] for item in calls] == ["X", "Z"]
    assert [item["partition_index"] for item in certificate[
        "sector_exact"
    ]["decision_attempts"]] == [0, 0]
    assert calls[0]["timeout"] <= 5
    assert certificate["passed"] is False
    attempts = certificate["sector_exact"]["decision_attempts"]
    assert [item["outcome"] for item in attempts] == [
        "solver_error",
        "unsat",
    ]
    assert attempts[0]["retryable"] is True
    assert certificate["sector_exact"]["retryable_decisions"] == 1
    assert certificate["sector_exact"]["completed_lower_decisions"] == 1


def test_escalation_timeout_does_not_starve_other_sector_witness(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    claim = _claim()
    _, hx, hz, lx, lz = _problem()
    claim[REQUEST_FIELD]["lower_bound_decisions"] = [
        {
            "sector": sector,
            "partition_index": None,
            "solver_evidence": _fake_solver(
                checks,
                logicals,
                max_weight=1,
                sector=sector,
            ),
        }
        for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx))
    ]
    calls = []

    def flaky_solver(checks, logicals, *, sector, **kwargs):
        calls.append(sector)
        evidence = _fake_solver(
            checks,
            logicals,
            sector=sector,
            **kwargs,
        )
        return _retryable_timeout(evidence) if sector == "X" else evidence

    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=flaky_solver,
    )

    assert calls == ["X", "Z"]
    assert certificate["passed"] is True
    assert certificate["claim"]["d"] == 2
    attempts = certificate["sector_exact"]["decision_attempts"]
    assert [item["outcome"] for item in attempts] == [
        "hard_timeout",
        "sat",
    ]


def test_verification_timeout_does_not_starve_later_sector(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    certificate = build_sector_sat_certificate(
        _claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    calls = []

    def flaky_solver(checks, logicals, *, sector, **kwargs):
        calls.append(sector)
        evidence = _fake_solver(
            checks,
            logicals,
            sector=sector,
            **kwargs,
        )
        return _retryable_timeout(evidence) if sector == "X" else evidence

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=flaky_solver,
    )

    assert calls == ["X", "Z"]
    assert replay["passed"] is False
    assert replay["replay_complete"] is False
    assert replay["sector_decisions_verified"] == 1
    assert [item["outcome"] for item in replay[
        "sector_decision_attempts"
    ]] == ["hard_timeout", "unsat"]


def test_verified_xz_isometry_reduces_build_and_replay_to_canonical_x(
    tmp_path, monkeypatch,
):
    _patch_isometric_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    claim = _isometric_claim()
    _, hx, hz, lx, lz = _isometric_problem()
    report = verify_bb_xz_sector_isometry(hx, hz, ell=1, m=2)
    assert report["verified"] is True
    claim[REQUEST_FIELD]["xz_sector_isometry"] = report
    calls = []

    def recording_solver(checks, logicals, *, sector, max_weight, **kwargs):
        calls.append((sector, max_weight))
        return _isometric_solver(
            checks,
            logicals,
            sector=sector,
            max_weight=max_weight,
            **kwargs,
        )

    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=recording_solver,
    )

    assert certificate["passed"] is True
    assert calls == [("X", 1), ("X", 2)]
    assert certificate["xz_sector_isometry"] == report
    assert certificate["sector_exact"]["xz_sector_isometry"] == report
    assert certificate["sector_exact"]["expected_lower_decisions"] == 1
    proof = certificate["claim"]["exact_distance_proof"]
    assert proof["xz_sector_isometry"] == report
    assert {
        item["sector"] for item in proof["lower_bound_decisions"]
    } == {"X"}
    assert _typed_exact_sector_check(
        certificate["claim"],
        distance=2,
        k=1,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    ) is True

    calls.clear()
    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=recording_solver,
    )
    assert replay["passed"] is True
    assert calls == [("X", 1)]
    assert replay["sector_decisions_total"] == 1
    assert replay["checks"]["xz_sector_isometry"] is True


def test_stage3_handoff_replays_xz_isometry_and_rejects_tampering(
    monkeypatch,
):
    _patch_isometric_problem(monkeypatch)
    claim = _isometric_claim()
    _, hx, hz, lx, lz = _isometric_problem()
    report = verify_bb_xz_sector_isometry(hx, hz, ell=1, m=2)
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    lower = [{
        "sector": "X",
        "partition_index": None,
        "solver_evidence": _isometric_solver(
            hz,
            lz,
            max_weight=1,
            sector="X",
        ),
    }]
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": {
            key: value for key, value in claim.items() if key != REQUEST_FIELD
        },
        "required_distance": 2,
        "coverage_mode": "global",
        "translation_symmetry": None,
        "logical_detector": detector,
        "xz_sector_isometry": report,
        "lower_bound_decisions": lower,
        "upper_witness": {
            "sector": "X",
            "partition_index": None,
            "solver_evidence": _isometric_solver(
                hz,
                lz,
                max_weight=2,
                sector="X",
            ),
        },
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(
        artifact,
    )

    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off[REQUEST_FIELD]["xz_sector_isometry"] == report
    assert len(handed_off[REQUEST_FIELD]["lower_bound_decisions"]) == 1

    tampered = deepcopy(artifact)
    tampered["xz_sector_isometry"]["shape"] = [2, 1]
    tampered["artifact_sha256"] = sector_certificate._canonical_sha256(
        tampered,
        omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(tampered)

    wrong_geometry = deepcopy(artifact)
    wrong_geometry["candidate"]["ell"] = 2
    wrong_geometry["candidate"]["m"] = 1
    wrong_geometry["artifact_sha256"] = sector_certificate._canonical_sha256(
        wrong_geometry,
        omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(wrong_geometry)

    missing = deepcopy(artifact)
    missing.pop("xz_sector_isometry")
    missing["artifact_sha256"] = sector_certificate._canonical_sha256(
        missing,
        omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(missing)


def test_certificate_isometry_binding_tampering_fails_closed(
    tmp_path, monkeypatch,
):
    _patch_isometric_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    claim = _isometric_claim()
    _, hx, hz, _, _ = _isometric_problem()
    claim[REQUEST_FIELD]["xz_sector_isometry"] = (
        verify_bb_xz_sector_isometry(hx, hz, ell=1, m=2)
    )
    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_isometric_solver,
    )
    assert certificate["passed"] is True

    top_level = deepcopy(certificate)
    top_level["xz_sector_isometry"]["shape"] = [2, 1]
    top_level["certificate_sha256"] = sector_certificate._certificate_sha256(
        top_level,
    )
    replay = verify_sector_sat_certificate(
        top_level,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_isometric_solver,
    )
    assert replay["passed"] is False
    assert replay["checks"]["xz_sector_isometry"] is False

    proof_tamper = deepcopy(certificate)
    proof = proof_tamper["claim"]["exact_distance_proof"]
    proof["xz_sector_isometry"]["shape"] = [2, 1]
    proof["proof_sha256"] = sector_certificate._canonical_sha256(
        proof,
        omit="proof_sha256",
    )
    proof_tamper["sector_exact"]["proof"] = proof
    proof_tamper["certificate_sha256"] = (
        sector_certificate._certificate_sha256(proof_tamper)
    )
    replay = verify_sector_sat_certificate(
        proof_tamper,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_isometric_solver,
    )
    assert replay["passed"] is False
    assert replay["replay_complete"] is False
    assert "isometry" in replay["failures"][0]


def test_solver_workers_bound_parallel_build_and_verification(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    lock = threading.Lock()
    barrier = threading.Barrier(2)
    active = 0
    maximum_active = 0

    def parallel_solver(checks, logicals, **kwargs):
        nonlocal active, maximum_active
        with lock:
            active += 1
            maximum_active = max(maximum_active, active)
        try:
            barrier.wait(timeout=2)
            time.sleep(0.02)
            return _fake_solver(checks, logicals, **kwargs)
        finally:
            with lock:
                active -= 1

    certificate = build_sector_sat_certificate(
        _claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=2,
        sector_solver=parallel_solver,
    )
    assert certificate["passed"] is True
    assert maximum_active == 2
    assert certificate["solver"]["solver_workers"] == 2

    maximum_active = 0
    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=2,
        sector_solver=parallel_solver,
    )
    assert replay["passed"] is True
    assert maximum_active == 2
    assert replay["solver_workers"] == 2


def test_verifier_reuses_each_validated_stage3_solver_encoding_pair(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    claim = _claim()
    _, hx, hz, lx, lz = _problem()
    configs = {
        "X": ("cadical153", "totalizer"),
        # A self-hashed but unsupported pair must not be trusted by replay.
        "Z": ("bad solver!", "untrusted-encoding"),
    }
    lower = []
    for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx)):
        solver_name, encoding = configs[sector]
        evidence = _fake_solver(
            checks,
            logicals,
            max_weight=1,
            sector=sector,
        )
        lower.append({
            "sector": sector,
            "partition_index": None,
            "solver_evidence": _trusted_replay_config(
                evidence,
                solver=solver_name,
                encoding=encoding,
            ),
        })
    claim[REQUEST_FIELD]["lower_bound_decisions"] = lower
    claim[REQUEST_FIELD]["upper_witness"] = {
        "sector": "X",
        "partition_index": None,
        "solver_evidence": _fake_solver(
            hz,
            lz,
            max_weight=2,
            sector="X",
        ),
    }
    certificate = build_sector_sat_certificate(
        claim,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    assert certificate["passed"] is True
    calls = {}

    # Deliberately omit timeout/workers/checkpoint kwargs: _call_solver must
    # filter its extended configuration safely for narrow custom adapters.
    def replay_solver(
        checks,
        logicals,
        *,
        max_weight,
        sector,
        partition_index=None,
        anchor_indices=(),
        solver="auto",
        cardinality_encoding="seqcounter",
    ):
        calls[sector] = (solver, cardinality_encoding)
        return _fake_solver(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
            partition_index=partition_index,
            anchor_indices=anchor_indices,
        )

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        solver_workers=2,
        sector_solver=replay_solver,
    )

    assert replay["passed"] is True
    assert calls == {
        "X": ("cadical153", "totalizer"),
        "Z": ("auto", "seqcounter"),
    }


def test_sector_certificate_tampered_witness_fails_closed(tmp_path, monkeypatch):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    certificate = build_sector_sat_certificate(
        _claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    certificate["claim"]["exact_distance_proof"]["upper_witness"][
        "solver_evidence"
    ]["objective"] = 1
    certificate["certificate_sha256"] = sector_certificate._certificate_sha256(
        certificate,
    )

    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    assert replay["passed"] is False
    assert replay["checks"]["upper_witness"] is False


def test_sector_certificate_metadata_tampering_fails_closed(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    original = build_sector_sat_certificate(
        _claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )

    cases = []
    coverage = deepcopy(original)
    coverage["sector_exact"]["coverage_mode"] = "first-nonzero"
    cases.append((coverage, "sector_exact_coverage_mode"))
    expected = deepcopy(original)
    expected["sector_exact"]["expected_lower_decisions"] = 3
    cases.append((expected, "sector_exact_counts"))
    completed = deepcopy(original)
    completed["sector_exact"]["completed_lower_decisions"] = 1
    cases.append((completed, "sector_exact_counts"))
    proof_binding = deepcopy(original)
    proof_binding["sector_exact"]["proof"] = {
        **proof_binding["sector_exact"]["proof"],
        "distance": 99,
    }
    cases.append((proof_binding, "sector_exact_proof_binding"))
    proof_metadata = deepcopy(original)
    proof = dict(proof_metadata["claim"]["exact_distance_proof"])
    proof["completed_lower_decisions"] = 1
    proof_without_hash = dict(proof)
    proof_without_hash.pop("proof_sha256", None)
    proof["proof_sha256"] = sector_certificate._canonical_sha256(
        proof_without_hash,
    )
    proof_metadata["claim"]["exact_distance_proof"] = proof
    proof_metadata["sector_exact"]["proof"] = proof
    cases.append((proof_metadata, "proof_metadata"))

    for certificate, failed_check in cases:
        certificate["certificate_sha256"] = sector_certificate._certificate_sha256(
            certificate,
        )
        replay = verify_sector_sat_certificate(
            certificate,
            known_answer_artifact=known,
            timeout_per_logical=1,
            total_timeout=10,
            sector_solver=_fake_solver,
        )
        assert replay["passed"] is False
        assert replay["checks"][failed_check] is False


def test_final_gate_recognizes_only_the_typed_sector_proof(tmp_path, monkeypatch):
    _patch_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    certificate = build_sector_sat_certificate(
        _claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    _, hx, hz, lx, lz = _problem()
    row = certificate["claim"]
    assert _typed_exact_sector_check(
        row,
        distance=2,
        k=1,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    ) is True

    row["exact_distance_proof"]["lower_bound_decisions"][0][
        "solver_evidence"
    ]["outcome"] = "hard_timeout"
    assert _typed_exact_sector_check(
        row,
        distance=2,
        k=1,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    ) is False


def test_stage3_handoff_replays_distqldpc_global_lower_fail_closed(
    monkeypatch,
):
    _patch_problem(monkeypatch)
    claim = _claim()
    candidate = {
        key: value for key, value in claim.items() if key != REQUEST_FIELD
    }
    _, hx, hz, lx, lz = _problem()
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    mode = "default"
    checkpoint_identity = {
        "stage3_gate": STAGE3_GATE,
        "candidate_digest": "digest",
        "target_mode": None,
        "target_binding_sha256": None,
        "phase": "lower-distqldpc",
        "lower_backend": "distqldpc",
        "cardinality_mode": mode,
        "coverage_mode": "global",
        "logical_detector_sha256": detector["report_sha256"],
        "translation_symmetry": None,
        "construction_symmetry_sha256": None,
        "xz_sector_isometry_sha256": None,
    }
    evidence = {
        "outcome": "exact",
        "decision_complete": True,
        "threshold_infeasible": True,
        "retryable": False,
        "exact_distance": 2,
    }
    wrapper = {
        "sector": "XZ",
        "partition_index": None,
        "anchor_cube": None,
        "cardinality_mode": mode,
        "checkpoint_identity": checkpoint_identity,
        "solver_evidence": evidence,
    }
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": candidate,
        "required_distance": 2,
        "coverage_mode": "global",
        "requested_coverage_mode": "global",
        "requested_lower_backend": "distqldpc",
        "lower_bound_backend": "distqldpc",
        "lower_bound_threshold": 1,
        "translation_symmetry": None,
        "construction_symmetry": None,
        "logical_detector": detector,
        "xz_sector_isometry": None,
        "anchor_cover_cubes": None,
        "expected_lower_decisions": 1,
        "completed_lower_decisions": 1,
        "expected_lower_partitions": 1,
        "completed_lower_partitions": 1,
        "lower_bound_decisions": [wrapper],
        "distqldpc_exact_distances": [2],
        "distqldpc_exact_decisions": [wrapper],
        "distqldpc_lower_decisions": [wrapper],
        "distqldpc_conflict": False,
        "distqldpc_conflict_details": None,
        "low_witnesses": [],
        "upper_witness": {
            "sector": "Z",
            "partition_index": None,
            "solver_evidence": _fake_solver(
                hx,
                lx,
                max_weight=2,
                sector="Z",
            ),
        },
        "units": [],
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(
        artifact,
    )

    observed = {}
    replayed_modes = []

    def replay(_evidence, *_matrices, **kwargs):
        observed.update(kwargs)
        replayed_modes.append(kwargs["cardinality_mode"])
        return []

    monkeypatch.setattr(
        sector_certificate,
        "verify_distqldpc_lower_evidence",
        replay,
    )
    monkeypatch.setattr(
        sector_certificate,
        "verify_distqldpc_exact_evidence",
        replay,
    )
    handed_off = claim_from_sector_sat_artifact(artifact)
    request = handed_off[REQUEST_FIELD]
    assert request["lower_bound_backend"] == "distqldpc"
    assert request["lower_bound_decisions"] == [wrapper]
    assert observed["cardinality_mode"] == mode
    assert observed["expected_checkpoint_identity"] == checkpoint_identity

    conflict = deepcopy(artifact)
    conflict["distqldpc_conflict"] = True
    conflict["artifact_sha256"] = sector_certificate._canonical_sha256(
        conflict, omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(conflict)

    contradiction = deepcopy(artifact)
    contradiction["lower_bound_decisions"][0]["solver_evidence"][
        "exact_distance"
    ] = 3
    contradiction["distqldpc_lower_decisions"] = deepcopy(
        contradiction["lower_bound_decisions"],
    )
    contradiction["distqldpc_exact_decisions"] = deepcopy(
        contradiction["lower_bound_decisions"],
    )
    contradiction["distqldpc_exact_distances"] = [3]
    contradiction["artifact_sha256"] = sector_certificate._canonical_sha256(
        contradiction, omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(contradiction)

    hidden_conflict = deepcopy(artifact)
    second_wrapper = deepcopy(wrapper)
    second_wrapper["cardinality_mode"] = "mto"
    second_wrapper["checkpoint_identity"]["cardinality_mode"] = "mto"
    second_wrapper["solver_evidence"]["exact_distance"] = 3
    hidden_conflict["distqldpc_exact_decisions"] = [
        deepcopy(wrapper),
        second_wrapper,
    ]
    # A malicious/stale producer must not hide the second exact value in its
    # summary fields and then rely on its freshly sealed outer artifact hash.
    hidden_conflict["distqldpc_exact_distances"] = [2]
    hidden_conflict["distqldpc_conflict"] = False
    hidden_conflict["distqldpc_conflict_details"] = None
    hidden_conflict["artifact_sha256"] = sector_certificate._canonical_sha256(
        hidden_conflict, omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(hidden_conflict)

    pysat_lower = [
        {
            "sector": "X",
            "partition_index": None,
            "anchor_cube": None,
            "solver_evidence": _fake_solver(
                hz,
                lz,
                max_weight=1,
                sector="X",
            ),
        },
        {
            "sector": "Z",
            "partition_index": None,
            "anchor_cube": None,
            "solver_evidence": _fake_solver(
                hx,
                lx,
                max_weight=1,
                sector="Z",
            ),
        },
    ]
    fallback = deepcopy(artifact)
    fallback["lower_bound_backend"] = "pysat"
    fallback["expected_lower_decisions"] = 2
    fallback["completed_lower_decisions"] = 2
    fallback["expected_lower_partitions"] = 2
    fallback["completed_lower_partitions"] = 2
    fallback["lower_bound_decisions"] = pysat_lower
    fallback["distqldpc_exact_distances"] = []
    fallback["distqldpc_exact_decisions"] = []
    fallback["distqldpc_lower_decisions"] = []
    fallback["artifact_sha256"] = sector_certificate._canonical_sha256(
        fallback, omit="artifact_sha256",
    )
    handed_off = claim_from_sector_sat_artifact(fallback)
    assert handed_off[REQUEST_FIELD]["lower_bound_backend"] == "pysat"

    fallback_conflict = deepcopy(fallback)
    fallback_conflict["distqldpc_conflict"] = True
    fallback_conflict["distqldpc_conflict_details"] = {
        "reasons": ["producer observed a backend contradiction"],
    }
    fallback_conflict["artifact_sha256"] = sector_certificate._canonical_sha256(
        fallback_conflict, omit="artifact_sha256",
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_conflict)

    fallback_low_witness = deepcopy(fallback)
    fallback_low_witness["status"] = "THRESHOLD_PROVEN"
    fallback_low_witness["upper_witness"] = None
    fallback_low_witness["low_witnesses"] = [{
        "sector": "X",
        "partition_index": None,
        "producer_claimed_objective": 1,
    }]
    fallback_low_witness["artifact_sha256"] = (
        sector_certificate._canonical_sha256(
            fallback_low_witness, omit="artifact_sha256",
        )
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_low_witness)

    fallback_hidden_conflict = deepcopy(fallback)
    fallback_hidden_conflict["distqldpc_exact_decisions"] = [
        deepcopy(wrapper),
        deepcopy(second_wrapper),
    ]
    fallback_hidden_conflict["distqldpc_exact_distances"] = [2]
    fallback_hidden_conflict["distqldpc_conflict"] = False
    fallback_hidden_conflict["distqldpc_conflict_details"] = None
    fallback_hidden_conflict["artifact_sha256"] = (
        sector_certificate._canonical_sha256(
            fallback_hidden_conflict, omit="artifact_sha256",
        )
    )
    replayed_modes.clear()
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_hidden_conflict)
    assert replayed_modes == ["default", "mto"]

    # Even a self-consistent single external exact result cannot contradict a
    # separately replayed PySAT lower proof or upper witness.
    fallback_lower_conflict = deepcopy(fallback)
    below_lower = deepcopy(wrapper)
    below_lower["solver_evidence"]["exact_distance"] = 1
    fallback_lower_conflict["status"] = "THRESHOLD_PROVEN"
    fallback_lower_conflict["upper_witness"] = None
    fallback_lower_conflict["distqldpc_exact_distances"] = [1]
    fallback_lower_conflict["distqldpc_exact_decisions"] = [below_lower]
    fallback_lower_conflict["distqldpc_lower_decisions"] = []
    fallback_lower_conflict["artifact_sha256"] = (
        sector_certificate._canonical_sha256(
            fallback_lower_conflict, omit="artifact_sha256",
        )
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_lower_conflict)

    fallback_witness_conflict = deepcopy(fallback)
    fallback_witness_conflict["distqldpc_exact_distances"] = [3]
    fallback_witness_conflict["distqldpc_exact_decisions"] = [
        deepcopy(second_wrapper),
    ]
    fallback_witness_conflict["distqldpc_lower_decisions"] = [
        deepcopy(second_wrapper),
    ]
    fallback_witness_conflict["artifact_sha256"] = (
        sector_certificate._canonical_sha256(
            fallback_witness_conflict, omit="artifact_sha256",
        )
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_witness_conflict)

    upper_unsat_units = []
    for item in pysat_lower:
        upper_unsat = deepcopy(item["solver_evidence"])
        upper_unsat["max_weight"] = 2
        upper_unsat["evidence_sha256"] = sector_certificate._canonical_sha256(
            upper_unsat, omit="evidence_sha256",
        )
        upper_unsat_units.append({
            "phase": "upper",
            "sector": item["sector"],
            "partition_index": None,
            "solver_evidence": upper_unsat,
        })
    fallback_upper_unsat_conflict = deepcopy(fallback)
    fallback_upper_unsat_conflict["status"] = "THRESHOLD_PROVEN"
    fallback_upper_unsat_conflict["upper_witness"] = None
    fallback_upper_unsat_conflict["distqldpc_exact_distances"] = [2]
    fallback_upper_unsat_conflict["distqldpc_exact_decisions"] = [
        deepcopy(wrapper),
    ]
    fallback_upper_unsat_conflict["distqldpc_lower_decisions"] = [
        deepcopy(wrapper),
    ]
    fallback_upper_unsat_conflict["units"] = upper_unsat_units
    fallback_upper_unsat_conflict["artifact_sha256"] = (
        sector_certificate._canonical_sha256(
            fallback_upper_unsat_conflict, omit="artifact_sha256",
        )
    )
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(fallback_upper_unsat_conflict)


def test_typed_stage3_handoff_preserves_exact_sector_evidence(monkeypatch):
    _patch_problem(monkeypatch)
    claim = _claim()
    lower = []
    for sector in ("X", "Z"):
        code, hx, hz, lx, lz = _problem()
        checks, logicals = (
            (hx, lx) if sector == "Z" else (hz, lz)
        )
        lower.append({
            "sector": sector,
            "partition_index": None,
            "solver_evidence": _fake_solver(
                checks,
                logicals,
                max_weight=1,
                sector=sector,
            ),
        })
    _, hx, hz, lx, lz = _problem()
    certificate_detector = verify_css_logical_detectors(hx, hz, lx, lz)
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": {key: value for key, value in claim.items() if key != REQUEST_FIELD},
        "required_distance": 2,
        "coverage_mode": "global",
        "translation_symmetry": None,
        "logical_detector": certificate_detector,
        "lower_bound_decisions": lower,
        "upper_witness": {
            "sector": "Z",
            "partition_index": None,
            "solver_evidence": _fake_solver(
                hx,
                lx,
                max_weight=2,
                sector="Z",
            ),
        },
    }
    assert certificate_detector["verified"] is True
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(artifact)

    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off[REQUEST_FIELD]["coverage_mode"] == "global"
    assert len(handed_off[REQUEST_FIELD]["lower_bound_decisions"]) == 2
    assert builder_for_claim(handed_off) is build_sector_sat_certificate
    assert verifier_for_certificate({"certificate_type": CERTIFICATE_TYPE})


def test_scalar_stage3_handoff_preserves_explicit_target_binding(monkeypatch):
    n = 16
    k = 16
    hx = np.zeros((0, n), dtype=np.uint8)
    hz = np.zeros((0, n), dtype=np.uint8)
    lx = np.eye(n, dtype=np.uint8)
    lz = np.eye(n, dtype=np.uint8)
    monkeypatch.setattr(
        sector_certificate,
        "_matrices",
        lambda _claim: (
            SimpleNamespace(num_qudits=n, dimension=k),
            hx,
            hz,
            lx,
            lz,
        ),
    )
    monkeypatch.setattr(
        sector_certificate,
        "_xz_isometry_context",
        lambda *_args, **_kwargs: (None, ("X", "Z")),
    )
    monkeypatch.setattr(
        sector_certificate,
        "_coverage_context",
        lambda *_args, **_kwargs: (
            {"verified": True},
            {"verified": True, "orbit_representatives": []},
            (),
        ),
    )
    claim = {
        "ell": 2,
        "m": 4,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": n,
        "k": k,
        "canonical_digest": "scalar-target-digest",
    }
    selected_target = target_binding(n, k, TARGET_MODE_SCALAR)
    required = selected_target["required_distance"]
    claim.update({
        "required_distance": required,
        "target_mode": TARGET_MODE_SCALAR,
        "target": selected_target,
    })
    lower = []
    for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx)):
        evidence = _fake_solver(
            checks,
            logicals,
            max_weight=1,
            sector=sector,
        )
        evidence.update({
            "max_weight": required - 1,
            "outcome": "unsat",
            "threshold_infeasible": True,
            "success": False,
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
        evidence.pop("evidence_sha256", None)
        evidence["evidence_sha256"] = sector_certificate._canonical_sha256(
            evidence,
        )
        lower.append({
            "sector": sector,
            "partition_index": None,
            "solver_evidence": evidence,
        })
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "THRESHOLD_PROVEN",
        "candidate": claim,
        "target_mode": TARGET_MODE_SCALAR,
        "target": selected_target,
        "required_distance": required,
        "lower_bound_threshold": required - 1,
        "coverage_mode": "global",
        "translation_symmetry": None,
        "logical_detector": {"verified": True},
        "lower_bound_decisions": lower,
        "upper_witness": None,
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(
        artifact,
    )

    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off["target"] == selected_target
    assert handed_off["target_binding_sha256"] == (
        selected_target["binding_sha256"]
    )
    assert handed_off[REQUEST_FIELD]["target"] == selected_target
    assert handed_off[REQUEST_FIELD]["required_distance"] == required


def test_scalar_target_build_verify_end_to_end_uses_bound_threshold(
    tmp_path,
    monkeypatch,
):
    n = 72
    k = 12
    hx = np.zeros((n - k, n), dtype=np.uint8)
    hx[:, :n - k] = np.eye(n - k, dtype=np.uint8)
    hz = np.zeros((0, n), dtype=np.uint8)
    lx = np.zeros((k, n), dtype=np.uint8)
    lz = np.zeros((k, n), dtype=np.uint8)
    lx[:, n - k:] = np.eye(k, dtype=np.uint8)
    lz[:, n - k:] = np.eye(k, dtype=np.uint8)
    problem = SimpleNamespace(num_qudits=n, dimension=k), hx, hz, lx, lz
    monkeypatch.setattr(sector_certificate, "_matrices", lambda _claim: problem)
    monkeypatch.setattr(
        sector_certificate,
        "check_code_novelty",
        lambda *_args, **_kwargs: {
            "checked": True,
            "novel": True,
            "canonical_digest": "scalar-target-digest",
            "registry_sha256": "registry",
        },
    )

    def typed_gate(row, **_kwargs):
        accepted = _typed_exact_sector_check(
            row,
            distance=int(row["d"]),
            k=k,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
        )
        return {
            "accepted": accepted,
            "checks": {"typed_exact_sector_sat_proof": accepted},
            "failures": [] if accepted else ["typed_exact_sector_sat_proof"],
        }

    monkeypatch.setattr(
        sector_certificate,
        "evaluate_challenge_gate",
        typed_gate,
    )

    selected_target = target_binding(n, k, TARGET_MODE_SCALAR)
    gist_target = target_binding(n, k, TARGET_MODE_GIST)
    assert gist_target["required_distance"] == 7
    assert selected_target["required_distance"] == 9
    required = int(selected_target["required_distance"])
    claim = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": n,
        "k": k,
        "required_distance": required,
        "canonical_digest": "scalar-target-digest",
        "target_mode": TARGET_MODE_SCALAR,
        "target": selected_target,
    }

    checkpoint_identities = []

    def scalar_solver(
        checks,
        logicals,
        *,
        max_weight,
        sector,
        partition_index=None,
        anchor_indices=(),
        checkpoint_identity=None,
        **_kwargs,
    ):
        checks = np.asarray(checks, dtype=np.uint8)
        logicals = np.asarray(logicals, dtype=np.uint8)
        if checkpoint_identity is not None:
            checkpoint_identities.append(dict(checkpoint_identity))
        evidence = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "formulation": SAT_FORMULATION,
            "sector": sector,
            "max_weight": max_weight,
            "partition_index": partition_index,
            "anchor_indices": list(anchor_indices),
            "backend": {
                "distribution": "python-sat",
                "version": "test",
                "solver": "test-solver",
            },
            "instance": {
                "check_matrix_sha256": sector_certificate._array_sha256(
                    "checks",
                    checks,
                ),
                "target_logicals_sha256": sector_certificate._array_sha256(
                    "logicals",
                    logicals,
                ),
                "partition_index": partition_index,
                "anchor_indices": list(anchor_indices),
            },
            "decision_complete": True,
        }
        if max_weight < required:
            evidence.update({
                "outcome": "unsat",
                "threshold_infeasible": True,
                "success": False,
                "operator": None,
                "objective": None,
                "logical_syndrome": None,
            })
        else:
            vector = np.zeros(n, dtype=np.uint8)
            vector[n - k:n - k + required] = 1
            evidence.update({
                "outcome": "sat",
                "threshold_infeasible": False,
                "success": True,
                "operator": pack_vector(vector),
                "objective": required,
                "logical_syndrome": (
                    (logicals @ vector) & 1
                ).astype(int).tolist(),
            })
        evidence["evidence_sha256"] = sector_certificate._canonical_sha256(
            evidence,
        )
        return evidence

    lower = []
    for sector, checks, logicals in ("X", hz, lz), ("Z", hx, lx):
        lower.append({
            "sector": sector,
            "partition_index": None,
            "solver_evidence": scalar_solver(
                checks,
                logicals,
                max_weight=required - 1,
                sector=sector,
            ),
        })
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    assert detector["verified"] is True
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "THRESHOLD_PROVEN",
        "candidate": claim,
        "target_mode": TARGET_MODE_SCALAR,
        "target": selected_target,
        "required_distance": required,
        "lower_bound_threshold": required - 1,
        "coverage_mode": "global",
        "translation_symmetry": None,
        "logical_detector": detector,
        "lower_bound_decisions": lower,
        "upper_witness": None,
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(
        artifact,
    )
    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off["target"] == selected_target
    assert handed_off[REQUEST_FIELD]["target"] == selected_target
    assert handed_off[REQUEST_FIELD]["target_binding_sha256"] == (
        selected_target["binding_sha256"]
    )

    known = tmp_path / "known.json"
    known.write_text("{}")
    checkpoint_identities.clear()
    certificate = build_sector_sat_certificate(
        handed_off,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=tmp_path / "scalar-certificate.json",
        resume=True,
        sector_solver=scalar_solver,
    )
    assert certificate["passed"] is True
    assert certificate["target"] == selected_target
    assert certificate["target_gate"]["required_distance"] == required
    assert certificate["target_gate"]["passed"] is True
    assert certificate["claim"]["required_distance"] == required
    proof = certificate["claim"]["exact_distance_proof"]
    assert proof["distance"] == required
    assert proof["target"] == selected_target
    assert certificate["sector_exact"]["target"] == selected_target
    assert checkpoint_identities
    assert all(
        identity["target_mode"] == TARGET_MODE_SCALAR
        and identity["target_binding_sha256"]
        == selected_target["binding_sha256"]
        and identity["required_distance"] == required
        for identity in checkpoint_identities
    )

    checkpoint_identities.clear()
    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=tmp_path / "scalar-replay.json",
        resume=True,
        sector_solver=scalar_solver,
    )
    assert replay["passed"] is True
    assert replay["checks"]["target_binding"] is True
    assert replay["checks"]["target_gate"] is True
    assert replay["checks"]["target_win"] is True
    assert replay["checks"]["stored_final_gate"] is True
    assert checkpoint_identities
    assert all(
        identity["target_mode"] == TARGET_MODE_SCALAR
        and identity["target_binding_sha256"]
        == selected_target["binding_sha256"]
        and identity["required_distance"] == required
        for identity in checkpoint_identities
    )

    missing_claim_binding = deepcopy(certificate)
    del missing_claim_binding["claim"]["target_binding_sha256"]
    missing_claim_binding["certificate_sha256"] = (
        sector_certificate._certificate_sha256(missing_claim_binding)
    )
    rejected_missing_binding = verify_sector_sat_certificate(
        missing_claim_binding,
        known_answer_artifact=known,
        sector_solver=scalar_solver,
    )
    assert rejected_missing_binding["passed"] is False
    assert rejected_missing_binding["failures"][0].startswith(
        "certificate reconstruction failed",
    )

    tampered = deepcopy(certificate)
    tampered["claim"]["exact_distance_proof"]["target"] = gist_target
    _reseal_sector_certificate(tampered)
    rejected = verify_sector_sat_certificate(
        tampered,
        known_answer_artifact=known,
        sector_solver=scalar_solver,
    )
    assert rejected["passed"] is False
    assert rejected["failures"][0].startswith("certificate reconstruction failed")


def test_anchored_handoff_recomputes_translation_orbits(monkeypatch):
    import scripts.screen_frontier_xor as xor_screen

    _patch_problem(monkeypatch)
    anchors = (0, 2)
    symmetry = {
        "method": "bb-torus-translation-row-set-v1",
        "verified": True,
        "orbit_representatives": list(anchors),
    }
    monkeypatch.setattr(
        xor_screen,
        "verify_bb_translation_symmetry",
        lambda _claim: dict(symmetry),
    )
    claim = _claim()
    _, hx, hz, lx, lz = _problem()
    lower = []
    for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx)):
        lower.append({
            "sector": sector,
            "partition_index": None,
            "solver_evidence": _fake_solver(
                checks,
                logicals,
                max_weight=1,
                sector=sector,
                anchor_indices=anchors,
            ),
        })
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": {key: value for key, value in claim.items() if key != REQUEST_FIELD},
        "required_distance": 2,
        "coverage_mode": "global",
        "translation_symmetry": symmetry,
        "logical_detector": verify_css_logical_detectors(hx, hz, lx, lz),
        "lower_bound_decisions": lower,
        "upper_witness": {
            "sector": "Z",
            "partition_index": None,
            "solver_evidence": _fake_solver(
                hx,
                lx,
                max_weight=2,
                sector="Z",
                anchor_indices=anchors,
            ),
        },
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(artifact)
    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off[REQUEST_FIELD]["use_translation_anchors"] is True

    artifact["translation_symmetry"] = {**symmetry, "orbit_representatives": [0, 1]}
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(artifact)
    with np.testing.assert_raises(ValueError):
        claim_from_sector_sat_artifact(artifact)


def test_threshold_stage3_handoff_lets_stage4_find_weight_r_witness(
    tmp_path, monkeypatch,
):
    _patch_problem(monkeypatch)
    claim = _claim()
    _, hx, hz, lx, lz = _problem()
    lower = [
        {
            "sector": sector,
            "partition_index": None,
            "solver_evidence": _fake_solver(
                checks,
                logicals,
                max_weight=1,
                sector=sector,
            ),
        }
        for sector, checks, logicals in (("X", hz, lz), ("Z", hx, lx))
    ]
    artifact = {
        "schema_version": 1,
        "gate": STAGE3_GATE,
        "status": "THRESHOLD_PROVEN",
        "candidate": {key: value for key, value in claim.items() if key != REQUEST_FIELD},
        "required_distance": 2,
        "coverage_mode": "global",
        "translation_symmetry": None,
        "logical_detector": verify_css_logical_detectors(hx, hz, lx, lz),
        "lower_bound_decisions": lower,
        "upper_witness": None,
    }
    artifact["artifact_sha256"] = sector_certificate._canonical_sha256(artifact)
    handed_off = claim_from_sector_sat_artifact(artifact)
    assert handed_off[REQUEST_FIELD]["stage3_status"] == "THRESHOLD_PROVEN"
    assert handed_off[REQUEST_FIELD]["upper_witness"] is None

    known = tmp_path / "known.json"
    known.write_text("{}")
    certificate = build_sector_sat_certificate(
        handed_off,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_fake_solver,
    )
    assert certificate["passed"] is True
    assert certificate["sector_exact"]["lower_resumed_from_stage3"] is True
    assert certificate["sector_exact"]["upper_resumed_from_stage3"] is False


def test_stage4_escalates_until_first_exact_witness_and_reruns_final_lower(
    tmp_path, monkeypatch,
):
    _patch_steane_problem(monkeypatch)
    known = tmp_path / "known.json"
    known.write_text("{}")
    calls = []
    certificate = build_sector_sat_certificate(
        _steane_claim(),
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=20,
        checkpoint_path=tmp_path / "certificate.json",
        resume=True,
        sector_solver=_steane_solver_factory(calls),
    )

    assert certificate["passed"] is True
    assert certificate["claim"]["d"] == 3
    proof = certificate["claim"]["exact_distance_proof"]
    assert proof["required_distance"] == 2
    assert proof["lower_bound_threshold"] == 2
    assert proof["coverage_mode"] == "global"
    assert {item["solver_evidence"]["max_weight"] for item in proof[
        "lower_bound_decisions"
    ]} == {2}
    assert certificate["sector_exact"]["completed_unsat_thresholds"] == [2]
    escalation_paths = {
        (item["sector"], item["max_weight"]): item["checkpoint_path"]
        for item in calls
        if item["max_weight"] >= 2
    }
    assert escalation_paths[("X", 2)].endswith(
        ".escalation.X.global.w2.json",
    )
    assert escalation_paths[("Z", 2)].endswith(
        ".escalation.Z.global.w2.json",
    )
    assert escalation_paths[("X", 3)].endswith(
        ".escalation.X.global.w3.json",
    )

    calls.clear()
    replay = verify_sector_sat_certificate(
        certificate,
        known_answer_artifact=known,
        timeout_per_logical=1,
        total_timeout=10,
        sector_solver=_steane_solver_factory(calls),
    )
    assert replay["passed"] is True
    assert [(item["sector"], item["max_weight"]) for item in calls] == [
        ("X", 2),
        ("Z", 2),
    ]
