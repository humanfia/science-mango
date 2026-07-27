"""Tests for structured MILP evidence and certificate integrity."""

import copy
import json
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

import evaluation.certificate as certificate_module
from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    _certificate_sha256,
    build_css_certificate,
    pack_vector,
    solve_css_below_threshold,
    solve_css_direction,
    solve_css_sector_xor,
    unpack_vector,
    verify_css_sector_witness,
    verify_css_witness,
    verify_direction_evidence,
    verify_css_certificate,
)
from evaluation.distance_milp import get_code_matrices


def _tiny_direction():
    code = build_bb_code(
        2, 2,
        [(0, 0), (0, 1)],
        [(0, 0), (1, 0)],
    )
    hx, _, lx, _ = get_code_matrices(code)
    return np.asarray(hx, dtype=np.uint8), np.asarray(lx[0], dtype=np.uint8)


def _tiny_claim():
    return {
        "ell": 2,
        "m": 2,
        "A_terms": [[0, 0], [0, 1]],
        "B_terms": [[0, 0], [1, 0]],
    }


KNOWN_ANSWER = (
    Path(__file__).resolve().parents[1]
    / "results"
    / "known_answer_gate.json"
)


def test_packed_vector_round_trip_and_tamper_detection():
    vector = np.array([1, 0, 1, 1, 0, 0, 1], dtype=np.uint8)
    packed = pack_vector(vector)
    assert np.array_equal(unpack_vector(packed), vector)
    packed["weight"] += 1
    try:
        unpack_vector(packed)
    except ValueError:
        pass
    else:
        raise AssertionError("tampered packed vector was accepted")


def test_direction_evidence_contains_replayable_zero_gap_witness():
    checks, logical = _tiny_direction()
    evidence = solve_css_direction(checks, logical, timeout=30)
    evidence["target_logical"] = pack_vector(logical)
    assert evidence["success"] is True
    assert evidence["mip_gap"] == 0.0
    assert evidence["mip_dual_bound"] == evidence["objective"]
    assert verify_direction_evidence(evidence, checks, logical) == []


def test_threshold_direction_proves_absence_below_exact_distance():
    checks, logical = _tiny_direction()
    evidence = solve_css_below_threshold(
        checks, logical, max_weight=1, timeout=30,
    )
    assert evidence["status"] == 2
    assert evidence["threshold_infeasible"] is True
    assert evidence["operator"] is None


def test_threshold_direction_returns_replayable_counterexample():
    checks, logical = _tiny_direction()
    evidence = solve_css_below_threshold(
        checks, logical, max_weight=2, timeout=30,
    )
    assert evidence["success"] is True
    assert evidence["threshold_infeasible"] is False
    assert evidence["objective"] == 2
    evidence["target_logical"] = pack_vector(logical)
    assert verify_css_witness(evidence, checks, logical) == []

def test_xor_sector_threshold_proves_absence_below_distance():
    checks, logical = _tiny_direction()
    evidence = solve_css_sector_xor(
        checks, logical[None, :], timeout=30, max_weight=1,
    )
    assert evidence["status_name"] == "INFEASIBLE"
    assert evidence["threshold_infeasible"] is True
    assert evidence["operator"] is None


def test_xor_sector_returns_replayable_global_witness():
    checks, logical = _tiny_direction()
    evidence = solve_css_sector_xor(
        checks, logical[None, :], timeout=30, max_weight=2,
    )
    assert evidence["success"] is True
    assert evidence["objective"] == 2
    assert verify_css_sector_witness(
        evidence, checks, logical[None, :],
    ) == []
    exact = solve_css_sector_xor(
        checks, logical[None, :], timeout=30,
    )
    assert exact["exact"] is True
    assert exact["objective"] == 2


def test_xor_sector_anchor_is_replayed_from_witness():
    checks, logical = _tiny_direction()
    evidence = solve_css_sector_xor(
        checks,
        logical[None, :],
        timeout=30,
        max_weight=2,
        anchor_indices=(0, 4),
    )
    assert evidence["success"] is True
    assert verify_css_sector_witness(
        evidence, checks, logical[None, :],
    ) == []
    operator = unpack_vector(evidence["operator"])
    zero_index = int(np.flatnonzero(operator == 0)[0])
    evidence["anchor_indices"] = [zero_index]
    assert "operator violates stored symmetry anchors" in verify_css_sector_witness(
        evidence, checks, logical[None, :],
    )



def test_direction_evidence_rejects_tampered_objective():
    checks, logical = _tiny_direction()
    evidence = solve_css_direction(checks, logical, timeout=30)
    evidence["target_logical"] = pack_vector(logical)
    evidence["objective"] += 1
    assert verify_direction_evidence(evidence, checks, logical)


def test_certificate_digest_changes_on_evidence_tamper():
    certificate = {
        "schema_version": 1,
        "milp": {"directions": [{"objective": 2}]},
    }
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    tampered = copy.deepcopy(certificate)
    tampered["milp"]["directions"][0]["objective"] = 3
    assert tampered["certificate_sha256"] != _certificate_sha256(tampered)


def test_css_solver_records_and_limits_highs_threads(monkeypatch):
    captured = {}

    def fake_milp(**kwargs):
        captured.update(kwargs)
        values = np.zeros(len(kwargs["c"]))
        values[0] = 1
        return SimpleNamespace(
            success=True,
            status=0,
            message="ok",
            x=values,
            fun=1,
            mip_dual_bound=1.0,
            mip_gap=0.0,
            mip_node_count=0,
        )

    monkeypatch.setattr(certificate_module, "milp", fake_milp)
    checks, logical = _tiny_direction()
    evidence = solve_css_direction(
        checks, logical, timeout=1, solver_workers=3,
    )

    assert captured["options"]["threads"] == 3
    assert evidence["solver_workers"] == 3
    with pytest.raises(ValueError, match="between 1 and 8"):
        solve_css_direction(checks, logical, timeout=1, solver_workers=9)


def test_build_checkpoint_survives_interruption_and_resumes(
    tmp_path, monkeypatch,
):
    checkpoint = tmp_path / "build.checkpoint.json"
    real_solve = certificate_module.solve_css_direction
    first_calls = 0

    def interrupt_second(*args, **kwargs):
        nonlocal first_calls
        first_calls += 1
        if first_calls == 2:
            raise RuntimeError("simulated interruption")
        return real_solve(*args, **kwargs)

    monkeypatch.setattr(
        certificate_module, "solve_css_direction", interrupt_second,
    )
    with pytest.raises(RuntimeError, match="simulated interruption"):
        build_css_certificate(
            _tiny_claim(),
            known_answer_artifact=KNOWN_ANSWER,
            timeout_per_logical=30,
            total_timeout=120,
            checkpoint_path=checkpoint,
            resume=True,
        )
    saved = json.loads(checkpoint.read_text())
    assert saved["completed_directions"] == 1
    assert "solver_workers" not in saved["binding"]["solver"]

    resumed_calls = 0

    def count_remaining(*args, **kwargs):
        nonlocal resumed_calls
        resumed_calls += 1
        return real_solve(*args, **kwargs)

    monkeypatch.setattr(
        certificate_module, "solve_css_direction", count_remaining,
    )
    certificate = build_css_certificate(
        _tiny_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=30,
        total_timeout=120,
        checkpoint_path=checkpoint,
        resume=True,
    )

    assert certificate["milp"]["exact"] is True
    assert certificate["milp"]["resumed_directions"] == 1
    assert resumed_calls == certificate["milp"]["expected_directions"] - 1


def test_verify_checkpoint_and_global_timeout(tmp_path, monkeypatch):
    certificate = build_css_certificate(
        _tiny_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=30,
        total_timeout=120,
    )
    checkpoint = tmp_path / "verify.checkpoint.json"
    real_solve = certificate_module.solve_css_direction
    first_calls = 0

    def interrupt_second(*args, **kwargs):
        nonlocal first_calls
        first_calls += 1
        if first_calls == 2:
            raise RuntimeError("simulated verifier interruption")
        return real_solve(*args, **kwargs)

    monkeypatch.setattr(
        certificate_module, "solve_css_direction", interrupt_second,
    )
    with pytest.raises(RuntimeError, match="verifier interruption"):
        verify_css_certificate(
            certificate,
            known_answer_artifact=KNOWN_ANSWER,
            checkpoint_path=checkpoint,
            resume=True,
            timeout_per_logical=30,
            total_timeout=120,
        )
    assert json.loads(checkpoint.read_text())["completed_directions"] == 1

    monkeypatch.setattr(
        certificate_module, "solve_css_direction", real_solve,
    )
    resumed = verify_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        checkpoint_path=checkpoint,
        resume=True,
        timeout_per_logical=30,
        total_timeout=120,
    )
    assert resumed["resumed_directions"] == 1
    assert (
        resumed["rerun_directions_completed"]
        == resumed["directions_total"]
    )

    def should_not_run(*args, **kwargs):
        raise AssertionError("global timeout should stop before a rerun")

    monkeypatch.setattr(
        certificate_module, "solve_css_direction", should_not_run,
    )
    timed_out = verify_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=30,
        total_timeout=1e-12,
    )
    assert timed_out["checks"]["stored_direction_evidence"] is True
    assert timed_out["checks"]["milp_rerun"] is False
    assert any(
        "rerun total timeout exhausted" in failure
        for failure in timed_out["failures"]
    )


def test_verifier_fails_closed_on_malformed_directions():
    certificate = build_css_certificate(
        _tiny_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=30,
        total_timeout=120,
    )
    certificate["milp"]["directions"] = {"not": "a list"}
    certificate["certificate_sha256"] = _certificate_sha256(certificate)

    result = verify_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        rerun_milp=False,
    )

    assert result["passed"] is False
    assert "milp.directions must be a list" in result["failures"][0]
