"""Tests for structured MILP evidence and certificate integrity."""

import copy

import numpy as np

from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    _certificate_sha256,
    pack_vector,
    solve_css_direction,
    unpack_vector,
    verify_direction_evidence,
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
