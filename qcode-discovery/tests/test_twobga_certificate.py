"""End-to-end trust-boundary tests for typed 2BGA certificates."""

from __future__ import annotations

import copy
import itertools
from pathlib import Path

import numpy as np
import pytest

import evaluation.certificate_dispatch as dispatch
import evaluation.twobga_certificate as twobga_certificate
from humanize.pipeline import _twobga_expected_lower_decisions
from evaluation.bb_code import build_bb_code
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    _pack_vector,
)
from evaluation.final_gate import evaluate_final_gate
from evaluation.twobga_certificate import (
    CERTIFICATE_TYPE,
    build_twobga_certificate,
    validate_twobga_candidate_rejection,
    validate_twobga_exact_proof,
    verify_twobga_certificate,
)
from scripts import screen_frontier_twobga as twobga_screen
from scripts.audit_candidate_pool import _terminal_certificate_rejection


KNOWN_ANSWER = (
    Path(__file__).resolve().parents[1]
    / "results"
    / "known_answer_gate.json"
)


def _candidate(*, digest: str = "twobga-certificate-fixture") -> dict:
    """Return an eligible small BB/2BGA test instance."""

    ell, m = 2, 3
    a_terms = [(0, 0), (0, 1)]
    b_terms = [(0, 0), (1, 0)]
    code = build_bb_code(ell, m, a_terms, b_terms)
    return {
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        # This is the final gate's Pareto-aware threshold for [[12,2,*]].
        "required_distance": 6,
        "canonical_digest": digest,
    }


def _find_operator(
    checks: np.ndarray,
    detectors: np.ndarray,
    *,
    weight: int,
    anchors: tuple[int, ...],
) -> np.ndarray:
    width = int(np.asarray(checks).shape[1])
    for support in itertools.combinations(range(width), weight):
        vector = np.zeros(width, dtype=np.uint8)
        vector[list(support)] = 1
        if np.any((np.asarray(checks, dtype=np.uint8) @ vector) & 1):
            continue
        if not np.any((np.asarray(detectors, dtype=np.uint8) @ vector) & 1):
            continue
        if anchors and not any(int(vector[index]) for index in anchors):
            continue
        return vector
    raise AssertionError("fixture has no requested logical operator")


def _find_operator_up_to(
    checks: np.ndarray,
    detectors: np.ndarray,
    *,
    max_weight: int,
    anchors: tuple[int, ...],
) -> np.ndarray:
    for weight in range(1, max_weight + 1):
        try:
            return _find_operator(
                checks,
                detectors,
                weight=weight,
                anchors=anchors,
            )
        except AssertionError:
            continue
    raise AssertionError("fixture has no bounded logical operator")


def _bound_evidence(
    checks: np.ndarray,
    detectors: np.ndarray,
    *,
    sector: str,
    max_weight: int,
    anchors: tuple[int, ...],
    outcome: str,
    operator: np.ndarray | None = None,
) -> dict:
    checks = np.asarray(checks, dtype=np.uint8) & 1
    detectors = np.asarray(detectors, dtype=np.uint8) & 1
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": "css-global-logical-threshold-cnf-v1",
        "instance": {
            "check_matrix_sha256": twobga_screen._sat_array_sha256(
                "checks", checks,
            ),
            "target_logicals_sha256": twobga_screen._sat_array_sha256(
                "logicals", detectors,
            ),
            "partition_index": None,
            "anchor_indices": list(anchors),
            "zero_anchor_indices": [],
            "one_anchor_index": None,
            "anchor_cube_sha256": None,
        },
        "backend": {"distribution": "python-sat", "solver": "fixture"},
        "sector": sector,
        "max_weight": max_weight,
        "partition_index": None,
        "anchor_indices": list(anchors),
        "zero_anchor_indices": [],
        "one_anchor_index": None,
        "anchor_cube_sha256": None,
        "decision_complete": True,
        "threshold_infeasible": outcome == "unsat",
        "outcome": outcome,
    }
    if outcome == "unsat":
        evidence.update({
            "success": False,
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    elif outcome == "sat" and operator is not None:
        vector = np.asarray(operator, dtype=np.uint8) & 1
        evidence.update({
            "success": True,
            "operator": _pack_vector(vector),
            "objective": int(vector.sum()),
            "logical_syndrome": ((detectors @ vector) & 1).astype(int).tolist(),
        })
    else:
        raise AssertionError("SAT fixture requires an operator")
    evidence["evidence_sha256"] = twobga_screen._canonical_sha256(evidence)
    return evidence


def _screen_artifact(
    monkeypatch,
    tmp_path: Path,
    *,
    threshold_only: bool,
) -> dict:
    candidate = _candidate(digest=f"twobga-{threshold_only}")

    def solver(checks, detectors, **kwargs):
        checks = np.asarray(checks, dtype=np.uint8) & 1
        detectors = np.asarray(detectors, dtype=np.uint8) & 1
        anchors = tuple(kwargs["anchor_indices"])
        max_weight = int(kwargs["max_weight"])
        if checks.shape[1] < candidate["n"]:
            return _bound_evidence(
                checks,
                detectors,
                sector=str(kwargs["sector"]),
                max_weight=max_weight,
                anchors=anchors,
                outcome="unsat",
            )
        operator = _find_operator(
            checks,
            detectors,
            weight=max_weight,
            anchors=anchors,
        )
        return _bound_evidence(
            checks,
            detectors,
            sector=str(kwargs["sector"]),
            max_weight=max_weight,
            anchors=anchors,
            outcome="sat",
            operator=operator,
        )

    monkeypatch.setattr(twobga_screen, "solve_css_sector_sat", solver)
    artifact = twobga_screen.screen_twobga_candidate(
        candidate,
        output=tmp_path / f"stage3-{threshold_only}.json",
        timeout=1,
        workers=3,
        threshold_only=threshold_only,
    )
    assert artifact["status"] == (
        "THRESHOLD_PROVEN" if threshold_only else "EXACT_PROVEN"
    )
    return artifact


@pytest.fixture
def exact_certificate(monkeypatch, tmp_path) -> dict:
    artifact = _screen_artifact(
        monkeypatch,
        tmp_path,
        threshold_only=False,
    )
    request = twobga_screen.claim_from_twobga_artifact(artifact)
    monkeypatch.setattr(
        twobga_certificate,
        "evaluate_challenge_gate",
        lambda *args, **kwargs: {
            "accepted": True,
            "checks": {"fixture": True},
            "failures": [],
        },
    )

    def forbidden_solver(*args, **kwargs):
        raise AssertionError("Stage 3 already supplied the original witness")

    certificate = build_twobga_certificate(
        request,
        known_answer_artifact=KNOWN_ANSWER,
        sector_solver=forbidden_solver,
    )
    assert certificate["twobga_exact"]["exact"] is True
    assert certificate["passed"] is True
    return certificate


@pytest.fixture
def exact_claim(exact_certificate) -> dict:
    return exact_certificate["claim"]


def _reseal_proof(claim: dict) -> None:
    proof = claim["exact_distance_proof"]
    proof["proof_sha256"] = twobga_screen._canonical_sha256(
        proof,
        omit="proof_sha256",
    )


def test_dispatch_selects_typed_twobga_builder_and_verifier():
    claim = {twobga_screen.TWOBGA_REQUEST_FIELD: {"schema_version": 1}}
    assert dispatch.builder_for_claim(claim) is build_twobga_certificate
    assert dispatch.verifier_for_certificate({
        "certificate_type": CERTIFICATE_TYPE,
    }) is verify_twobga_certificate
    assert CERTIFICATE_TYPE in dispatch.SUPPORTED_CERTIFICATE_TYPES


def test_twobga_certificate_builder_rejects_twisted_geometry_before_request():
    with pytest.raises(ValueError, match="twisted-torus geometry"):
        build_twobga_certificate(
            {
                "ell": 6,
                "m": 6,
                "A_terms": [[0, 0], [1, 0]],
                "B_terms": [[0, 0], [0, 1]],
                "geometry": {
                    "schema_version": 1,
                    "family": "twisted_torus",
                    "twist": 1,
                },
            },
            known_answer_artifact=KNOWN_ANSWER,
        )


def test_twobga_certificate_verifier_rejects_twisted_claim(
    exact_certificate,
):
    forged = copy.deepcopy(exact_certificate)
    forged["claim"]["geometry"] = {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": 1,
    }
    forged["certificate_sha256"] = twobga_certificate._certificate_sha256(
        forged,
    )

    result = verify_twobga_certificate(
        forged,
        known_answer_artifact=KNOWN_ANSWER,
        sector_solver=lambda *args, **kwargs: pytest.fail(
            "domain-invalid certificate reached a solver"
        ),
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False
    assert "twisted-torus geometry" in result["failures"][0]


def test_certificate_verifier_reruns_both_auxiliary_sectors(
    monkeypatch,
    exact_certificate,
):
    calls = []

    def trusted_lower_oracle(checks, detectors, **kwargs):
        calls.append(str(kwargs["sector"]))
        return _bound_evidence(
            checks,
            detectors,
            sector=str(kwargs["sector"]),
            max_weight=int(kwargs["max_weight"]),
            anchors=tuple(kwargs["anchor_indices"]),
            outcome="unsat",
        )

    monkeypatch.setattr(
        twobga_certificate,
        "evaluate_challenge_gate",
        lambda *args, **kwargs: {
            "accepted": True,
            "checks": {"fixture": True},
            "failures": [],
        },
    )
    result = verify_twobga_certificate(
        copy.deepcopy(exact_certificate),
        known_answer_artifact=KNOWN_ANSWER,
        sector_solver=trusted_lower_oracle,
    )

    assert result["passed"] is True
    assert result["replay_complete"] is True
    assert result["distance"] == exact_certificate["claim"]["d"]
    assert result["rerun"]["completed_sectors"] == 2
    assert result["rerun"]["cardinality_encoding"] == "seqcounter"
    assert result["rerun"]["solver"] == "glucose42"
    assert sorted(calls) == ["X", "Z"]
    assert _twobga_expected_lower_decisions(
        exact_certificate,
        replay_checks=result["checks"],
        replay_result=result,
    ) == 2


def test_real_independent_solver_rejects_forged_auxiliary_unsat(
    exact_certificate,
):
    # The fixture's stored Stage-3 UNSAT rows are deliberately synthetic;
    # its actual dressed auxiliary distances are below the claimed threshold.
    result = verify_twobga_certificate(
        copy.deepcopy(exact_certificate),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=5,
        total_timeout=10,
        solver_workers=2,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False
    assert result["checks"]["independent_auxiliary_rerun"] is False
    assert result["rerun"]["completed_sectors"] == 2
    assert {
        item["solver_evidence"]["outcome"]
        for item in result["rerun"]["results"]
    } == {"sat"}


def test_certificate_verifier_fails_closed_on_malformed_nested_objects(
    exact_certificate,
):
    malformed = copy.deepcopy(exact_certificate)
    malformed["known_answer"] = None
    malformed["solver"] = []
    malformed["certificate_sha256"] = (
        twobga_certificate._certificate_sha256(malformed)
    )

    result = verify_twobga_certificate(
        malformed,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=1,
        sector_solver=lambda *args, **kwargs: {
            "outcome": "solver_error",
        },
    )

    assert result["passed"] is False
    assert result["checks"]["known_answer_sha256"] is False


def test_certificate_verifier_fails_closed_on_noncanonical_nan(
    exact_certificate,
):
    malformed = copy.deepcopy(exact_certificate)
    malformed["twobga_exact"]["elapsed_s"] = float("nan")

    result = verify_twobga_certificate(
        malformed,
        known_answer_artifact=KNOWN_ANSWER,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False
    assert result["failure_disposition"]["codes"] == [
        "TWOBGA_CERTIFICATE_SCHEMA_INVALID",
    ]


@pytest.mark.parametrize("tamper", ["theorem", "matrix", "upper-domain"])
def test_typed_proof_tampering_fails_closed(exact_claim, tamper):
    claim = copy.deepcopy(exact_claim)
    proof = claim["exact_distance_proof"]
    if tamper == "theorem":
        proof["theorem_eligibility"]["rank_defects"]["delta_x"] = 1
    elif tamper == "matrix":
        evidence = proof["lower_bound_decisions"][0]["solver_evidence"]
        evidence["instance"]["check_matrix_sha256"] = "0" * 64
        evidence["evidence_sha256"] = twobga_screen._canonical_sha256(
            evidence,
            omit="evidence_sha256",
        )
    else:
        proof["upper_witness"]["domain"] = "auxiliary-subsystem"
    _reseal_proof(claim)

    with pytest.raises(ValueError):
        validate_twobga_exact_proof(claim)


def test_final_gate_dispatches_twobga_proof_and_rejects_resealed_tamper(
    exact_claim,
):
    valid = evaluate_final_gate(
        copy.deepcopy(exact_claim),
        known_answer_artifact=KNOWN_ANSWER,
    )
    assert valid["checks"]["typed_exact_twobga_subsystem_proof"] is True

    tampered_claim = copy.deepcopy(exact_claim)
    tampered_claim["exact_distance_proof"]["upper_witness"][
        "domain"
    ] = "auxiliary-subsystem"
    _reseal_proof(tampered_claim)
    tampered = evaluate_final_gate(
        tampered_claim,
        known_answer_artifact=KNOWN_ANSWER,
    )
    assert tampered["accepted"] is False
    assert tampered["checks"]["typed_exact_twobga_subsystem_proof"] is False


def test_auxiliary_sat_witness_cannot_be_promoted_to_exact(
    monkeypatch,
    tmp_path,
):
    artifact = _screen_artifact(
        monkeypatch,
        tmp_path,
        threshold_only=True,
    )
    request = twobga_screen.claim_from_twobga_artifact(artifact)
    context = twobga_screen.validate_twobga_stage3_artifact(artifact)
    checks, detectors, _ = context["problem"].sector_matrices("X")
    anchors = (0,)
    auxiliary_operator = _find_operator_up_to(
        checks,
        detectors,
        max_weight=int(context["required_distance"]),
        anchors=anchors,
    )
    auxiliary_sat = _bound_evidence(
        checks,
        detectors,
        sector="X",
        max_weight=int(context["required_distance"]),
        anchors=anchors,
        outcome="sat",
        operator=auxiliary_operator,
    )
    monkeypatch.setattr(
        twobga_certificate,
        "evaluate_challenge_gate",
        lambda *args, **kwargs: {
            "accepted": True,
            "checks": {"fixture": True},
            "failures": [],
        },
    )

    certificate = build_twobga_certificate(
        request,
        known_answer_artifact=KNOWN_ANSWER,
        sector_solver=lambda *args, **kwargs: copy.deepcopy(auxiliary_sat),
    )

    assert certificate["twobga_exact"]["upper_attempt"]["solver_evidence"][
        "outcome"
    ] == "sat"
    assert certificate["twobga_exact"]["upper_attempt"][
        "witness_verified"
    ] is False
    assert certificate["twobga_exact"]["exact"] is False
    assert certificate["claim"]["d_is_exact"] is False
    assert "exact_distance_proof" not in certificate["claim"]
    assert certificate["passed"] is False


def test_original_low_witness_is_a_terminal_candidate_rejection(
    monkeypatch,
    tmp_path,
):
    artifact = _screen_artifact(
        monkeypatch,
        tmp_path,
        threshold_only=True,
    )
    request = twobga_screen.claim_from_twobga_artifact(artifact)

    def honest_upper_solver(checks, detectors, **kwargs):
        anchors = tuple(kwargs["anchor_indices"])
        operator = _find_operator_up_to(
            checks,
            detectors,
            max_weight=int(kwargs["max_weight"]) - 1,
            anchors=anchors,
        )
        return _bound_evidence(
            checks,
            detectors,
            sector=str(kwargs["sector"]),
            max_weight=int(kwargs["max_weight"]),
            anchors=anchors,
            outcome="sat",
            operator=operator,
        )

    certificate = build_twobga_certificate(
        request,
        known_answer_artifact=KNOWN_ANSWER,
        sector_solver=honest_upper_solver,
    )

    assert certificate["passed"] is False
    assert certificate["claim"]["stage"] == "twobga_rejected"
    assert certificate["candidate_rejection"]["witness"][
        "witness_verified"
    ] is True
    assert certificate["failure_disposition"]["status"] == "CANDIDATE_REJECTED"
    assert validate_twobga_candidate_rejection(certificate) is True
    assert _terminal_certificate_rejection(certificate) is True
