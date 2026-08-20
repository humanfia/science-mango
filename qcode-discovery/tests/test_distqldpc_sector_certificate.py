"""Focused tests for the typed DistQLDPC exact certificate path."""

from __future__ import annotations

from copy import deepcopy
from types import SimpleNamespace

import numpy as np
import pytest

from evaluation import distqldpc_sector_adapter as adapter
from evaluation import distqldpc_sector_certificate as certificate_module
from evaluation import sector_certificate


def _fixture(monkeypatch):
    hx = np.asarray([[1, 1, 0, 0]], dtype=np.uint8)
    hz = np.asarray([[0, 0, 1, 1]], dtype=np.uint8)
    lx = np.asarray([[1, 0, 0, 0]], dtype=np.uint8)
    lz = np.asarray([[0, 0, 1, 0]], dtype=np.uint8)
    code = SimpleNamespace(num_qudits=4, dimension=2)
    candidate = {
        "ell": 1,
        "m": 2,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 4,
        "k": 2,
        "required_distance": 2,
        "canonical_digest": "typed-distqldpc-certificate-test",
    }
    detector = {"verified": True, "report_sha256": "b" * 64}
    translation = {
        "verified": True,
        "method": "test-translation",
        "orbit_representatives": [0, 2],
    }
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "d" * 64,
    }
    identity = adapter.stage3_distqldpc_checkpoint_identity(
        candidate,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=None,
        xz_sector_isometry=isometry,
    )
    evidence = {"outcome": "exact", "exact_distance": 2}
    lower = {
        "sector": "XZ",
        "partition_index": None,
        "anchor_cube": None,
        "cardinality_mode": "mto",
        "checkpoint_identity": identity,
        "solver_evidence": evidence,
    }
    upper = {
        "sector": "X",
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": {"outcome": "sat", "objective": 2},
    }
    request = {
        "coverage_mode": "global",
        "requested_coverage_mode": "first-nonzero",
        "requested_lower_backend": "distqldpc",
        "lower_bound_backend": "distqldpc",
        "lower_bound_threshold": 1,
        "lower_bound_decisions": [lower],
        "distqldpc_exact_distances": [2],
        "distqldpc_exact_decisions": [lower],
        "distqldpc_lower_decisions": [lower],
        "distqldpc_conflict": False,
        "distqldpc_conflict_details": None,
        "low_witnesses": [],
        "upper_witness": upper,
        "logical_detector": detector,
        "translation_symmetry": translation,
        "construction_symmetry": None,
        "use_translation_anchors": True,
        "use_construction_anchors": False,
        "xz_sector_isometry": isometry,
        "anchor_cover_cubes": None,
        "stage3_status": "EXACT_PROVEN",
        "stage3_artifact_sha256": "a" * 64,
        "required_distance": 2,
    }
    source_claim = {
        **candidate,
        sector_certificate.REQUEST_FIELD: request,
    }
    context = {
        "claim": dict(candidate),
        "code": code,
        "hx": hx,
        "hz": hz,
        "lx": lx,
        "lz": lz,
        "n": 4,
        "k": 2,
        "target_mode": "gist",
        "target": None,
        "required_distance": 2,
        "admissibility_report": None,
    }

    monkeypatch.setattr(
        certificate_module, "_candidate_context", lambda _claim: dict(context),
    )
    monkeypatch.setattr(
        certificate_module,
        "_fresh_reports",
        lambda _context, _request: (detector, translation, (0, 2)),
    )
    monkeypatch.setattr(
        sector_certificate, "_valid_upper_witness", lambda *_a, **_k: True,
    )
    monkeypatch.setattr(
        sector_certificate,
        "check_code_novelty",
        lambda *_a, **_k: {
            "checked": True,
            "novel": True,
            "canonical_digest": candidate["canonical_digest"],
            "registry_sha256": "registry-test",
        },
    )
    monkeypatch.setattr(
        certificate_module,
        "classify_target_win",
        lambda *_a, **_k: {"passed": True, "fom": 2.0},
    )
    monkeypatch.setattr(
        certificate_module,
        "evaluate_challenge_gate",
        lambda *_a, **_k: {
            "schema_version": 1,
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": {
                certificate_module.LEGACY_PROOF_CHECK: False,
                "css_bb_candidate": True,
                "structural_audit_present": True,
                "structural_audit_reproduced": True,
                "expanded_registry_novel": True,
            },
            "failures": [certificate_module.LEGACY_PROOF_CHECK],
        },
    )
    return {
        "source_claim": source_claim,
        "candidate": candidate,
        "context": context,
        "lower": lower,
        "detector": detector,
        "translation": translation,
        "isometry": isometry,
    }


def test_build_is_static_and_verify_runs_one_certificate_bound_lane(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(monkeypatch)
    verifier_calls = []

    def exact_verifier(evidence, *_args, **kwargs):
        verifier_calls.append(("exact", evidence, kwargs))
        return []

    def lower_verifier(evidence, *_args, **kwargs):
        verifier_calls.append(("lower", evidence, kwargs))
        return []

    monkeypatch.setattr(
        adapter, "verify_distqldpc_exact_evidence", exact_verifier,
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lower_verifier,
    )
    known = tmp_path / "known.json"
    known.write_text("{}", encoding="utf-8")
    solver_calls = []

    def fake_solver(*_args, **kwargs):
        solver_calls.append(kwargs)
        return {"outcome": "exact", "exact_distance": 2}

    built = certificate_module.build_distqldpc_sector_certificate(
        fixture["source_claim"],
        known_answer_artifact=known,
    )
    assert built["passed"] is True
    assert built["build"] == {
        "mode": "static-no-rerun",
        "solver_invocations": 0,
        "independent_replay_complete": False,
    }
    assert solver_calls == []
    assert built["distqldpc_exact"]["coverage_mode"] == "global"
    assert (
        built["distqldpc_exact"]["requested_coverage_mode"]
        == "first-nonzero"
    )
    assert built["distqldpc_exact"]["completed_lower_decisions"] == 1
    assert built["claim"]["exact_distance_proof"]["proof_type"] == (
        certificate_module.PROOF_TYPE
    )
    assert certificate_module.LEGACY_PROOF_CHECK not in (
        built["final_gate"]["checks"]
    )
    assert built["final_gate"]["checks"][
        certificate_module.TYPED_PROOF_CHECK
    ] is True

    replay = certificate_module.verify_distqldpc_sector_certificate(
        built,
        known_answer_artifact=known,
        timeout=10,
        distqldpc_solver=fake_solver,
    )
    assert replay["passed"] is True
    assert replay["replay_complete"] is True
    assert replay["typed_lower"] is True
    assert replay["upper"] is True
    assert replay["distqldpc_decisions_verified"] == 1
    assert replay["distqldpc_decisions_total"] == 1
    assert "sat_rerun" not in replay["checks"]
    assert len(solver_calls) == 1
    fresh_identity = solver_calls[0]["checkpoint_identity"]
    assert fresh_identity["phase"] == "verify-lower-distqldpc"
    assert fresh_identity["certificate_sha256"] == built[
        "certificate_sha256"
    ]
    assert fresh_identity != fixture["lower"]["checkpoint_identity"]
    # Build and static verification each explicitly call exact and lower;
    # fresh verification then calls stored lower plus fresh exact and lower.
    assert [item[0] for item in verifier_calls].count("exact") >= 3
    assert [item[0] for item in verifier_calls].count("lower") >= 4


def test_explicit_exact_replay_failure_rejects_static_build(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(monkeypatch)
    monkeypatch.setattr(
        adapter,
        "verify_distqldpc_exact_evidence",
        lambda *_a, **_k: ["exact evidence rejected"],
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lambda *_a, **_k: [],
    )
    known = tmp_path / "known.json"
    known.write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="exact evidence rejected"):
        certificate_module.build_distqldpc_sector_certificate(
            fixture["source_claim"],
            known_answer_artifact=known,
        )


def test_requested_and_effective_coverage_modes_are_not_interchangeable(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(monkeypatch)
    monkeypatch.setattr(
        adapter, "verify_distqldpc_exact_evidence", lambda *_a, **_k: [],
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lambda *_a, **_k: [],
    )
    known = tmp_path / "known.json"
    known.write_text("{}", encoding="utf-8")
    forged = deepcopy(fixture["source_claim"])
    forged[sector_certificate.REQUEST_FIELD][
        "requested_coverage_mode"
    ] = "global"
    with pytest.raises(ValueError, match="checkpoint identity"):
        certificate_module.build_distqldpc_sector_certificate(
            forged,
            known_answer_artifact=known,
        )


def test_extended_final_gate_preserves_every_nonproof_failure(monkeypatch):
    fixture = _fixture(monkeypatch)
    row = {
        **fixture["candidate"],
        "d": 2,
        "fom": 2.0,
        "d_is_exact": True,
        "exact_distance_proof": {"proof_type": certificate_module.PROOF_TYPE},
    }
    monkeypatch.setattr(
        certificate_module,
        "validate_distqldpc_exact_proof",
        lambda _row: fixture["context"],
    )
    monkeypatch.setattr(
        certificate_module,
        "evaluate_challenge_gate",
        lambda *_a, **_k: {
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": {
                certificate_module.LEGACY_PROOF_CHECK: False,
                "unrelated_nonproof_check": False,
            },
            "failures": [
                certificate_module.LEGACY_PROOF_CHECK,
                "unrelated_nonproof_check",
            ],
        },
    )
    gate = certificate_module.evaluate_distqldpc_final_gate(
        row,
        known_answer_artifact="unused-by-mock.json",
    )
    assert gate["accepted"] is False
    assert certificate_module.LEGACY_PROOF_CHECK not in gate["checks"]
    assert gate["checks"][certificate_module.TYPED_PROOF_CHECK] is True
    assert gate["failures"] == ["unrelated_nonproof_check"]


def test_no_rerun_is_explicitly_incomplete(tmp_path, monkeypatch):
    fixture = _fixture(monkeypatch)
    monkeypatch.setattr(
        adapter, "verify_distqldpc_exact_evidence", lambda *_a, **_k: [],
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lambda *_a, **_k: [],
    )
    known = tmp_path / "known.json"
    known.write_text("{}", encoding="utf-8")
    built = certificate_module.build_distqldpc_sector_certificate(
        fixture["source_claim"],
        known_answer_artifact=known,
    )
    replay = certificate_module.verify_distqldpc_sector_certificate(
        built,
        known_answer_artifact=known,
        rerun=False,
    )
    assert replay["passed"] is False
    assert replay["replay_complete"] is False
    assert replay["checks"]["distqldpc_rerun"] is False
    assert replay["distqldpc_rerun"] is None
