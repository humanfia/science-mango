"""Focused tests for typed DistQLDPC Stage-3/Stage-4 replay."""

from __future__ import annotations

import hashlib
import json

import numpy as np

from evaluation.admissibility_policy import css_w6_admissibility_binding
from evaluation import distqldpc_sector_adapter as adapter
from evaluation.target_policy import TARGET_MODE_SCALAR_13_INCLUSIVE
from scripts import screen_frontier_sat as stage3


def _sha(value) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()


def _context():
    candidate = {
        "canonical_digest": "typed-distqldpc-candidate",
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": {
            "mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
            "binding_sha256": "a" * 64,
        },
        "admissibility": css_w6_admissibility_binding(),
    }
    detector = {"verified": True, "report_sha256": "b" * 64}
    translation = {
        "verified": True,
        "method": "test-translation",
        "orbit_representatives": [0, 7],
    }
    construction = {"verified": True, "report_sha256": "c" * 64}
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "d" * 64,
    }
    matrices = tuple(
        np.zeros((1, 2), dtype=np.uint8) for _ in range(4)
    )
    return candidate, detector, translation, construction, isometry, matrices


def _source_decision():
    candidate, detector, translation, construction, isometry, _ = _context()
    identity = adapter.stage3_distqldpc_checkpoint_identity(
        candidate,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
    )
    evidence = {"outcome": "exact", "exact_distance": 3}
    return {
        "sector": "XZ",
        "partition_index": None,
        "anchor_cube": None,
        "cardinality_mode": "mto",
        "checkpoint_identity": identity,
        "solver_evidence": evidence,
    }


def test_stage3_identity_exactly_matches_production_builder():
    candidate, detector, translation, construction, isometry, _ = _context()
    expected = stage3.distqldpc_stage3_checkpoint_identity(
        candidate,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
    )
    actual = adapter.stage3_distqldpc_checkpoint_identity(
        candidate,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
    )
    assert actual == expected


def test_static_replay_uses_official_lower_verifier_and_rejects_tampering(
    monkeypatch,
):
    candidate, detector, translation, construction, isometry, matrices = _context()
    decision = _source_decision()
    calls = []

    def lower_verifier(evidence, *args, **kwargs):
        calls.append((evidence, args, kwargs))
        assert kwargs["max_weight"] == 2
        assert kwargs["cardinality_mode"] == "mto"
        assert kwargs["expected_checkpoint_identity"] == decision[
            "checkpoint_identity"
        ]
        return []

    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lower_verifier,
    )
    replay = adapter.replay_stage3_distqldpc_decisions(
        [decision],
        candidate=candidate,
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
        hx=matrices[0], hz=matrices[1], lx=matrices[2], lz=matrices[3],
        max_weight=2,
    )
    assert replay["verified"] is True
    assert replay["exact_distance"] == 3
    assert replay["decisions"] == [decision]
    assert len(calls) == 1

    forged = {**decision, "checkpoint_identity": {
        **decision["checkpoint_identity"],
        "candidate_digest": "different-candidate",
    }}
    rejected = adapter.replay_stage3_distqldpc_decisions(
        [forged],
        candidate=candidate,
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
        hx=matrices[0], hz=matrices[1], lx=matrices[2], lz=matrices[3],
        max_weight=2,
    )
    assert rejected["verified"] is False
    assert rejected["decisions"] == []
    assert any("checkpoint identity" in item for item in rejected["failures"])
    assert len(calls) == 1


def test_certificate_identity_is_distinct_and_binds_stage3_source():
    candidate, detector, translation, _construction, isometry, _ = _context()
    source = _source_decision()["checkpoint_identity"]
    identity = adapter.certificate_bound_distqldpc_checkpoint_identity(
        certificate_type="qldpc-css-bb-sector-distqldpc-exact",
        certificate_sha256="e" * 64,
        candidate=candidate,
        cardinality_mode="mto",
        required_distance=3,
        exact_distance=3,
        max_weight=2,
        logical_detector=detector,
        translation_symmetry=translation,
        xz_sector_isometry=isometry,
        source_stage3_checkpoint_identity=source,
    )
    assert identity != source
    assert identity["phase"] == "verify-lower-distqldpc"
    assert identity["certificate_sha256"] == "e" * 64
    assert identity["source_stage3_checkpoint_identity_sha256"] == _sha(source)
    assert identity["translation_symmetry_sha256"] == _sha(translation)


def test_fresh_rerun_gets_new_identity_and_requires_exact_and_lower_replay(
    monkeypatch,
):
    candidate, detector, translation, construction, isometry, matrices = _context()
    source = _source_decision()
    solver_calls = []
    verifier_calls = []

    def lower_verifier(evidence, *_args, **kwargs):
        verifier_calls.append(("lower", evidence, kwargs))
        return []

    def exact_verifier(evidence, *_args, **kwargs):
        verifier_calls.append(("exact", evidence, kwargs))
        return []

    def fake_solver(*_args, **kwargs):
        solver_calls.append(kwargs)
        return {"outcome": "exact", "exact_distance": 3}

    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lower_verifier,
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_exact_evidence", exact_verifier,
    )
    report = adapter.rerun_certificate_bound_distqldpc_lower(
        source,
        certificate_type="qldpc-css-bb-sector-distqldpc-exact",
        certificate_sha256="e" * 64,
        candidate=candidate,
        coverage_mode="first-nonzero",
        required_distance=3,
        exact_distance=3,
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
        hx=matrices[0], hz=matrices[1], lx=matrices[2], lz=matrices[3],
        timeout=10,
        solver=fake_solver,
    )
    assert report["verified"] is True
    assert len(solver_calls) == 1
    fresh_identity = solver_calls[0]["checkpoint_identity"]
    assert fresh_identity == report["checkpoint_identity"]
    assert fresh_identity != source["checkpoint_identity"]
    assert fresh_identity["phase"] == "verify-lower-distqldpc"
    # Once for stored Stage 3, then once each for fresh exact and fresh lower.
    assert [item[0] for item in verifier_calls] == ["lower", "exact", "lower"]
    assert all(
        item[2]["expected_checkpoint_identity"] == fresh_identity
        for item in verifier_calls[1:]
    )


def test_fresh_rerun_fails_closed_on_distance_change(monkeypatch):
    candidate, detector, translation, construction, isometry, matrices = _context()
    source = _source_decision()
    monkeypatch.setattr(
        adapter, "verify_distqldpc_lower_evidence", lambda *_a, **_k: [],
    )
    monkeypatch.setattr(
        adapter, "verify_distqldpc_exact_evidence", lambda *_a, **_k: [],
    )
    report = adapter.rerun_certificate_bound_distqldpc_lower(
        source,
        certificate_type="qldpc-css-bb-sector-distqldpc-exact",
        certificate_sha256="e" * 64,
        candidate=candidate,
        coverage_mode="first-nonzero",
        required_distance=3,
        exact_distance=3,
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=construction,
        xz_sector_isometry=isometry,
        hx=matrices[0], hz=matrices[1], lx=matrices[2], lz=matrices[3],
        timeout=10,
        solver=lambda *_a, **_k: {"outcome": "exact", "exact_distance": 4},
    )
    assert report["verified"] is False
    assert "fresh exact distance does not match certificate" in report["failures"]
