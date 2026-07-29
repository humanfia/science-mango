"""Focused tests for the resumable Stage 3 to Stage 4 handoff."""

from __future__ import annotations

import json

import numpy as np
import pytest

import scripts.audit_candidate_pool as candidate_pool
import scripts.audit_direction_pool as direction_pool
from evaluation.certificate import _direction_specs, pack_vector
from scripts.audit_direction_pool import (
    annotate_rows,
    candidate_from_stage2,
    screen_selected_candidates,
    select_unresolved,
    threshold_artifacts,
    validate_worker_budget,
)
from scripts.audit_candidate_pool import (
    claim_from_certifiable_stage3_artifact,
    merge_certification_results,
)
from scripts.build_certificate import load_one
from scripts.screen_frontier_candidate import (
    CSS_EXACT_FORMULATION,
    CSS_THRESHOLD_FORMULATION,
    build_candidate_code,
    claim_from_threshold_artifact,
    load_replayable_directions,
    replayable_directions_from_artifact,
    validate_candidate_parameters,
    write_artifact,
)


def _candidate() -> dict:
    return {
        "source": "ibm-72-test",
        "ell": 6,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
        "n": 72,
        "k": 12,
        "required_distance": 7,
        "canonical_digest": "digest-72",
    }


def _fake_unresolved_screen(candidate, **kwargs):
    return {
        "status": "UNRESOLVED",
        "completed_directions": 0,
        "expected_directions": 24,
    }


def _bounded(spec, position: int, max_weight: int = 6) -> dict:
    logical_type, index, check_name, _, target = spec
    return {
        "formulation": CSS_THRESHOLD_FORMULATION,
        "solver": "scipy.optimize.milp",
        "backend": "HiGHS",
        "solver_workers": 1,
        "position": position,
        "logical_type": logical_type,
        "logical_index": index,
        "check_matrix": check_name,
        "target_logical": pack_vector(target),
        "max_weight": max_weight,
        "success": False,
        "status": 2,
        "threshold_infeasible": True,
        "objective": None,
        "operator": None,
    }


def test_stage3_artifact_is_safe_direct_stage4_input(tmp_path):
    candidate = _candidate()
    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    directions = [
        _bounded(spec, position)
        for position, spec in enumerate(_direction_specs(code))
    ]
    output = tmp_path / "stage3.json"
    artifact = write_artifact(
        output,
        candidate,
        directions,
        expected_directions=geometry["expected_directions"],
        threshold_only=True,
        reconstructed_parameters=geometry,
    )

    assert artifact["status"] == "THRESHOLD_PROVEN"
    assert load_one(output, 0) == candidate

    artifact["status"] = "UNRESOLVED"
    output.write_text(json.dumps(artifact))
    with pytest.raises(ValueError, match="THRESHOLD_PROVEN"):
        load_one(output, 0)

    artifact["status"] = "THRESHOLD_PROVEN"
    artifact["directions"][0]["max_weight"] = 5
    output.write_text(json.dumps(artifact))
    with pytest.raises(ValueError, match="non-replayable"):
        load_one(output, 0)


def test_resume_reuses_bound_proof_and_discards_unknown(tmp_path):
    candidate = _candidate()
    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    specs = _direction_specs(code)
    unknown = {
        **_bounded(specs[1], 1),
        "status": 1,
        "threshold_infeasible": False,
    }
    output = tmp_path / "partial.json"
    write_artifact(
        output,
        candidate,
        [_bounded(specs[0], 0), unknown],
        expected_directions=geometry["expected_directions"],
        threshold_only=True,
        reconstructed_parameters=geometry,
    )

    recovered = load_replayable_directions(
        output, candidate, code, threshold_only=True,
    )
    assert [item["position"] for item in recovered] == [0]
    assert recovered[0]["resumed_solver_proof"] is True

    stored = json.loads(output.read_text())
    stored["directions"][0]["target_logical"] = pack_vector(
        np.zeros(72, dtype=np.uint8),
    )
    output.write_text(json.dumps(stored))
    assert load_replayable_directions(
        output, candidate, code, threshold_only=True,
    ) == []


def test_stage3_rejects_fractional_parameters_and_unbound_solver_metadata(
    tmp_path,
):
    candidate = _candidate()
    code = build_candidate_code(candidate)
    with pytest.raises(ValueError, match="integer n"):
        validate_candidate_parameters({**candidate, "n": 72.5}, code)

    geometry = validate_candidate_parameters(candidate, code)
    direction = _bounded(_direction_specs(code)[0], 0)
    direction.pop("backend")
    output = tmp_path / "unbound.json"
    write_artifact(
        output,
        candidate,
        [direction],
        expected_directions=geometry["expected_directions"],
        threshold_only=True,
        reconstructed_parameters=geometry,
    )
    assert load_replayable_directions(
        output, candidate, code, threshold_only=True,
    ) == []


def test_resume_accepts_zero_gap_exact_direction(monkeypatch):
    class FakeCode:
        num_qudits = 10
        dimension = 1

    target0 = np.array([1] + [0] * 9, dtype=np.uint8)
    target1 = np.array([0, 1] + [0] * 8, dtype=np.uint8)
    specs = [
        ("Z", 0, "hx", np.zeros((1, 10), dtype=np.uint8), target0),
        ("X", 0, "hz", np.zeros((1, 10), dtype=np.uint8), target1),
    ]
    monkeypatch.setattr(
        "scripts.screen_frontier_candidate.minimum_winning_distance",
        lambda n, k: 3,
    )
    monkeypatch.setattr(
        "scripts.screen_frontier_candidate._direction_specs", lambda code: specs,
    )
    monkeypatch.setattr(
        "scripts.screen_frontier_candidate.verify_css_witness",
        lambda *args: [],
    )
    monkeypatch.setattr(
        "scripts.screen_frontier_candidate.verify_direction_evidence",
        lambda *args: [],
    )
    candidate = {"n": 10, "k": 1, "required_distance": 3}
    geometry = validate_candidate_parameters(candidate, FakeCode())
    exact = {
        "formulation": CSS_EXACT_FORMULATION,
        "solver": "scipy.optimize.milp",
        "backend": "HiGHS",
        "solver_workers": 1,
        "position": 0,
        "logical_type": "Z",
        "logical_index": 0,
        "check_matrix": "hx",
        "target_logical": pack_vector(target0),
        "success": True,
        "status": 0,
        "objective": 3,
        "mip_dual_bound": 3.0,
        "mip_gap": 0.0,
        "operator": pack_vector(target0),
    }
    artifact = {
        "schema_version": 2,
        "gate": "qldpc-frontier-threshold-screen",
        "candidate": candidate,
        "threshold_only": False,
        "required_distance": 3,
        "expected_directions": 2,
        "completed_directions": 1,
        "reconstructed_parameters": geometry,
        "directions": [exact],
    }
    recovered = replayable_directions_from_artifact(
        artifact, candidate, FakeCode(), threshold_only=False,
    )
    assert recovered[0]["resumed_zero_gap_exact"] is True


def test_stage3_pool_selects_only_unresolved_and_enforces_budget(tmp_path):
    base = _candidate()
    row = {
        **base,
        "triage_identity": {"canonical_digest": "digest/unsafe"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }
    selected, counts = select_unresolved([
        row,
        row,
        {**row, "campaign_audit": {"status": "REJECTED"}},
    ])
    assert counts["selected_candidates"] == 1
    assert counts["duplicate_digests_skipped"] == 1
    assert counts["unselected_unresolved_candidates"] == 0
    assert counts["selection_exhausted"] is True
    assert candidate_from_stage2(row)["canonical_digest"] == "digest/unsafe"
    validate_worker_budget(2, 4, 8)
    with pytest.raises(ValueError, match="exceeds"):
        validate_worker_budget(3, 4, 8)

    results = screen_selected_candidates(
        selected,
        tmp_path,
        timeout=1,
        candidate_workers=1,
        direction_workers=2,
        threshold_only=True,
        resume=True,
        screener=_fake_unresolved_screen,
    )
    assert results[0]["status"] == "UNRESOLVED"
    assert "digest/unsafe" not in results[0]["artifact_path"]


def test_stage3_top_and_duplicate_annotations_are_explicit():
    first = {
        **_candidate(),
        "triage_identity": {"canonical_digest": "duplicate"},
        "campaign_audit": {
            "canonical_digest": "duplicate",
            "status": "UNRESOLVED",
        },
    }
    duplicate = dict(first)
    second = {
        **_candidate(),
        "triage_identity": {"canonical_digest": "second"},
        "campaign_audit": {
            "canonical_digest": "second",
            "status": "UNRESOLVED",
        },
    }

    selected, counts = select_unresolved([first, duplicate, second], top=1)
    annotated = annotate_rows(
        [first, duplicate, second],
        selected,
        [{"canonical_digest": "duplicate", "status": "UNRESOLVED"}],
    )

    assert counts["selected_candidates"] == 1
    assert counts["duplicate_digests_skipped"] == 1
    assert counts["unselected_unresolved_candidates"] == 1
    assert counts["selection_exhausted"] is False
    duplicate_rows = [
        row
        for row in annotated
        if row["triage_identity"]["canonical_digest"] == "duplicate"
    ]
    assert (
        sum(row["campaign_direction_selected"] is True for row in duplicate_rows)
        == 1
    )
    assert sum("campaign_direction_audit" in row for row in duplicate_rows) == 1


def test_stage3_pool_isolates_outer_worker_and_artifact_failures(
    tmp_path, monkeypatch,
):
    monkeypatch.setattr(
        direction_pool,
        "start_isolated_call",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            RuntimeError("worker crashed")
        ),
    )
    results = screen_selected_candidates(
        [("digest", _candidate())],
        tmp_path,
        timeout=1,
        candidate_workers=2,
        direction_workers=1,
        threshold_only=True,
        resume=True,
    )
    assert results[0]["status"] == "ERROR"
    assert "worker crashed" in results[0]["error"]

    broken = tmp_path / "broken.json"
    broken.write_text("not json")
    artifacts, failures = threshold_artifacts([{
        "canonical_digest": "digest",
        "status": "THRESHOLD_PROVEN",
        "artifact_path": str(broken),
    }])
    assert artifacts == []
    assert "artifact validation failed" in failures["digest"]


def test_exact_stage3_artifact_requires_uncapped_strict_replay(monkeypatch):
    candidate = _candidate()
    artifact = {
        "gate": "qldpc-frontier-threshold-screen",
        "status": "EXACT_PROVEN",
        "threshold_only": False,
        "candidate": candidate,
    }
    validated = []

    def strict_validator(value):
        validated.append(value)
        assert value["status"] == "THRESHOLD_PROVEN"
        assert value["threshold_only"] is False
        return candidate

    monkeypatch.setattr(
        candidate_pool,
        "claim_from_threshold_artifact",
        strict_validator,
    )

    assert claim_from_certifiable_stage3_artifact(artifact) == candidate
    assert artifact["status"] == "EXACT_PROVEN"
    assert len(validated) == 1

    with pytest.raises(ValueError, match="threshold_only=false"):
        claim_from_certifiable_stage3_artifact({
            **artifact,
            "threshold_only": True,
        })


def test_stage3_exact_cli_hands_artifact_to_certificate_and_merges_result(
    tmp_path, monkeypatch,
):
    candidate = _candidate()
    row = {
        **candidate,
        "triage_identity": {"canonical_digest": "digest-72"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    manifest = tmp_path / "stage4.jsonl"
    state_dir = tmp_path / "state"
    artifact_path = state_dir / "exact.json"
    exact_artifact = {
        "gate": "qldpc-frontier-threshold-screen",
        "status": "EXACT_PROVEN",
        "threshold_only": False,
        "candidate": candidate,
    }
    ranked_input.write_text(json.dumps(row) + "\n")
    artifact_path.parent.mkdir(parents=True)
    artifact_path.write_text(json.dumps(exact_artifact) + "\n")

    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        lambda *args, **kwargs: [{
            "canonical_digest": "digest-72",
            "status": "EXACT_PROVEN",
            "artifact_path": str(artifact_path),
            "completed_directions": 24,
            "expected_directions": 24,
        }],
    )
    monkeypatch.setattr(
        candidate_pool,
        "claim_from_threshold_artifact",
        lambda artifact: candidate,
    )
    monkeypatch.setattr(
        candidate_pool,
        "certify_selected_candidates",
        lambda artifacts, config, **kwargs: {
            "digest-72": {
                "attempted": True,
                "certificate_exact": True,
                "certificate_passed": True,
                "verification_passed": True,
            },
        },
    )

    assert direction_pool.main([
        str(ranked_input),
        "--state-dir",
        str(state_dir),
        "--ranked-output",
        str(ranked_output),
        "--summary-output",
        str(summary_output),
        "--stage4-manifest",
        str(manifest),
        "--exact",
        "--certify",
    ]) == 0

    summary = json.loads(summary_output.read_text())
    assert summary["threshold_only"] is False
    assert summary["stage4_candidates"] == 1
    assert summary["certified_wins"] == 1
    assert summary["results"][0]["status"] == "EXACT_PROVEN"
    assert summary["results"][0]["certificate"]["certificate_passed"] is True
    assert json.loads(manifest.read_text())["status"] == "EXACT_PROVEN"


def test_certificate_merge_preserves_threshold_behavior_and_accepts_exact():
    certification = {
        "attempted": True,
        "certificate_exact": True,
        "certificate_passed": True,
        "verification_passed": True,
    }
    merged = merge_certification_results(
        [
            {"canonical_digest": "threshold", "status": "THRESHOLD_PROVEN"},
            {"canonical_digest": "exact", "status": "EXACT_PROVEN"},
            {"canonical_digest": "pending", "status": "UNRESOLVED"},
        ],
        {
            "threshold": certification,
            "exact": certification,
        },
        certify=True,
    )

    assert merged[0]["certificate"] == certification
    assert merged[1]["certificate"] == certification
    assert "certificate" not in merged[2]
