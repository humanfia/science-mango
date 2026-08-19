"""Focused tests for the resumable Stage 3 to Stage 4 handoff."""

from __future__ import annotations

import json

import numpy as np
import pytest

import scripts.audit_candidate_pool as candidate_pool
import scripts.audit_direction_pool as direction_pool
from evaluation.certificate import _direction_specs, pack_vector
from evaluation.target_policy import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    target_binding,
)
from scripts.audit_direction_pool import (
    _candidate_wall_timeout,
    _expected_proof_units,
    _screen_one,
    annotate_rows,
    artifact_state_path,
    candidate_from_stage2,
    screen_selected_candidates,
    select_unresolved,
    prioritize_resume_candidates,
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


def test_stage3_jsonl_reader_rejects_invalid_unterminated_tail(tmp_path):
    path = tmp_path / "stage2-ranked.jsonl"
    row = {"canonical_digest": "complete"}
    path.write_text(json.dumps(row) + "\n" + '{"partial":')

    with pytest.raises(ValueError, match="invalid JSON"):
        direction_pool.read_ranked_jsonl(path)

    path.write_text(json.dumps(row))
    assert direction_pool.read_ranked_jsonl(path) == [row]


def test_stage3_handoff_copies_and_validates_scalar_target():
    target = target_binding(72, 12, TARGET_MODE_SCALAR)
    row = {
        **_candidate(),
        "required_distance": target["required_distance"],
        "target_mode": TARGET_MODE_SCALAR,
        "target": target,
        "campaign_audit": {"status": "UNRESOLVED"},
    }

    candidate = candidate_from_stage2(
        row,
        target_mode=TARGET_MODE_SCALAR,
    )
    assert candidate["target_mode"] == TARGET_MODE_SCALAR
    assert candidate["target"] == target
    assert candidate["required_distance"] == 9

    with pytest.raises(ValueError, match="required_distance"):
        candidate_from_stage2(
            {**row, "required_distance": 7},
            target_mode=TARGET_MODE_SCALAR,
        )
    with pytest.raises(ValueError, match="target_mode"):
        candidate_from_stage2(row, target_mode=TARGET_MODE_GIST)


def test_stage3_handoff_accepts_authoritative_fom13_target():
    target = target_binding(210, 10, TARGET_MODE_SCALAR_13_INCLUSIVE)
    row = {
        **_candidate(),
        "n": 210,
        "k": 10,
        "required_distance": target["required_distance"],
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": target,
        "campaign_audit": {"status": "UNRESOLVED"},
    }

    candidate = candidate_from_stage2(
        row,
        target_mode=TARGET_MODE_SCALAR_13_INCLUSIVE,
    )

    assert candidate["target_mode"] == TARGET_MODE_SCALAR_13_INCLUSIVE
    assert candidate["target"] == target
    assert candidate["required_distance"] == 17


def test_stage3_legacy_handoff_is_explicitly_bound_to_gist():
    row = {
        **_candidate(),
        "campaign_audit": {"status": "UNRESOLVED"},
    }

    candidate = candidate_from_stage2(row)

    assert candidate["target_mode"] == TARGET_MODE_GIST
    assert candidate["target"] == target_binding(72, 12, TARGET_MODE_GIST)


def test_stage3_scalar_solver_preflight_rejects_stale_binding():
    candidate = {
        **_candidate(),
        "required_distance": 9,
        "target_mode": TARGET_MODE_SCALAR,
        "target": target_binding(72, 12, TARGET_MODE_SCALAR),
    }
    code = build_candidate_code(candidate)
    assert validate_candidate_parameters(candidate, code)[
        "required_distance"
    ] == 9

    stale = {
        **candidate,
        "target": target_binding(72, 12, TARGET_MODE_GIST),
    }
    with pytest.raises(ValueError, match="target binding mode"):
        validate_candidate_parameters(stale, code)


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


def test_resume_discards_legacy_zero_objective_threshold_formulation(tmp_path):
    candidate = _candidate()
    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    legacy = {
        **_bounded(_direction_specs(code)[0], 0),
        "formulation": "css-logical-threshold-feasibility-v1",
    }
    output = tmp_path / "legacy-threshold.json"
    write_artifact(
        output,
        candidate,
        [legacy],
        expected_directions=geometry["expected_directions"],
        threshold_only=True,
        reconstructed_parameters=geometry,
    )

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
        "scripts.screen_frontier_candidate.target_binding",
        lambda n, k, mode: {"required_distance": 3},
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


def test_sat_stage3_uses_independent_state_and_budgets_all_proof_units(
    tmp_path,
):
    candidate = _candidate()
    captured = {}

    def fake_sat_screen(_candidate, *, output, **_kwargs):
        captured["output"] = output
        captured["kwargs"] = _kwargs
        return {
            "status": "UNRESOLVED",
            "terminal_units": 7,
            "expected_units": 26,
        }

    result = _screen_one(
        "digest-72",
        candidate,
        tmp_path,
        timeout=10,
        direction_workers=5,
        threshold_only=False,
        resume=True,
        backend="sat-sectors",
        sat_incremental_conflict_budget=25000,
        screener=fake_sat_screen,
    )

    expected_path = artifact_state_path(
        tmp_path, "digest-72", "sat-sectors",
    )
    assert captured["output"] == expected_path
    assert captured["kwargs"]["cardinality_encoding"] == "kmtotalizer"
    assert captured["kwargs"]["incremental_conflict_budget"] == 25000
    assert expected_path.parent.name == "sat-sectors"
    assert result["backend"] == "sat-sectors"
    assert result["sat_cardinality_encoding"] == "kmtotalizer"
    assert result["sat_incremental_conflict_budget"] == 25000
    assert result["expected_proof_units"] == 26
    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=5,
        direction_hard_timeout=None,
        candidate_hard_timeout=None,
        backend="sat-sectors",
    ) == 102
    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=5,
        direction_hard_timeout=None,
        candidate_hard_timeout=None,
        backend="legacy-directions",
    ) == 87

    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=5,
        direction_hard_timeout=None,
        candidate_hard_timeout=None,
        backend="sat-sectors",
        termination_grace=7,
    ) == 126
    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=5,
        direction_hard_timeout=None,
        candidate_hard_timeout=None,
        backend="legacy-directions",
        termination_grace=7,
    ) == 109
    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=5,
        direction_hard_timeout=12,
        candidate_hard_timeout=None,
        backend="sat-sectors",
        termination_grace=7,
    ) == 138

    captured.clear()
    overridden = _screen_one(
        "digest-72",
        candidate,
        tmp_path,
        timeout=10,
        direction_workers=5,
        threshold_only=False,
        resume=True,
        backend="sat-sectors",
        sat_cardinality_encoding="native-minicard",
        screener=fake_sat_screen,
    )
    assert captured["kwargs"]["cardinality_encoding"] == "native-minicard"
    assert overridden["sat_cardinality_encoding"] == "native-minicard"


def test_distqldpc_lower_backend_is_forwarded_to_sat_screen(tmp_path):
    candidate = _candidate()
    captured = {}
    executable = tmp_path / "distqldpc"

    def fake_sat_screen(_candidate, *, output, **kwargs):
        captured["output"] = output
        captured["kwargs"] = kwargs
        return {
            "status": "UNRESOLVED",
            "terminal_units": 1,
            "expected_units": 31,
        }

    result = _screen_one(
        "digest-72",
        candidate,
        tmp_path,
        timeout=10,
        direction_workers=6,
        threshold_only=False,
        resume=True,
        backend="sat-sectors",
        sat_lower_backend="distqldpc",
        sat_distqldpc_exe=executable,
        screener=fake_sat_screen,
    )

    assert captured["kwargs"]["lower_backend"] == "distqldpc"
    assert captured["kwargs"]["distqldpc_exe"] == executable
    assert result["sat_lower_backend"] == "distqldpc"
    assert result["sat_distqldpc_exe"] == str(executable.resolve())
    assert result["completed_proof_units"] == 1
    assert result["expected_proof_units"] == 31

    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=6,
        direction_hard_timeout=None,
        candidate_hard_timeout=None,
        backend="sat-sectors",
        sat_lower_backend="distqldpc",
    ) == 102
    assert _candidate_wall_timeout(
        candidate,
        timeout=10,
        direction_workers=6,
        direction_hard_timeout=None,
        candidate_hard_timeout=120,
        backend="sat-sectors",
        sat_lower_backend="distqldpc",
        termination_grace=3,
    ) == 128


    with pytest.raises(ValueError, match="requires backend=sat-sectors"):
        screen_selected_candidates(
            [], tmp_path, timeout=1, candidate_workers=1,
            direction_workers=1, threshold_only=True, resume=True,
            backend="legacy-directions", sat_lower_backend="distqldpc",
        )


def test_sat_unit_reduction_requires_fresh_geometry_isometry_replay():
    candidate = _candidate()
    assert _expected_proof_units(candidate, "sat-sectors") == 26
    stale = {**candidate, "n": 74}
    assert _expected_proof_units(stale, "sat-sectors") == 52


def test_twobga_stage3_has_independent_state_and_fail_closed_preflight(
    tmp_path,
):
    candidate = _candidate()
    captured = {}

    def fake_twobga_screen(_candidate, *, output, **kwargs):
        captured["output"] = output
        captured["kwargs"] = kwargs
        return {
            "status": "INELIGIBLE",
            "terminal_units": 0,
            "expected_units": 0,
        }

    result = _screen_one(
        "digest-72",
        candidate,
        tmp_path,
        timeout=10,
        direction_workers=3,
        threshold_only=False,
        resume=True,
        backend="twobga-aux",
        screener=fake_twobga_screen,
    )
    path = artifact_state_path(tmp_path, "digest-72", "twobga-aux")
    assert captured["output"] == path
    assert path.parent.name == "twobga-aux"
    assert captured["kwargs"]["cardinality_encoding"] == "kmtotalizer"
    assert result == {
        "canonical_digest": "digest-72",
        "backend": "twobga-aux",
        "status": "INELIGIBLE",
        "artifact_path": str(path),
        "sat_cardinality_encoding": "kmtotalizer",
        "completed_proof_units": 0,
        "expected_proof_units": 0,
    }
    assert _expected_proof_units(candidate, "twobga-aux") == 3
    assert direction_pool.twobga_solver_eligible(candidate) is False


def test_stage3_sat_cli_summary_keeps_pool_gate(tmp_path, monkeypatch):
    candidate = _candidate()
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    ranked_input.write_text(json.dumps({
        **candidate,
        "triage_identity": {"canonical_digest": "digest-72"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }) + "\n")
    captured = {}

    def fake_screen_selected(*args, **kwargs):
        captured.update(kwargs)
        return [{
            "canonical_digest": "digest-72",
            "backend": kwargs["backend"],
            "status": "UNRESOLVED",
            "artifact_path": str(tmp_path / "sat.json"),
            "completed_directions": 0,
            "expected_directions": 26,
        }]

    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        fake_screen_selected,
    )

    assert direction_pool.main([
        str(ranked_input),
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--backend", "sat-sectors",
    ]) == direction_pool.RECOVERABLE_INCOMPLETE_EXIT_CODE
    summary = json.loads(summary_output.read_text())
    assert summary["gate"] == "qldpc-direction-candidate-pool"
    assert summary["backend"] == "sat-sectors"
    assert summary["sat_cardinality_encoding"] == "kmtotalizer"
    assert captured["sat_cardinality_encoding"] == "kmtotalizer"
    assert summary["threshold_only"] is False
    assert summary["retry_required"] is True
    assert summary["retry_reasons"] == {
        "unresolved_candidates": 1,
        "unselected_unresolved_candidates": 0,
        "operational_errors": 0,
    }


def test_stage3_sat_cardinality_cli_override_is_forwarded(
    tmp_path, monkeypatch,
):
    candidate = _candidate()
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    ranked_input.write_text(json.dumps({
        **candidate,
        "triage_identity": {"canonical_digest": "digest-72"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }) + "\n")
    captured = {}

    def fake_screen_selected(*_args, **kwargs):
        captured.update(kwargs)
        return [{
            "canonical_digest": "digest-72",
            "backend": kwargs["backend"],
            "status": "UNRESOLVED",
            "artifact_path": str(tmp_path / "sat.json"),
        }]

    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        fake_screen_selected,
    )
    assert direction_pool.main([
        str(ranked_input),
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--backend", "sat-sectors",
        "--sat-cardinality-encoding", "native-minicard",
        "--sat-incremental-conflict-budget", "25000",
    ]) == direction_pool.RECOVERABLE_INCOMPLETE_EXIT_CODE
    summary = json.loads(summary_output.read_text())
    assert captured["sat_cardinality_encoding"] == "native-minicard"
    assert captured["sat_incremental_conflict_budget"] == 25000
    assert summary["sat_cardinality_encoding"] == "native-minicard"
    assert summary["sat_incremental_conflict_budget"] == 25000
    assert summary["retry_required"] is True


def test_stage3_distqldpc_cli_preflights_and_records_backend(
    tmp_path, monkeypatch,
):
    candidate = _candidate()
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    executable = tmp_path / "distqldpc"
    ranked_input.write_text(json.dumps({
        **candidate,
        "triage_identity": {"canonical_digest": "digest-72"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }) + "\n")
    captured = {}
    backend_identity = {
        "distribution": "DistQLDPC",
        "binary_sha256": "b" * 64,
        "resolved_path": str(executable),
    }

    def fake_screen_selected(*_args, **kwargs):
        captured.update(kwargs)
        return [{
            "canonical_digest": "digest-72",
            "backend": kwargs["backend"],
            "status": "UNRESOLVED",
            "artifact_path": str(tmp_path / "sat.json"),
        }]

    monkeypatch.setattr(
        direction_pool,
        "inspect_distqldpc_binary",
        lambda path: (
            backend_identity
            if path == executable
            else pytest.fail("unexpected DistQLDPC executable")
        ),
    )
    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        fake_screen_selected,
    )

    assert direction_pool.main([
        str(ranked_input),
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--backend", "sat-sectors",
        "--sat-lower-backend", "distqldpc",
        "--sat-distqldpc-exe", str(executable),
    ]) == direction_pool.RECOVERABLE_INCOMPLETE_EXIT_CODE

    summary = json.loads(summary_output.read_text())
    assert captured["sat_lower_backend"] == "distqldpc"
    assert captured["sat_distqldpc_exe"] == executable
    assert summary["sat_lower_backend"] == "distqldpc"
    assert summary["sat_distqldpc_backend"] == backend_identity
    assert summary["proof_unit_semantics"].startswith(
        "distqldpc-maxcdcl-cardinality-portfolio"
    )


def test_stage3_cli_returns_recoverable_nonzero_when_selection_is_truncated(
    tmp_path, monkeypatch,
):
    candidate = _candidate()
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    rows = [
        {
            **candidate,
            "triage_identity": {"canonical_digest": digest},
            "campaign_audit": {"status": "UNRESOLVED"},
        }
        for digest in ("first", "second")
    ]
    ranked_input.write_text(
        "".join(json.dumps(row) + "\n" for row in rows)
    )

    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        lambda selected, *_args, **_kwargs: [{
            "canonical_digest": selected[0][0],
            "backend": "legacy-directions",
            "status": "REJECTED",
            "artifact_path": str(tmp_path / "rejected.json"),
        }],
    )

    assert direction_pool.main([
        str(ranked_input),
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--top", "1",
    ]) == direction_pool.RECOVERABLE_INCOMPLETE_EXIT_CODE

    summary = json.loads(summary_output.read_text())
    assert summary["status_counts"] == {"REJECTED": 1}
    assert summary["selection_exhausted"] is False
    assert summary["retry_required"] is True
    assert summary["retry_reasons"] == {
        "unresolved_candidates": 0,
        "unselected_unresolved_candidates": 1,
        "operational_errors": 0,
    }


@pytest.mark.parametrize(
    "status",
    ("INELIGIBLE", "BOUND_INSUFFICIENT", "EXACTNESS_GAP"),
)
def test_stage3_cli_terminal_mechanism_gaps_do_not_request_more_time(
    tmp_path, monkeypatch, status,
):
    candidate = _candidate()
    ranked_input = tmp_path / "ranked.jsonl"
    ranked_output = tmp_path / "audited.jsonl"
    summary_output = tmp_path / "summary.json"
    ranked_input.write_text(json.dumps({
        **candidate,
        "triage_identity": {"canonical_digest": "mechanism-gap"},
        "campaign_audit": {"status": "UNRESOLVED"},
    }) + "\n")
    monkeypatch.setattr(
        direction_pool,
        "screen_selected_candidates",
        lambda *_args, **_kwargs: [{
            "canonical_digest": "mechanism-gap",
            "backend": "twobga-aux",
            "status": status,
            "artifact_path": str(tmp_path / "mechanism-gap.json"),
        }],
    )

    assert direction_pool.main([
        str(ranked_input),
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--backend", "twobga-aux",
    ]) == 0

    summary = json.loads(summary_output.read_text())
    assert summary["status_counts"] == {status: 1}
    assert summary["selection_exhausted"] is True
    assert summary["retry_required"] is False
    assert summary["retry_reasons"] == {
        "unresolved_candidates": 0,
        "unselected_unresolved_candidates": 0,
        "operational_errors": 0,
    }


def test_stage3_sat_manifest_uses_typed_sector_handoff(tmp_path, monkeypatch):
    artifact = {
        "gate": candidate_pool.SECTOR_SAT_STAGE3_GATE,
        "status": "THRESHOLD_PROVEN",
    }
    path = tmp_path / "sat-stage3.json"
    path.write_text(json.dumps(artifact) + "\n")
    seen = []
    monkeypatch.setattr(
        candidate_pool,
        "claim_from_sector_sat_artifact",
        lambda value: seen.append(value) or {
            **_candidate(),
            candidate_pool.SECTOR_SAT_REQUEST_FIELD: {},
        },
    )
    monkeypatch.setattr(
        candidate_pool,
        "claim_from_certifiable_stage3_artifact",
        lambda _value: pytest.fail("SAT artifact routed to legacy handoff"),
    )

    artifacts, failures = threshold_artifacts([{
        "canonical_digest": "digest-72",
        "status": "THRESHOLD_PROVEN",
        "artifact_path": str(path),
    }])

    assert failures == {}
    assert artifacts == [artifact]
    assert seen == [artifact]


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


def test_sat_resume_prioritizes_required_upper_witness(tmp_path):
    plain = {**_candidate(), "canonical_digest": "plain"}
    attempted = {**_candidate(), "canonical_digest": "attempted"}
    promising = {**_candidate(), "canonical_digest": "promising"}
    selected = [
        ("plain", plain),
        ("attempted", attempted),
        ("promising", promising),
    ]
    attempted_path = direction_pool.sat_state_path(tmp_path, "attempted")
    attempted_path.parent.mkdir(parents=True)
    attempted_path.write_text(json.dumps({"attempted_units": 5}))
    checkpoint_dir = (
        tmp_path / "sat-sectors" / "sat-units"
        / direction_pool.safe_digest("promising")
    )
    checkpoint_dir.mkdir(parents=True)
    (checkpoint_dir / "upper-X-global.json").write_text(json.dumps({
        "outcome": "sat",
        "objective": promising["required_distance"],
    }))

    ordered = prioritize_resume_candidates(
        selected,
        tmp_path,
        backend="sat-sectors",
        resume=True,
    )

    assert [digest for digest, _ in ordered] == [
        "promising", "attempted", "plain",
    ]


def test_resume_priority_does_not_reorder_legacy_or_fresh_runs(tmp_path):
    selected = [
        ("first", {**_candidate(), "canonical_digest": "first"}),
        ("second", {**_candidate(), "canonical_digest": "second"}),
    ]

    assert prioritize_resume_candidates(
        selected, tmp_path, backend="legacy-directions", resume=True,
    ) == selected
    assert prioritize_resume_candidates(
        selected, tmp_path, backend="sat-sectors", resume=False,
    ) == selected


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
