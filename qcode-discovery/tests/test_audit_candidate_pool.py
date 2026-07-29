"""Unit tests for the proof-oriented candidate-pool orchestrator."""

from __future__ import annotations

import json
from types import SimpleNamespace

import pytest
import scripts.audit_candidate_pool as candidate_pool

from scripts.audit_candidate_pool import (
    AuditConfig,
    _annotate_ranked,
    audit_candidate,
    canonicalize_for_audit,
    certify_candidate,
    certify_selected_candidates,
    rank_candidate_files,
    read_candidate_jsonl,
    safe_digest,
    select_audit_candidates,
    state_paths,
    validate_worker_budget,
)


_REAL_POSITIVE_DIMENSION_CONSTRUCTIONS = (
    (
        [[2, 3], [5, 4], [1, 2]],
        [[3, 5], [5, 0], [0, 4]],
    ),
    (
        [[5, 0], [5, 4], [5, 5]],
        [[5, 0], [4, 1], [1, 3]],
    ),
    (
        [[2, 2], [1, 3], [5, 3]],
        [[4, 0], [0, 0], [0, 4]],
    ),
    (
        [[4, 3], [3, 1], [4, 2]],
        [[5, 2], [4, 0], [3, 4]],
    ),
    (
        [[3, 4], [2, 5], [5, 1]],
        [[0, 1], [0, 3], [3, 5]],
    ),
    (
        [[1, 1], [0, 2], [5, 3]],
        [[2, 0], [3, 2], [1, 5]],
    ),
    (
        [[2, 2], [0, 4], [3, 0]],
        [[1, 1], [2, 3], [0, 2]],
    ),
    (
        [[3, 3], [1, 2], [2, 4]],
        [[5, 4], [5, 0], [0, 3]],
    ),
)


def _construction(marker: int) -> dict:
    a_terms, b_terms = _REAL_POSITIVE_DIMENSION_CONSTRUCTIONS[
        marker % len(_REAL_POSITIVE_DIMENSION_CONSTRUCTIONS)
    ]
    return {
        "source": f"candidate-{marker}",
        "ell": 6,
        "m": 6,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": 72,
        "k": 2,
        "required_distance": 21,
    }


def _novelty_result(
    canonical_digest: str,
    *,
    novel: bool = True,
) -> dict:
    registry = candidate_pool.load_registry()
    return {
        "checked": True,
        "novel": novel,
        "code_type": "css",
        "canonical_digest": canonical_digest,
        "registry_version": registry["registry_version"],
        "registry_sha256": registry["registry_sha256"],
        "matched_entries": [] if novel else [{
            "id": "known",
            "family": "test",
            "provenance": "test",
        }],
    }


def _parameterized_fake_code(n: int = 72, k: int = 4):
    return SimpleNamespace(num_qudits=n, dimension=k)


def _fake_certificate(identifier: str, *, passed: bool, exact: bool) -> dict:
    completed = 1 if exact else 0
    return {
        "certificate_type": "fake",
        "certificate_sha256": identifier,
        "passed": passed,
        "milp": {
            "exact": exact,
            "completed_directions": completed,
            "expected_directions": 1,
        },
    }


def test_rank_candidate_files_demotes_unsealed_rejection_to_advisory(tmp_path):
    expanded = tmp_path / "expanded.jsonl"
    frontier = tmp_path / "frontier.jsonl"
    expanded.write_text(json.dumps({
        "trial": 1,
        "claim": _construction(1),
        "directions": [{
            "mip_dual_bound": 20,
            "objective": 24,
            "witness_verified": True,
        }],
    }) + "\n")
    frontier.write_text("\n".join([
        json.dumps({
            **_construction(2),
            "trial": 2,
            "directions": [{
                "objective": 1,
                "witness_verified": True,
            }],
        }),
        json.dumps({
            **_construction(3),
            "trial": 3,
            "directions": [{"mip_dual_bound": 10}],
        }),
    ]) + "\n")

    ranked, counts = rank_candidate_files([expanded, frontier])

    assert counts == {
        "input_records": 3,
        "unique_candidates": 3,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": 3,
    }
    assert all(
        row["proof_score"]["status"] == "UNSCREENED" for row in ranked
    )
    assert not any(row["proof_score"]["rejected"] is True for row in ranked)
    demoted = next(row for row in ranked if row["source"] == "candidate-2")
    assert demoted["input_proof_advisory"]["evidence"]["directions"][0] == {
        "objective": 1,
        "witness_verified": True,
    }


def test_rank_candidate_files_derives_authoritative_stage1_threshold(tmp_path):
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(json.dumps({
        "source": "humanize-stage1",
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
        "n": 72,
        "k": 12,
        "d": 6,
        "fom": 6.0,
    }) + "\n")

    ranked, counts = rank_candidate_files([stage1])

    assert counts == {
        "input_records": 1,
        "unique_candidates": 1,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": 1,
    }
    assert ranked[0]["n"] == 72
    assert ranked[0]["k"] == 8
    assert ranked[0]["required_distance"] == 11
    assert ranked[0]["proof_score"]["required_distance"] == 11
    assert ranked[0]["authoritative_geometry"]["reported_k"] == 12
    assert ranked[0]["authoritative_geometry"]["reported_k_matches"] is False


def test_rank_candidate_files_rebuilds_untrusted_reported_parameters(
    tmp_path,
):
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text("\n".join([
        json.dumps({**_construction(1), "required_distance": 999}),
        json.dumps({**_construction(2), "k": 0}),
        json.dumps({**_construction(3), "n": "72"}),
        json.dumps({"ell": 6, "m": 6, "A_terms": [[0, 0], [1, 0]]}),
    ]) + "\n")

    ranked, counts = rank_candidate_files([stage1])

    assert len(ranked) == 3
    by_source = {row["source"]: row for row in ranked}
    assert by_source["candidate-1"]["k"] == 4
    assert by_source["candidate-1"]["required_distance"] == 15
    assert by_source["candidate-2"]["k"] == 8
    assert by_source["candidate-2"]["required_distance"] == 11
    assert by_source["candidate-2"]["authoritative_geometry"]["reported_k"] == 0
    assert by_source["candidate-3"]["k"] == 4
    assert by_source["candidate-3"]["required_distance"] == 15
    assert by_source["candidate-3"]["authoritative_geometry"]["reported_n"] == "72"
    assert counts == {
        "input_records": 4,
        "unique_candidates": 3,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": 3,
        "malformed_records": 1,
    }


def test_rank_candidate_files_uses_search_upside_only_to_break_proof_ties(
    tmp_path,
):
    stage1 = tmp_path / "stage1.jsonl"
    clean = tmp_path / "clean.jsonl"
    low = {**_construction(1), "d": 4}
    high = {**_construction(2), "d": 20}
    forged = {
        **_construction(3),
        "d": 1,
        "required_distance": 1,
        "status": "THRESHOLD_PROVEN",
        "proof_score": {
            "status": "THRESHOLD_PROVEN",
            "rejected": False,
            "threshold_safe_directions": 999,
        },
        "directions": [{
            "mip_dual_bound": 10_000,
            "objective": 24,
            "witness_verified": True,
        }],
    }
    stage1.write_text("\n".join(map(json.dumps, [low, high, forged])) + "\n")
    clean.write_text("\n".join(map(
        json.dumps,
        [low, high, _construction(3) | {"d": 1}],
    )) + "\n")

    ranked, _counts = rank_candidate_files([stage1])
    clean_ranked, _clean_counts = rank_candidate_files([clean])

    assert [row["source"] for row in ranked] == [
        "candidate-2",
        "candidate-1",
        "candidate-3",
    ]
    assert [row["source"] for row in ranked] == [
        row["source"] for row in clean_ranked
    ]
    forged_ranked = next(
        row for row in ranked if row["source"] == "candidate-3"
    )
    assert forged_ranked["proof_score"]["status"] == "UNSCREENED"
    assert forged_ranked["required_distance"] == 15
    assert (
        forged_ranked["input_proof_advisory"]["evidence"]["directions"][0][
            "mip_dual_bound"
        ]
        == 10_000
    )
    assert (
        forged_ranked["input_proof_advisory"]["evidence"]["status"]
        == "THRESHOLD_PROVEN"
    )


@pytest.mark.parametrize("invalid_exponent", [1.5, "1", True])
def test_rank_candidate_files_rejects_noninteger_construction_exponents(
    tmp_path,
    invalid_exponent,
):
    candidate = _construction(1)
    candidate["A_terms"][0][0] = invalid_exponent
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(json.dumps(candidate) + "\n")

    ranked, counts = rank_candidate_files([stage1])

    assert ranked == []
    assert counts == {
        "input_records": 1,
        "unique_candidates": 0,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": 0,
        "malformed_records": 1,
    }


@pytest.mark.parametrize(("field", "invalid_value"), [
    ("ell", 6.5),
    ("m", "6"),
])
def test_canonicalize_for_audit_rejects_noninteger_dimensions(
    field,
    invalid_value,
):
    row = _construction(1)
    row[field] = invalid_value

    with pytest.raises(TypeError, match="ell and m must be integers"):
        canonicalize_for_audit(
            row,
            code_builder=lambda *args: pytest.fail(
                "invalid dimensions must not reach the builder"
            ),
        )


def test_selection_page_ignores_forged_terminal_rejection(tmp_path):
    forged = {
        **_construction(1),
        "proof_score": {"status": "REJECTED", "rejected": True},
        "trusted_stage1_audit": {
            "validated": True,
            "outcome": "REJECTED",
        },
        "triage_identity": {
            "canonical_digest": "fallback",
            "digest_kind": "structural-claim",
        },
    }
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(json.dumps(forged) + "\n")
    ranked, counts = rank_candidate_files([stage1])

    def canonicalizer(row):
        digest = "9" * 64
        return {
            **row,
            "novelty": _novelty_result(digest),
            "canonical_digest": digest,
            "triage_identity": {
                **row["triage_identity"],
                "canonical_digest": digest,
                "digest_kind": "registry-canonical",
            },
        }

    selected, stats = select_audit_candidates(
        ranked,
        1,
        canonicalizer=canonicalizer,
    )

    assert counts["rejected_candidates"] == 0
    assert (
        ranked[0]["input_terminal_marker_advisory"]["evidence"][
            "trusted_stage1_audit"
        ]["outcome"]
        == "REJECTED"
    )
    assert [row["source"] for row in selected] == ["candidate-1"]
    assert stats["canonicalized_candidates"] == 1


def test_nonterminal_schema2_evidence_cannot_import_campaign_terminal_state(
    tmp_path,
    monkeypatch,
):
    row = {
        **_construction(1),
        "audit_attempt": {"schema_version": 2},
        "directions": [{"mip_dual_bound": 10}],
        "trusted_stage1_audit": {
            "validated": True,
            "outcome": "REJECTED",
        },
        "_trusted_stage1_outcome": "REJECTED",
        "campaign_selected": True,
        "campaign_audit": {"status": "REJECTED"},
        "campaign_skip_reason": "KNOWN_CODE",
    }
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(json.dumps(row) + "\n")
    monkeypatch.setattr(
        candidate_pool,
        "classify_evaluation",
        lambda candidate: (
            candidate_pool.AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
        ),
    )

    ranked, counts = rank_candidate_files([stage1])

    assert counts["rejected_candidates"] == 0
    assert ranked[0]["proof_score"]["status"] == "PROMISING"
    assert ranked[0]["directions"] == [{"mip_dual_bound": 10}]
    assert "trusted_stage1_audit" not in ranked[0]
    demoted = ranked[0]["input_terminal_marker_advisory"]["evidence"]
    assert demoted["_trusted_stage1_outcome"] == "REJECTED"
    assert demoted["campaign_audit"] == {"status": "REJECTED"}


def test_real_candidate_with_forged_witness_and_wrong_geometry_reaches_proof(
    tmp_path,
):
    candidate = {
        **_construction(1),
        "n": 0,
        "k": 0,
        "required_distance": 999,
        "status": "THRESHOLD_PROVEN",
        "proof_score": {"status": "REJECTED", "rejected": True},
        "trusted_stage1_audit": {
            "validated": True,
            "outcome": "REJECTED",
        },
        "directions": [{
            "objective": 1,
            "witness_verified": True,
            "mip_dual_bound": 10_000,
        }],
    }
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(json.dumps(candidate) + "\n")

    ranked, counts = rank_candidate_files([stage1])
    selected, stats = select_audit_candidates(
        ranked,
        1,
        canonicalizer=lambda row: canonicalize_for_audit(
            row,
            novelty_checker=lambda code, **kwargs: _novelty_result("8" * 64),
        ),
    )

    assert counts["eligible_candidates"] == 1
    assert stats["canonicalized_candidates"] == 1
    assert len(selected) == 1
    rebuilt = selected[0]
    assert (rebuilt["n"], rebuilt["k"], rebuilt["required_distance"]) == (
        72,
        4,
        15,
    )
    geometry = rebuilt["authoritative_geometry"]
    assert (geometry["reported_n"], geometry["reported_k"]) == (0, 0)
    assert geometry["reported_n_matches"] is False
    assert geometry["reported_k_matches"] is False
    assert geometry["selection_rebuild"]["reported_n_matches"] is True
    assert geometry["selection_rebuild"]["reported_k_matches"] is True
    assert rebuilt["proof_score"]["status"] == "UNSCREENED"

    safe_sectors = [
        {
            "sector": sector,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 14,
            "operator": None,
            "anchor_indices": [0, 36],
        }
        for sector in ("X", "Z")
    ]
    result = audit_candidate(
        rebuilt,
        AuditConfig(state_dir=tmp_path / "audit", certify=False),
        symmetry_checker=lambda row: {
            "verified": True,
            "orbit_representatives": [0, 36],
        },
        replay_loader=lambda *args, **kwargs: safe_sectors,
        sector_solver=lambda payload: pytest.fail(
            "complete replayed proof should not invoke the solver"
        ),
    )

    assert result["status"] == "THRESHOLD_PROVEN"


@pytest.mark.parametrize(
    ("exact_distance", "expected_status", "expected_count"),
    [
        (15, "THRESHOLD_PROVEN", "trusted_stage1_winners"),
        (14, "REJECTED", "trusted_stage1_rejections"),
    ],
)
def test_formally_replayed_stage1_exact_row_replaces_bp_duplicate(
    tmp_path,
    monkeypatch,
    exact_distance,
    expected_status,
    expected_count,
):
    candidate = _construction(1)
    raw = {
        **candidate,
        "source": "raw-bp-upper-bound",
        "d": 40,
    }
    exact = {
        **candidate,
        "source": "formal-stage1-milp",
        "d": exact_distance,
        "d_is_exact": True,
        "audit_attempt": {"schema_version": 2},
    }
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text("\n".join(map(json.dumps, [raw, exact])) + "\n")
    monkeypatch.setattr(
        candidate_pool,
        "classify_evaluation",
        lambda row: candidate_pool.AuditOutcome.EXACT,
    )

    ranked, counts = rank_candidate_files([stage1])

    assert len(ranked) == 1
    assert ranked[0]["source"] == "formal-stage1-milp"
    assert ranked[0]["d"] == exact_distance
    assert ranked[0]["proof_score"]["status"] == expected_status
    assert ranked[0]["trusted_stage1_audit"] == {
        "validated": True,
        "outcome": expected_status,
        "audit_attempt_schema": 2,
    }
    assert counts[expected_count] == 1
    assert counts["duplicate_records"] == 1
    assert counts["eligible_candidates"] == (
        1 if expected_status == "THRESHOLD_PROVEN" else 0
    )


def test_jsonl_reader_ignores_only_unterminated_trailing_fragment(tmp_path):
    live = tmp_path / "live.jsonl"
    complete = _construction(1)
    live.write_text(json.dumps(complete) + "\n" + '{"trial":')

    records, sources = read_candidate_jsonl([live])

    assert records == [complete]
    assert sources == [str(live)]

    malformed = tmp_path / "malformed.jsonl"
    malformed.write_text(json.dumps(complete) + "\n" + '{"trial":\n')
    with pytest.raises(ValueError, match="invalid JSON"):
        read_candidate_jsonl([malformed])


def test_worker_budget_prevents_solver_oversubscription():
    validate_worker_budget(2, 4, 8)
    with pytest.raises(ValueError, match="exceeds"):
        validate_worker_budget(3, 4, 8)
    with pytest.raises(ValueError, match="between 1 and 8"):
        validate_worker_budget(1, 9, 16)


def test_audit_resumes_one_sector_and_certifies_threshold_proof(tmp_path):
    digest = "claim-sha256:" + "a" * 64
    ranked = {
        **_construction(4),
        "triage_identity": {"canonical_digest": digest},
        "proof_score": {"status": "PROMISING", "rejected": False},
    }
    config = AuditConfig(
        state_dir=tmp_path,
        solver_timeout_s=12,
        solver_workers=3,
        known_answer_artifact=tmp_path / "known.json",
    )
    calls: dict[str, list] = {"solved": [], "built": [], "verified": []}

    def symmetry(candidate):
        return {
            "verified": True,
            "orbit_representatives": [0, 36],
        }

    def replay(path, candidate, **kwargs):
        return [{
            "sector": "Z",
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 20,
            "operator": None,
            "anchor_indices": [0, 36],
        }]

    def solve(payload):
        candidate, sector, timeout, max_weight, workers, seed, anchors = payload
        calls["solved"].append(
            (sector, timeout, max_weight, workers, anchors),
        )
        return {
            "sector": sector,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": max_weight,
            "operator": None,
            "anchor_indices": list(anchors),
        }

    def build(candidate, **kwargs):
        calls["built"].append((candidate, kwargs))
        return {
            **_fake_certificate("cert-a", passed=True, exact=True),
            "claim": candidate,
        }

    def verify(certificate, **kwargs):
        calls["verified"].append((certificate, kwargs))
        return {"passed": True}

    result = audit_candidate(
        ranked,
        config,
        symmetry_checker=symmetry,
        replay_loader=replay,
        sector_solver=solve,
        certificate_builder=build,
        certificate_verifier=verify,
    )

    assert result["status"] == "THRESHOLD_PROVEN"
    assert result["resumed_sectors"] == 1
    assert calls["solved"] == [("X", 12, 20, 3, (0, 36))]
    assert calls["built"] == calls["verified"] == []
    assert result["certificate"] == {
        "attempted": False,
        "deferred": True,
    }

    def certifier(candidate, candidate_digest, phase_config):
        return certify_candidate(
            candidate,
            candidate_digest,
            phase_config,
            builder=build,
            verifier=verify,
        )

    certifications = certify_selected_candidates(
        [ranked],
        config,
        certificate_workers=1,
        certifier=certifier,
    )
    certified = certifications[digest]
    assert len(calls["built"]) == len(calls["verified"]) == 1
    assert certified["certificate_passed"] is True
    assert certified["verification_passed"] is True
    paths = state_paths(tmp_path, digest)
    assert json.loads(paths["audit"].read_text())["status"] == "THRESHOLD_PROVEN"
    assert json.loads(paths["certificate"].read_text())["passed"] is True
    assert json.loads(paths["verification"].read_text())[
        "verification"
    ]["passed"] is True


def test_completed_certificate_and_verification_are_resumed(tmp_path):
    digest = "digest/with unsafe characters"
    candidate = _construction(5)
    config = AuditConfig(
        state_dir=tmp_path,
        known_answer_artifact=tmp_path / "known.json",
    )

    first = certify_candidate(
        candidate,
        digest,
        config,
        builder=lambda claim, **kwargs: _fake_certificate(
            "cert-b", passed=True, exact=True,
        ),
        verifier=lambda certificate, **kwargs: {"passed": True},
    )

    def should_not_run(*args, **kwargs):
        raise AssertionError("completed certificate work was repeated")

    second = certify_candidate(
        candidate,
        digest,
        config,
        builder=should_not_run,
        verifier=should_not_run,
    )

    assert first["certificate_resumed"] is False
    assert first["verification_resumed"] is False
    assert second["certificate_resumed"] is True
    assert second["verification_resumed"] is True
    assert "/" not in safe_digest(digest)
    assert len(safe_digest(digest)) == 64


def test_certificate_cache_is_invalidated_by_source_fingerprint(
    tmp_path,
    monkeypatch,
):
    build_calls = []
    verification_calls = []

    def build(claim, **kwargs):
        build_calls.append(kwargs)
        return _fake_certificate(
            f"source-{len(build_calls)}",
            passed=True,
            exact=True,
        )

    def verify(certificate, **kwargs):
        verification_calls.append(kwargs)
        return {"passed": True}

    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    config = AuditConfig(state_dir=tmp_path)
    certify_candidate(
        _construction(1),
        "source-bound",
        config,
        builder=build,
        verifier=verify,
    )

    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v2",
    )
    second = certify_candidate(
        _construction(1),
        "source-bound",
        config,
        builder=build,
        verifier=verify,
    )

    assert len(build_calls) == len(verification_calls) == 2
    assert build_calls[1]["resume"] is False
    assert verification_calls[1]["resume"] is False
    assert second["certificate_resumed"] is False
    assert second["verification_resumed"] is False
    paths = state_paths(tmp_path, "source-bound")
    assert json.loads(paths["certificate_metadata"].read_text())[
        "source_fingerprint"
    ] == "source-v2"
    assert json.loads(paths["verification"].read_text())[
        "source_fingerprint"
    ] == "source-v2"


@pytest.mark.parametrize("dependency", ["audit_state.py", "state.py"])
def test_certificate_source_fingerprint_includes_humanize_audit_dependencies(
    tmp_path,
    monkeypatch,
    dependency,
):
    project = tmp_path / "qcode"
    for path in (
        project / "scripts" / "audit_candidate_pool.py",
        project / "scripts" / "audit_direction_pool.py",
        project / "scripts" / "finalize_challenge.py",
        project / "tests" / "verify_known_answer_gate.py",
        project / "results" / "known_code_registry.json",
        project / "humanize" / "audit_state.py",
        project / "humanize" / "state.py",
        project / "evaluation" / "verifier.py",
    ):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"# fake {path.name}\n")
    monkeypatch.setattr(candidate_pool, "PROJECT", project)
    monkeypatch.setattr(
        candidate_pool,
        "__file__",
        str(project / "scripts" / "audit_candidate_pool.py"),
    )

    before = candidate_pool.certificate_source_fingerprint()
    source = project / "humanize" / dependency
    source.write_text(source.read_text() + "# changed audit dependency\n")

    assert candidate_pool.certificate_source_fingerprint() != before


def test_incomplete_certificate_is_retried_from_checkpoint(tmp_path):
    calls = []

    def build(claim, **kwargs):
        calls.append(kwargs)
        return _fake_certificate(
            f"incomplete-{len(calls)}", passed=False, exact=False,
        )

    config = AuditConfig(state_dir=tmp_path)
    first = certify_candidate(
        _construction(1), "incomplete", config, builder=build,
    )
    second = certify_candidate(
        _construction(1), "incomplete", config, builder=build,
    )

    assert len(calls) == 2
    assert calls[1]["resume"] is True
    assert first["certificate_exact"] is False
    assert second["certificate_resumed"] is False


def test_failed_verification_is_retried_and_resumes_checkpoint(tmp_path):
    builds = []
    verification_calls = []

    def build(claim, **kwargs):
        builds.append(kwargs)
        return _fake_certificate("exact-win", passed=True, exact=True)

    def verify(certificate, **kwargs):
        verification_calls.append(kwargs)
        return {"passed": len(verification_calls) == 2}

    config = AuditConfig(state_dir=tmp_path)
    first = certify_candidate(
        _construction(2), "verify-retry", config,
        builder=build, verifier=verify,
    )
    second = certify_candidate(
        _construction(2), "verify-retry", config,
        builder=build, verifier=verify,
    )

    assert len(builds) == 1
    assert len(verification_calls) == 2
    assert verification_calls[1]["resume"] is True
    assert first["verification_passed"] is False
    assert second["certificate_resumed"] is True
    assert second["verification_resumed"] is False
    assert second["verification_passed"] is True


def test_failed_certificate_skips_independent_milp_rerun(tmp_path):
    digest = "failed-certificate"
    verifier_calls = []

    result = certify_candidate(
        _construction(1),
        digest,
        AuditConfig(state_dir=tmp_path),
        builder=lambda claim, **kwargs: {
            "certificate_sha256": "cert-failed",
            "passed": False,
        },
        verifier=lambda certificate, **kwargs: verifier_calls.append(
            (certificate, kwargs),
        ),
    )

    assert verifier_calls == []
    assert result["certificate_passed"] is False
    assert result["verification_passed"] is False
    assert result["verification_attempted"] is False
    envelope = json.loads(
        state_paths(tmp_path, digest)["verification"].read_text(),
    )
    assert envelope["verification"] == {
        "passed": False,
        "skipped": True,
        "reason": "certificate build did not pass the exact challenge gate",
    }


def test_no_certify_stops_after_threshold_proof(tmp_path):
    digest = "digest"
    ranked = {
        **_construction(0),
        "triage_identity": {"canonical_digest": digest},
    }
    config = AuditConfig(state_dir=tmp_path, certify=False)
    safe_sectors = [
        {
            "sector": sector,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 20,
            "operator": None,
            "anchor_indices": [0, 36],
        }
        for sector in ("X", "Z")
    ]
    result = audit_candidate(
        ranked,
        config,
        symmetry_checker=lambda candidate: {
            "verified": True,
            "orbit_representatives": [0, 36],
        },
        replay_loader=lambda *args, **kwargs: safe_sectors,
        sector_solver=lambda payload: pytest.fail("no sector should rerun"),
    )
    assert result["status"] == "THRESHOLD_PROVEN"
    assert result["certificate"] == {"attempted": False}


def test_canonicalize_for_audit_replaces_claim_fallback_digest():
    actual_digest = "a" * 64
    row = {
        **_construction(2),
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
            "source_identity": "input#trial=2",
        },
    }
    built = []

    def builder(ell, m, a_terms, b_terms):
        built.append((ell, m, a_terms, b_terms))
        return _parameterized_fake_code()

    updated = canonicalize_for_audit(
        row,
        code_builder=builder,
        novelty_checker=lambda code, **kwargs: _novelty_result(
            actual_digest,
        ),
    )

    assert len(built) == 1
    assert updated["canonical_digest"] == actual_digest
    assert updated["triage_identity"]["canonical_digest"] == actual_digest
    assert (
        updated["triage_identity"]["precanonical_digest"]
        == "claim-sha256:fallback"
    )
    assert updated["triage_identity"]["digest_kind"] == "registry-canonical"
    assert updated["novelty"]["replayed_from_construction"] is True
    assert len(updated["novelty"]["registry_content_sha256"]) == 64
    assert len(updated["novelty"]["checker_source_fingerprint"]) == 64


def test_checked_novelty_without_novel_is_replayed_and_selected():
    actual_digest = "b" * 64
    row = {
        **_construction(2),
        "proof_score": {"status": "PROMISING", "rejected": False},
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
        "novelty": {
            "checked": True,
            "canonical_digest": "c" * 64,
        },
    }
    calls = []

    def canonicalizer(value):
        return canonicalize_for_audit(
            value,
            code_builder=lambda *args: _parameterized_fake_code(),
            novelty_checker=lambda code, **kwargs: (
                calls.append(kwargs)
                or _novelty_result(actual_digest)
            ),
        )

    selected, stats = select_audit_candidates(
        [row],
        1,
        canonicalizer=canonicalizer,
    )

    assert len(calls) == 1
    assert calls[0]["code_type"] == "css"
    assert selected[0]["canonical_digest"] == actual_digest
    assert selected[0]["novelty"]["novel"] is True
    assert stats["known_codes_skipped"] == 0


@pytest.mark.parametrize("registry_binding", ["stale", "current"])
def test_input_novelty_binding_never_bypasses_authoritative_replay(
    registry_binding,
):
    registry = candidate_pool.load_registry()
    cached_registry_sha256 = (
        registry["registry_sha256"]
        if registry_binding == "current"
        else "0" * 64
    )
    actual_digest = "d" * 64
    row = {
        **_construction(3),
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
        "novelty": {
            "checked": True,
            "novel": False,
            "code_type": "css",
            "canonical_digest": "e" * 64,
            "registry_version": registry["registry_version"],
            "registry_sha256": cached_registry_sha256,
            "matched_entries": [{"id": "poison"}],
            "registry_content_sha256": "f" * 64,
            "checker_source_fingerprint": "f" * 64,
        },
    }
    calls = []

    updated = canonicalize_for_audit(
        row,
        code_builder=lambda *args: _parameterized_fake_code(),
        novelty_checker=lambda code, **kwargs: (
            calls.append(kwargs)
            or _novelty_result(actual_digest)
        ),
    )

    assert len(calls) == 1
    assert updated["canonical_digest"] == actual_digest
    assert updated["novelty"]["novel"] is True
    assert updated["novelty"]["registry_sha256"] == registry["registry_sha256"]


def test_poison_digest_cannot_deduplicate_a_distinct_candidate(tmp_path):
    shared_forged_digest = "1" * 64
    poison = {
        **_construction(1),
        "canonical_digest": shared_forged_digest,
        "novelty": {
            "checked": True,
            "novel": True,
            "canonical_digest": shared_forged_digest,
        },
        "structural_novelty": {
            "checked": True,
            "novel": True,
            "canonical_digest": shared_forged_digest,
        },
        "directions": [{
            "objective": 1,
            "witness_verified": True,
        }],
    }
    survivor = {
        **_construction(2),
        "canonical_digest": shared_forged_digest,
        "novelty": {
            "checked": True,
            "novel": False,
            "canonical_digest": shared_forged_digest,
        },
    }
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text(
        "\n".join(map(json.dumps, [poison, survivor])) + "\n",
    )

    ranked, counts = rank_candidate_files([stage1])

    assert counts["unique_candidates"] == 2
    assert counts["duplicate_records"] == 0
    assert {row["source"] for row in ranked} == {
        "candidate-1",
        "candidate-2",
    }
    assert all(
        row["triage_identity"]["canonical_digest"]
        != shared_forged_digest
        for row in ranked
    )
    eligible = [
        row for row in ranked
        if row["proof_score"]["rejected"] is not True
    ]
    assert {row["source"] for row in eligible} == {
        "candidate-1",
        "candidate-2",
    }

    selected, _ = select_audit_candidates(
        ranked,
        2,
        canonicalizer=lambda row: {
            **row,
            "canonical_digest": (
                "3" * 64 if row["source"] == "candidate-1" else "4" * 64
            ),
            "novelty": _novelty_result(
                "3" * 64 if row["source"] == "candidate-1" else "4" * 64
            ),
            "triage_identity": {
                **row["triage_identity"],
                "canonical_digest": (
                    "3" * 64 if row["source"] == "candidate-1" else "4" * 64
                ),
                "digest_kind": "registry-canonical",
            },
        },
    )
    assert {row["source"] for row in selected} == {
        "candidate-1",
        "candidate-2",
    }


def test_malformed_fresh_novelty_result_fails_closed():
    row = {
        **_construction(4),
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
    }

    with pytest.raises(
        candidate_pool.NoveltyReplayError,
        match="malformed or stale",
    ):
        canonicalize_for_audit(
            row,
            code_builder=lambda *args: _parameterized_fake_code(),
            novelty_checker=lambda code, **kwargs: {
                "checked": True,
                "canonical_digest": "2" * 64,
            },
        )


def test_select_queue_skips_known_and_canonical_duplicates():
    rows = []
    for marker in range(1, 5):
        rows.append({
            **_construction(marker),
            "proof_score": {"status": "PROMISING", "rejected": False},
            "triage_identity": {
                "canonical_digest": f"fallback-{marker}",
                "digest_kind": "structural-claim",
            },
        })

    def canonicalizer(row):
        marker = int(str(row["source"]).split("-")[-1])
        digest = {
            1: "same",
            2: "same",
            3: "known",
            4: "unique",
        }[marker]
        return {
            **row,
            "canonical_digest": digest,
            "novelty": {
                "checked": True,
                "novel": marker != 3,
                "canonical_digest": digest,
            },
            "triage_identity": {
                **row["triage_identity"],
                "canonical_digest": digest,
                "digest_kind": "registry-canonical",
            },
        }

    selected, stats = select_audit_candidates(
        rows, 2, canonicalizer=canonicalizer,
    )

    assert [row["source"] for row in selected] == [
        "candidate-1", "candidate-4",
    ]
    assert stats == {
        "canonicalized_candidates": 4,
        "canonical_duplicates_skipped": 1,
        "known_codes_skipped": 1,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
    }
    assert rows[1]["campaign_skip_reason"] == "CANONICAL_DUPLICATE"
    assert rows[2]["campaign_skip_reason"] == "KNOWN_CODE"

    annotated = _annotate_ranked(
        rows,
        {"same", "unique"},
        [{"canonical_digest": "same", "status": "UNRESOLVED"}],
    )
    same_rows = [
        row
        for row in annotated
        if row["triage_identity"]["canonical_digest"] == "same"
    ]
    assert sum(row["campaign_selected"] is True for row in same_rows) == 1
    assert sum("campaign_audit" in row for row in same_rows) == 1


def test_top_truncation_is_reported_as_unexhausted():
    rows = [
        {
            **_construction(marker),
            "proof_score": {"status": "PROMISING", "rejected": False},
            "triage_identity": {
                "canonical_digest": f"digest-{marker}",
                "digest_kind": "registry-canonical",
            },
        }
        for marker in (1, 2)
    ]

    def canonicalizer(row):
        return {
            **row,
            "novelty": {"checked": True, "novel": True},
        }

    selected, stats = select_audit_candidates(
        rows,
        1,
        canonicalizer=canonicalizer,
    )

    assert len(selected) == 1
    assert stats["unscanned_eligible_candidates"] == 1
    assert stats["selection_exhausted"] is False


def test_selection_ledger_replays_pending_page_then_advances(tmp_path, monkeypatch):
    def rows():
        return [
            {
                **_construction(marker),
                "proof_score": {"status": "PROMISING", "rejected": False},
                "triage_identity": {
                    "canonical_digest": f"fallback-{marker}",
                    "digest_kind": "structural-claim",
                },
            }
            for marker in (1, 2)
        ]

    def canonicalizer(row):
        marker = int(str(row["source"]).split("-")[-1])
        digest = f"canonical-{marker}"
        return {
            **row,
            "canonical_digest": digest,
            "novelty": {
                "checked": True,
                "novel": True,
                "canonical_digest": digest,
            },
            "triage_identity": {
                **row["triage_identity"],
                "canonical_digest": digest,
                "digest_kind": "registry-canonical",
            },
        }

    monkeypatch.setattr(
        candidate_pool,
        "_selection_binding",
        lambda *args, **kwargs: "b" * 64,
    )
    ledger_path = tmp_path / "selection.json"
    first, first_stats, first_page, _ = candidate_pool._prepare_selection_page(
        rows(),
        top=1,
        ledger_path=ledger_path,
        known_answer_artifact=tmp_path / "known.json",
        canonicalizer=canonicalizer,
    )
    replay, replay_stats, replay_page, _ = (
        candidate_pool._prepare_selection_page(
            rows(),
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )

    assert [row["source"] for row in first] == ["candidate-1"]
    assert [row["source"] for row in replay] == ["candidate-1"]
    assert first_page == replay_page
    assert first_stats == replay_stats
    assert first_stats["selection_exhausted"] is False

    ledger = json.loads(ledger_path.read_text())
    ledger["cursor"] = first_page["next_index"]
    ledger["committed_digests"] = first_page["selected_digests"]
    ledger["completed_pages"] = 1
    ledger["pending"] = None
    candidate_pool.atomic_write_json(ledger_path, ledger)

    second, second_stats, second_page, _ = (
        candidate_pool._prepare_selection_page(
            rows(),
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )
    assert [row["source"] for row in second] == ["candidate-2"]
    assert second_page["start_index"] == first_page["next_index"]
    assert second_stats["selection_exhausted"] is True
