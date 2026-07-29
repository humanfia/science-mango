"""Unit tests for the proof-oriented candidate-pool orchestrator."""

from __future__ import annotations

import json

import pytest

from scripts.audit_candidate_pool import (
    AuditConfig,
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


def _construction(marker: int) -> dict:
    return {
        "source": f"candidate-{marker}",
        "ell": 6,
        "m": 6,
        "A_terms": [[marker % 6, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, marker % 6]],
        "n": 72,
        "k": 2,
        "required_distance": 21,
    }


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


def test_rank_candidate_files_normalizes_and_skips_rejected(tmp_path):
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
                "objective": 20,
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
        "rejected_candidates": 1,
        "eligible_candidates": 2,
    }
    assert ranked[0]["source"] == "candidate-1"
    assert ranked[0]["proof_score"]["min_dual_ratio"] == pytest.approx(20 / 21)
    assert sum(row["proof_score"]["rejected"] is True for row in ranked) == 1


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
    assert ranked[0]["required_distance"] == 7
    assert ranked[0]["proof_score"]["required_distance"] == 7


def test_rank_candidate_files_drops_nonpositive_and_malformed_parameters(
    tmp_path,
):
    stage1 = tmp_path / "stage1.jsonl"
    stage1.write_text("\n".join([
        json.dumps({**_construction(1), "required_distance": 999}),
        json.dumps({**_construction(2), "k": 0}),
        json.dumps({**_construction(3), "n": "72"}),
    ]) + "\n")

    ranked, counts = rank_candidate_files([stage1])

    assert len(ranked) == 1
    assert ranked[0]["required_distance"] == 21
    assert counts == {
        "input_records": 3,
        "unique_candidates": 1,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": 1,
        "ineligible_records": 1,
        "malformed_records": 1,
    }


def test_rank_candidate_files_uses_search_upside_only_to_break_proof_ties(
    tmp_path,
):
    stage1 = tmp_path / "stage1.jsonl"
    low = {**_construction(1), "d": 4}
    high = {**_construction(2), "d": 20}
    proof = {
        **_construction(3),
        "d": 1,
        "directions": [{
            "mip_dual_bound": 21,
            "objective": 24,
            "witness_verified": True,
        }],
    }
    stage1.write_text("\n".join(map(json.dumps, [low, high, proof])) + "\n")

    ranked, _counts = rank_candidate_files([stage1])

    assert [row["source"] for row in ranked] == [
        "candidate-3",
        "candidate-2",
        "candidate-1",
    ]


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
        return object()

    updated = canonicalize_for_audit(
        row,
        code_builder=builder,
        novelty_checker=lambda code, **kwargs: {
            "checked": True,
            "novel": True,
            "canonical_digest": "actual-digest",
        },
    )

    assert len(built) == 1
    assert updated["canonical_digest"] == "actual-digest"
    assert updated["triage_identity"]["canonical_digest"] == "actual-digest"
    assert (
        updated["triage_identity"]["precanonical_digest"]
        == "claim-sha256:fallback"
    )
    assert updated["triage_identity"]["digest_kind"] == "registry-canonical"


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
    }
    assert rows[1]["campaign_skip_reason"] == "CANONICAL_DUPLICATE"
    assert rows[2]["campaign_skip_reason"] == "KNOWN_CODE"
