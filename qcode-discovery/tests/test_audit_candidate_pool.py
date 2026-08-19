"""Unit tests for the proof-oriented candidate-pool orchestrator."""

from __future__ import annotations

import json
import os
from types import SimpleNamespace

import numpy as np
import pytest
import scripts.audit_candidate_pool as candidate_pool
from evaluation.certificate import _certificate_sha256
from evaluation.proof_runtime import proof_runtime_fingerprint
from evaluation.target_policy import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    TARGET_MODE_SCALAR_INCLUSIVE,
    target_binding,
)
from evaluation.selection_ledger import (
    acknowledge_selection_page,
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
    seal_selection_ledger,
    validate_selection_ledger,
)

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


def _compact_construction(marker: int = 0) -> dict:
    return {
        "source": f"compact-{marker}",
        "construction": {
            "kind": "test-compact",
            "marker": marker,
        },
        "n": 8,
        "k": 2,
        "required_distance": 5,
        "triage_identity": {
            "canonical_digest": f"compact-{marker}",
        },
    }


def test_stage2_replaces_input_target_after_authoritative_geometry():
    stale = target_binding(72, 12, TARGET_MODE_GIST)

    rebound = candidate_pool._bind_authoritative_target(
        {
            "n": 999,
            "k": 1,
            "required_distance": stale["required_distance"],
            "target_mode": TARGET_MODE_GIST,
            "target": stale,
        },
        n=72,
        k=12,
        target_mode=TARGET_MODE_SCALAR,
    )

    assert rebound["target_mode"] == TARGET_MODE_SCALAR
    assert rebound["target"] == target_binding(72, 12, TARGET_MODE_SCALAR)
    assert rebound["required_distance"] == 9
    assert rebound["input_target_advisory"]["trusted"] is False
    assert rebound["input_target_advisory"]["evidence"] == {
        "target": stale,
        "target_mode": TARGET_MODE_GIST,
    }


def test_stage2_rebinds_old_target_to_authoritative_fom13_policy():
    stale = target_binding(210, 10, TARGET_MODE_SCALAR_INCLUSIVE)
    rebound = candidate_pool._bind_authoritative_target(
        {
            "n": 210,
            "k": 10,
            "target_mode": TARGET_MODE_SCALAR_INCLUSIVE,
            "target": stale,
        },
        n=210,
        k=10,
        target_mode=TARGET_MODE_SCALAR_13_INCLUSIVE,
    )

    assert rebound["target_mode"] == TARGET_MODE_SCALAR_13_INCLUSIVE
    assert rebound["required_distance"] == 17
    assert rebound["target"] == target_binding(
        210, 10, TARGET_MODE_SCALAR_13_INCLUSIVE,
    )
    assert rebound["input_target_advisory"]["evidence"] == {
        "target": stale,
        "target_mode": TARGET_MODE_SCALAR_INCLUSIVE,
    }


def _compact_oracle_evidence(outcome: str, max_weight: int) -> dict:
    witness = None
    if outcome == "SAT":
        witness = {
            "side": "X",
            "index": 0,
            "weight": 2,
            "bits": [1, 1, 0, 0, 0, 0, 0, 0],
            "logical_syndrome": [1, 0],
            "support": [0, 1],
        }
    sectors = {
        "X": {"outcome": outcome if outcome == "SAT" else "UNSAT"},
    }
    if outcome == "UNSAT":
        sectors["Z"] = {"outcome": "UNSAT"}
    elif outcome == "UNKNOWN":
        sectors = {"X": {"outcome": "UNKNOWN"}}
    return {
        "outcome": outcome,
        "decision_complete": outcome in {"SAT", "UNSAT"},
        "retryable": outcome == "UNKNOWN",
        "max_weight": max_weight,
        "distance_lower_bound": max_weight + 1 if outcome == "UNSAT" else None,
        "witness": witness,
        "sectors": sectors,
        "evidence_sha256": (outcome.lower() + "0" * 64)[:64],
    }


def _two_block_oracle_evidence(outcome: str, max_weight: int) -> dict:
    witness = None
    if outcome == "SAT":
        witness = {
            "query_id": "X:A",
            "side": "X",
            "index": 0,
            "block": "A",
            "weight": 2,
            "bits": [1, 1, 0, 0, 0, 0, 0, 0],
            "support": [0, 1],
        }
    queries = {
        query_id: {"outcome": "UNSAT"}
        for query_id in ("X:A", "X:B", "Z:A", "Z:B")
    }
    if outcome == "SAT":
        queries = {"X:A": {"outcome": "SAT"}}
    elif outcome == "UNKNOWN":
        queries = {"X:A": {"outcome": "UNKNOWN"}}
    return {
        "outcome": outcome,
        "decision_complete": outcome != "UNKNOWN",
        "retryable": outcome == "UNKNOWN",
        "max_weight": max_weight,
        "distance_lower_bound": None,
        "distance_upper_bound": 2 if outcome == "SAT" else None,
        "single_block_minimum_weight_lower_bound": (
            max_weight + 1
            if outcome == "NO_SINGLE_BLOCK_WITNESS"
            else None
        ),
        "witness": witness,
        "queries": queries,
        "evidence_sha256": ("two-block-" + outcome.lower() + "0" * 64)[:64],
    }
def _install_compact_oracle_fakes(
    monkeypatch,
    outcomes,
    *,
    two_block_outcomes=None,
):
    from evaluation import (
        construction,
        distance_milp,
        low_weight_oracle,
        two_block_sparse_kernel_oracle,
    )

    calls: list[tuple[int, tuple[str, ...]]] = []
    outcome_iterator = iter(outcomes)
    two_block_iterator = (
        None if two_block_outcomes is None else iter(two_block_outcomes)
    )
    matrices = [
        np.zeros((2, 8), dtype=np.uint8),
        np.zeros((2, 8), dtype=np.uint8),
        np.zeros((2, 8), dtype=np.uint8),
        np.zeros((2, 8), dtype=np.uint8),
    ]
    monkeypatch.setattr(
        construction,
        "build_css_code_from_claim",
        lambda _claim: SimpleNamespace(num_qudits=8, dimension=2),
    )
    monkeypatch.setattr(
        distance_milp,
        "get_code_matrices",
        lambda _code: tuple(matrix.copy() for matrix in matrices),
    )

    def evaluate(*_matrices, max_weight, hard_timeout_s, terminal_sectors):
        assert hard_timeout_s > 0
        calls.append((max_weight, tuple(sorted(terminal_sectors))))
        return _compact_oracle_evidence(next(outcome_iterator), max_weight)

    monkeypatch.setattr(
        low_weight_oracle,
        "evaluate_css_low_weight_oracle",
        evaluate,
    )
    monkeypatch.setattr(
        low_weight_oracle,
        "verify_css_low_weight_oracle",
        lambda *_args, **_kwargs: [],
    )
    monkeypatch.setattr(
        two_block_sparse_kernel_oracle,
        "evaluate_two_block_sparse_kernel_oracle",
        lambda *_args, max_weight, **_kwargs: _two_block_oracle_evidence(
            (
                "NO_SINGLE_BLOCK_WITNESS"
                if two_block_iterator is None
                else next(two_block_iterator)
            ),
            max_weight,
        ),
    )
    monkeypatch.setattr(
        two_block_sparse_kernel_oracle,
        "verify_two_block_sparse_kernel_oracle",
        lambda *_args, **_kwargs: [],
    )
    return calls, matrices


@pytest.mark.parametrize(
    ("outcome", "status", "retry_required"),
    [
        ("SAT", "REJECTED", False),
        ("UNSAT", "UNRESOLVED", False),
        ("UNKNOWN", "UNRESOLVED", True),
    ],
)
def test_compact_low_weight_gate_has_three_way_proof_semantics(
    tmp_path,
    monkeypatch,
    outcome,
    status,
    retry_required,
):
    calls, _ = _install_compact_oracle_fakes(monkeypatch, [outcome])
    result = audit_candidate(
        _compact_construction(),
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert calls == [(4, ())]
    assert result["status"] == status
    assert result["retry_required"] is retry_required
    assert result["compact_low_weight_sat_ladder"]["outcome"] == outcome
    assert result["compact_low_weight_sat_ladder"]["max_weight"] == 4
    if outcome == "SAT":
        assert result["distance_upper_bound"] == 2
        assert result["threshold_rejection_proven"] is True
    elif outcome == "UNSAT":
        assert result["distance_lower_bound"] == 5
        assert result["deferred_backend"] == "generic-global-sat"


def test_compact_low_weight_cache_binds_threshold_source_and_matrices(
    tmp_path,
    monkeypatch,
):
    calls, matrices = _install_compact_oracle_fakes(
        monkeypatch,
        ["UNSAT", "UNSAT", "UNSAT"],
    )
    candidate = _compact_construction(1)
    first = audit_candidate(
        candidate,
        AuditConfig(state_dir=tmp_path, certify=False),
    )
    second = audit_candidate(
        candidate,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert len(calls) == 1
    assert first["compact_low_weight_sat_ladder"]["cache_hit"] is False
    assert second["compact_low_weight_sat_ladder"]["cache_hit"] is True
    cache = json.loads(
        state_paths(tmp_path, "compact-1")["compact_low_weight"].read_text()
    )
    binding = cache["binding"]
    assert binding["max_weight"] == 4
    assert len(binding["source_fingerprint"]) == 64
    assert set(binding["matrix_sha256"]) == {"hx", "hz", "lx", "lz"}

    # A threshold change and then a matrix change both invalidate the same
    # digest-keyed cache instead of inheriting a stale lower bound.
    threshold_changed = audit_candidate(
        candidate,
        AuditConfig(
            state_dir=tmp_path,
            certify=False,
            compact_low_weight_max_weight=3,
        ),
    )
    assert threshold_changed["compact_low_weight_sat_ladder"]["cache_hit"] is False
    matrices[0][0, 0] = 1
    matrix_changed = audit_candidate(
        candidate,
        AuditConfig(
            state_dir=tmp_path,
            certify=False,
            compact_low_weight_max_weight=3,
        ),
    )
    assert matrix_changed["compact_low_weight_sat_ladder"]["cache_hit"] is False
    assert [threshold for threshold, _ in calls] == [4, 3, 3]


def test_compact_unknown_cache_resumes_terminal_sectors_but_never_advances(
    tmp_path,
    monkeypatch,
):
    calls, _ = _install_compact_oracle_fakes(
        monkeypatch,
        ["UNKNOWN", "UNSAT"],
    )
    candidate = _compact_construction(2)
    first = audit_candidate(
        candidate,
        AuditConfig(state_dir=tmp_path, certify=False),
    )
    second = audit_candidate(
        candidate,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert first["status"] == "UNRESOLVED"
    assert first["retry_required"] is True
    assert second["retry_required"] is False
    assert len(calls) == 2


def test_two_block_sat_rejects_before_unrestricted_oracle(
    tmp_path,
    monkeypatch,
):
    calls, _ = _install_compact_oracle_fakes(
        monkeypatch,
        [],
        two_block_outcomes=["SAT"],
    )
    result = audit_candidate(
        _compact_construction(3),
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert calls == []
    assert result["status"] == "REJECTED"
    assert result["threshold_proof_source"] == (
        "two-block-sparse-kernel-oracle"
    )
    assert result["two_block_sparse_kernel_oracle"]["outcome"] == "SAT"


def test_two_block_unknown_is_advisory_and_uses_dynamic_cutoff(
    tmp_path,
    monkeypatch,
):
    calls, _ = _install_compact_oracle_fakes(
        monkeypatch,
        ["UNSAT"],
        two_block_outcomes=["UNKNOWN"],
    )
    candidate = _compact_construction(4)
    candidate["required_distance"] = 9
    result = audit_candidate(
        candidate,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert calls == [(4, ())]
    assert result["status"] == "UNRESOLVED"
    assert result["retry_required"] is False
    assert result["distance_lower_bound"] == 5
    assert result["two_block_sparse_kernel_oracle"]["outcome"] == "UNKNOWN"
    assert result["two_block_sparse_kernel_oracle"]["max_weight"] == 8
    cache = json.loads(
        state_paths(tmp_path, "compact-4")["compact_two_block"].read_text()
    )
    assert cache["binding"]["gate"] == (
        "qldpc-stage2-compact-two-block-cache"
    )
    assert cache["binding"]["max_weight"] == 8


def _novelty_result(
    canonical_digest: str,
    *,
    novel: bool = True,
) -> dict:
    registry = candidate_pool.load_registry()
    matched_entries = [] if novel else [{
        "id": "known",
        "family": "test",
        "provenance": ["test"],
        "construction_sha256": "f" * 64,
        "replay": {"verified": True},
    }]
    return {
        "status": "COMPLETE",
        "checked": True,
        "novel": novel,
        "code_type": "css",
        "canonical_digest": canonical_digest,
        "registry_version": registry["registry_version"],
        "registry_sha256": registry["registry_sha256"],
        "matched_entries": matched_entries,
        "replay_policy": {
            "schema_version": (
                candidate_pool.REGISTRY_REPLAY_POLICY_SCHEMA_VERSION
            ),
            "policy": candidate_pool.REGISTRY_REPLAY_POLICY,
            "digest_terminal": False,
            "index_fields": [
                "code_type",
                "n",
                "k",
                "canonical_digest",
            ],
            "entry_construction_required": True,
            "explicit_matrix_replay_required": True,
            "indexed_entries": len(matched_entries),
            "verified_entries": len(matched_entries),
            "complete": True,
        },
    }


def _parameterized_fake_code(n: int = 72, k: int = 4):
    return SimpleNamespace(num_qudits=n, dimension=k)


def _fake_certificate(
    identifier: str,
    *,
    passed: bool,
    exact: bool,
    failure_disposition: dict | None = None,
) -> dict:
    completed = 2 if exact else 0
    certificate = {
        "schema_version": 1,
        "certificate_type": "qldpc-css-bb-exact",
        "formulation": "css-logical-anticommutation-milp-v1",
        "test_identifier": identifier,
        "passed": passed,
        "claim": {"n": 72, "k": 1, "d": 1},
        "milp": {
            "exact": exact,
            "completed_directions": completed,
            "expected_directions": 2,
            "directions": [{} for _ in range(completed)],
        },
    }
    if failure_disposition is not None:
        checks = {
            "known_answer_gate": True,
            "css_bb_candidate": True,
            "candidate_rebuild": True,
            "css_commutation": True,
            "weight_and_degree_at_most_6": True,
            "connected_tanner_graph": True,
            "reported_n_matches": True,
            "reported_k_matches": True,
            "qldpc_k_crosscheck": True,
            "positive_reported_distance": True,
            "all_2k_milp_directions_optimal": True,
            "structural_audit_present": True,
            "structural_audit_reproduced": True,
            "expanded_registry_novel": True,
            "challenge_win": False,
            "reported_fom_matches": True,
        }
        certificate["failure_disposition"] = failure_disposition
        certificate["final_gate"] = {
            "schema_version": 1,
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": checks,
            "failures": ["challenge_win"],
            "win": {"passed": False},
        }
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def _ranked_snapshot_rows(count: int) -> list[dict]:
    rows = [
        {
            **_construction(marker),
            "proof_score": {
                "status": "PROMISING",
                "rejected": False,
            },
            "triage_identity": {
                "canonical_digest": f"snapshot-{marker:04d}",
                "digest_kind": "registry-canonical",
            },
        }
        for marker in range(count)
    ]
    return sorted(rows, key=candidate_pool._ranked_selection_key)


def _snapshot_counts(count: int) -> dict[str, int]:
    return {
        "input_records": count,
        "unique_candidates": count,
        "duplicate_records": 0,
        "rejected_candidates": 0,
        "eligible_candidates": count,
    }


_SNAPSHOT_SOLVER_RUNTIME = None


def _snapshot_solver_runtime():
    global _SNAPSHOT_SOLVER_RUNTIME
    if _SNAPSHOT_SOLVER_RUNTIME is None:
        _SNAPSHOT_SOLVER_RUNTIME = proof_runtime_fingerprint()
    return _SNAPSHOT_SOLVER_RUNTIME


def _snapshot_canonicalizer(row):
    return {
        **row,
        "novelty": {
            "checked": True,
            "novel": True,
            "canonical_digest": row["triage_identity"][
                "canonical_digest"
            ],
        },
    }


def test_ranked_snapshot_sorts_trusted_terminal_rows_after_eligible_rows():
    """A replayed terminal witness must own the rejected tail boundary."""

    eligible = {
        **_construction(0),
        "d": None,
        "proof_score": {
            "status": "UNSCREENED",
            "rejected": False,
        },
        "triage_identity": {
            "canonical_digest": "eligible",
            "digest_kind": "registry-canonical",
        },
    }
    terminal = {
        **_construction(1),
        "n": 144,
        "k": 2,
        "d": 2,
        # This is the exact stale-score shape that reached production: the
        # locally replayed oracle marker is authoritative even if an earlier
        # rank_record score still says UNSCREENED.
        "proof_score": {
            "status": "UNSCREENED",
            "rejected": False,
        },
        "trusted_search_oracle_rejection": {
            "validated": True,
            "outcome": "REJECTED",
            "source": "low_weight_oracle",
        },
        "triage_identity": {
            "canonical_digest": "terminal",
            "digest_kind": "registry-canonical",
        },
    }

    ranked = sorted(
        [terminal, eligible],
        key=candidate_pool._ranked_selection_key,
    )

    assert [
        row["triage_identity"]["canonical_digest"] for row in ranked
    ] == ["eligible", "terminal"]

    with pytest.raises(
        ValueError,
        match="terminal rejection score is inconsistent",
    ):
        candidate_pool._validate_ranked_snapshot_rows(
            ranked,
            {
                "input_records": 2,
                "unique_candidates": 2,
                "duplicate_records": 0,
                "rejected_candidates": 1,
                "eligible_candidates": 1,
            },
        )

    terminal["proof_score"] = {
        "status": "REJECTED",
        "rejected": True,
    }
    ranked = sorted(
        [terminal, eligible],
        key=candidate_pool._ranked_selection_key,
    )
    candidate_pool._validate_ranked_snapshot_rows(
        ranked,
        {
            "input_records": 2,
            "unique_candidates": 2,
            "duplicate_records": 0,
            "rejected_candidates": 1,
            "eligible_candidates": 1,
        },
    )


def test_basis_upper_bound_promotes_rejects_then_required_weight_near_misses():
    def row(name: str, upper: int | None) -> dict:
        value = {
            **_construction(0),
            "required_distance": 13,
            "proof_score": {"status": "UNSCREENED", "rejected": False},
            "triage_identity": {
                "canonical_digest": name,
                "digest_kind": "registry-canonical",
            },
            "stage2_structural_screen": {"status": "COMPLETE"},
            "static_eligibility": {"checked": True, "eligible": True},
        }
        if upper is not None:
            body = {
                "schema_version": 1,
                "kind": "qcode-logical-basis-upper-bound-v1",
                "method": "replayed-minimum-symplectic-basis-row",
                "available": True,
                "upper_bound": upper,
                "witness": {
                    "side": "Z",
                    "index": 0,
                    "dual_side": "X",
                    "dual_index": 0,
                    "weight": upper,
                    "bits": [1] * upper,
                },
            }
            value["static_eligibility"]["logical_basis_upper_bound"] = {
                **body,
                "report_sha256": candidate_pool._json_sha256(body),
            }
        return value

    ranked = sorted(
        [
            row("missing", None),
            row("headroom-five", 18),
            row("required-weight", 13),
            row("basis-reject", 12),
            row("headroom-two", 15),
        ],
        key=candidate_pool._ranked_selection_key,
    )
    assert [
        item["triage_identity"]["canonical_digest"] for item in ranked
    ] == [
        "basis-reject",
        "required-weight",
        "headroom-two",
        "headroom-five",
        "missing",
    ]


def _ranked_basis_row(
    name: str,
    upper: int | None,
    *,
    target_mode: str | None = None,
    proof_score: dict | None = None,
) -> dict:
    row = {
        **_construction(0),
        "required_distance": 13,
        "proof_score": proof_score or {
            "status": "UNSCREENED",
            "rejected": False,
        },
        "triage_identity": {
            "canonical_digest": name,
            "digest_kind": "registry-canonical",
        },
        "stage2_structural_screen": {"status": "COMPLETE"},
        "static_eligibility": {"checked": True, "eligible": True},
    }
    if target_mode is not None:
        row["target_mode"] = target_mode
    if upper is not None:
        body = {
            "schema_version": 1,
            "kind": "qcode-logical-basis-upper-bound-v1",
            "method": "replayed-minimum-symplectic-basis-row",
            "available": True,
            "upper_bound": upper,
            "witness": {
                "side": "Z",
                "index": 0,
                "dual_side": "X",
                "dual_index": 0,
                "weight": upper,
                "bits": [1] * upper,
            },
        }
        row["static_eligibility"]["logical_basis_upper_bound"] = {
            **body,
            "report_sha256": candidate_pool._json_sha256(body),
        }
    return row


@pytest.mark.parametrize("upper", [12, 13, 15, None])
def test_explicit_strict_target_preserves_legacy_rank_key(upper):
    legacy = _ranked_basis_row("same-candidate", upper)
    strict = _ranked_basis_row(
        "same-candidate",
        upper,
        target_mode=TARGET_MODE_SCALAR,
    )

    assert candidate_pool._ranked_selection_key(strict) == (
        candidate_pool._ranked_selection_key(legacy)
    )


@pytest.mark.parametrize(
    "target_mode",
    [TARGET_MODE_SCALAR_INCLUSIVE, TARGET_MODE_SCALAR_13_INCLUSIVE],
)
def test_inclusive_target_globally_prioritizes_basis_boundary(target_mode):
    weak_score = {"status": "UNSCREENED", "rejected": False}
    strong_score = {
        "status": "PROMISING",
        "rejected": False,
        "threshold_safe_directions": 8,
        "min_dual_ratio": 1.0,
        "terminal_dual_ratio": 1.0,
        "coverage": 1.0,
        "dual_coverage": 1.0,
    }
    ranked = sorted(
        [
            _ranked_basis_row(
                "missing", None,
                target_mode=target_mode,
                proof_score=strong_score,
            ),
            _ranked_basis_row(
                "above-boundary", 15,
                target_mode=target_mode,
                proof_score=strong_score,
            ),
            _ranked_basis_row(
                "basis-reject", 12,
                target_mode=target_mode,
                proof_score=strong_score,
            ),
            _ranked_basis_row(
                "boundary", 13,
                target_mode=target_mode,
                proof_score=weak_score,
            ),
        ],
        key=candidate_pool._ranked_selection_key,
    )

    assert [
        row["triage_identity"]["canonical_digest"] for row in ranked
    ] == [
        "boundary",
        "basis-reject",
        "above-boundary",
        "missing",
    ]


def test_stage2_cli_accepts_fom13_target_mode(tmp_path):
    args = candidate_pool.build_parser().parse_args([
        "candidates.jsonl",
        "--target-mode",
        TARGET_MODE_SCALAR_13_INCLUSIVE,
        "--state-dir",
        str(tmp_path / "state"),
        "--ranked-output",
        str(tmp_path / "ranked.jsonl"),
        "--summary-output",
        str(tmp_path / "summary.json"),
    ])

    assert args.target_mode == TARGET_MODE_SCALAR_13_INCLUSIVE


def test_ranked_snapshot_rejects_rejected_score_without_trusted_marker():
    row = {
        **_construction(0),
        "proof_score": {
            "status": "REJECTED",
            "rejected": True,
        },
        "triage_identity": {
            "canonical_digest": "untrusted-rejection",
            "digest_kind": "registry-canonical",
        },
    }

    with pytest.raises(
        ValueError,
        match="terminal rejection score is inconsistent",
    ):
        candidate_pool._validate_ranked_snapshot_rows(
            [row],
            {
                "input_records": 1,
                "unique_candidates": 1,
                "duplicate_records": 0,
                "rejected_candidates": 0,
                "eligible_candidates": 1,
            },
        )


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


def test_structural_ranking_keeps_timeout_retryable_at_tail(
    tmp_path,
    monkeypatch,
):
    candidates = tmp_path / "candidates.jsonl"
    candidates.write_text(
        "\n".join(
            json.dumps(_construction(marker)) for marker in (0, 1)
        )
        + "\n"
    )

    def structural_screen(rows, **_kwargs):
        completed = {
            **rows[0],
            "static_eligibility": {
                "checked": True,
                "eligible": True,
                "checks": {"candidate_rebuild": True},
                "failures": [],
                "n": 72,
                "k": 2,
            },
            "structural_novelty": {
                "checked": True,
                "novel": True,
                "canonical_digest": "b" * 64,
            },
        }
        return [completed], [], [{
            "candidate_index": 1,
            "input_sha256": (
                candidate_pool.structural_screen_input_sha256(rows[1])
            ),
            "attempt_count": 1,
            "failure": {
                "kind": "hard_timeout",
                "retryable": True,
            },
        }]

    monkeypatch.setattr(
        candidate_pool,
        "screen_css_results_with_deferred_cache",
        structural_screen,
    )
    monkeypatch.setattr(
        candidate_pool,
        "structural_screen_runtime_fingerprint",
        lambda: {"sha256": "c" * 64},
    )

    ranked, counts = (
        candidate_pool.rank_candidate_files_with_structural_cache(
            [candidates],
            structural_cache_dir=tmp_path / "cache",
            structural_max_workers=2,
            structural_hard_timeout=1,
        )
    )

    assert counts["structural_unresolved_candidates"] == 1
    assert counts["eligible_candidates"] == 2
    assert not candidate_pool._is_structural_screen_unresolved(ranked[0])
    assert candidate_pool._is_structural_screen_unresolved(ranked[1])
    candidate_pool._validate_ranked_snapshot_rows(ranked, counts)


def test_stage2_pair_timeout_cannot_be_merged_by_digest_and_retries_in_place(
    tmp_path,
    monkeypatch,
):
    candidates = tmp_path / "candidates.jsonl"
    candidates.write_text(
        "\n".join(
            json.dumps(_construction(marker)) for marker in (0, 1)
        )
        + "\n"
    )
    digest = "d" * 64
    runtime_sha256 = "e" * 64
    retry_attempts = 0

    def annotate(row, *, novel=True, pair_replay=None):
        annotated = {
            **row,
            "static_eligibility": {
                "checked": True,
                "eligible": True,
                "checks": {"candidate_rebuild": True},
                "failures": [],
                "n": 72,
                "k": 4,
            },
            "structural_novelty": {
                "checked": True,
                "novel": novel,
                "relation": (
                    None
                    if novel
                    else "within_run_css_tanner_permutation_equivalent"
                ),
                "canonical_digest": digest,
                "matched_reference": None if novel else "representative",
                "reference_digest": None if novel else digest,
                "explicit_isomorphism": pair_replay,
            },
        }
        if not novel:
            annotated["structural_rejection"] = "within_run_duplicate"
        return annotated

    def initial_screen(rows, **_kwargs):
        representative = annotate(rows[0])
        candidate = annotate(rows[1])
        pair_sha256 = candidate_pool.structural_pair_input_sha256(
            candidate,
            representative,
        )
        return [representative], [], [{
            "operation": "within_pool_isomorphism",
            "candidate_index": 1,
            "representative_index": 0,
            "canonical_digest": digest,
            "input_sha256": pair_sha256,
            "runtime_sha256": runtime_sha256,
            "candidate_input_sha256": (
                candidate_pool.structural_screen_input_sha256(rows[1])
            ),
            "representative_input_sha256": (
                candidate_pool.structural_screen_input_sha256(rows[0])
            ),
            "attempt_count": 1,
            "failure": {
                "kind": "hard_timeout",
                "retryable": True,
            },
        }]

    monkeypatch.setattr(
        candidate_pool,
        "screen_css_results_with_deferred_cache",
        initial_screen,
    )
    monkeypatch.setattr(
        candidate_pool,
        "structural_screen_runtime_fingerprint",
        lambda: {"sha256": runtime_sha256},
    )
    ranked, counts = (
        candidate_pool.rank_candidate_files_with_structural_cache(
            [candidates],
            structural_cache_dir=tmp_path / "cache",
            structural_max_workers=2,
            structural_hard_timeout=1,
        )
    )

    assert counts["unique_candidates"] == 2
    assert counts["duplicate_records"] == 0
    assert counts["structural_unresolved_candidates"] == 1
    representative = ranked[0]
    deferred = ranked[1]
    assert not candidate_pool._is_structural_screen_unresolved(
        representative
    )
    assert candidate_pool._is_pair_structural_unresolved(deferred)
    marker = deferred["stage2_structural_screen"]
    pair_sha256 = marker["pair_input_sha256"]
    assert marker["canonical_digest"] == digest
    assert marker["representative_input_sha256"] == (
        candidate_pool.structural_screen_input_sha256(
            marker["representative"]
        )
    )

    def retry_screen(rows, **_kwargs):
        nonlocal retry_attempts
        retry_attempts += 1
        representative_retry = annotate(rows[0])
        candidate_retry = annotate(rows[1])
        assert candidate_pool.structural_pair_input_sha256(
            candidate_retry,
            representative_retry,
        ) == pair_sha256
        if retry_attempts == 1:
            return [representative_retry], [], [{
                "operation": "within_pool_isomorphism",
                "candidate_index": 1,
                "representative_index": 0,
                "canonical_digest": digest,
                "input_sha256": pair_sha256,
                "runtime_sha256": runtime_sha256,
                "candidate_input_sha256": (
                    candidate_pool.structural_screen_input_sha256(rows[1])
                ),
                "representative_input_sha256": (
                    candidate_pool.structural_screen_input_sha256(rows[0])
                ),
                "attempt_count": 2,
                "failure": {
                    "kind": "hard_timeout",
                    "retryable": True,
                },
            }]
        block = 36
        replay = {
            "verified": True,
            "hx_preserved": True,
            "hz_preserved": True,
            "qubit_permutation": list(range(2 * block)),
            "x_check_permutation": list(range(block)),
            "z_check_permutation": list(range(block)),
        }
        completed = annotate(
            rows[1],
            novel=False,
            pair_replay=replay,
        )
        completed[candidate_pool.STRUCTURAL_PAIR_REPLAY_FIELD] = {
            "schema_version": (
                candidate_pool.STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION
            ),
            "status": "COMPLETE",
            "input_sha256": pair_sha256,
            "runtime_sha256": runtime_sha256,
            "candidate_input_sha256": (
                candidate_pool.structural_screen_input_sha256(rows[1])
            ),
            "representative_input_sha256": (
                candidate_pool.structural_screen_input_sha256(rows[0])
            ),
            "representative_index": 0,
            "canonical_digest": digest,
        }
        return [representative_retry], [completed], []

    monkeypatch.setattr(
        candidate_pool,
        "screen_css_results_with_deferred_cache",
        retry_screen,
    )
    with pytest.raises(candidate_pool.StructuralSelectionDeferredError):
        candidate_pool.resolve_structural_snapshot_row_for_audit(
            deferred,
            cache_dir=tmp_path / "cache",
            max_workers=2,
            hard_timeout=1,
        )
    resolved = candidate_pool.resolve_structural_snapshot_row_for_audit(
        deferred,
        cache_dir=tmp_path / "cache",
        max_workers=2,
        hard_timeout=2,
    )

    assert retry_attempts == 2
    assert resolved["campaign_skip_reason"] == "STRUCTURAL_DUPLICATE"
    assert resolved["stage2_structural_screen"]["status"] == "COMPLETE"
    assert resolved["stage2_structural_screen"][
        "pair_input_sha256"
    ] == pair_sha256
    assert resolved["within_pool_isomorphism_replay"][
        "input_sha256"
    ] == pair_sha256


def test_stage2_digest_collision_without_pair_replay_fails_closed(
    tmp_path,
    monkeypatch,
):
    candidates = tmp_path / "candidates.jsonl"
    candidates.write_text(
        "\n".join(
            json.dumps(_construction(marker)) for marker in (0, 1)
        )
        + "\n"
    )

    def unsafe_digest_only_screen(rows, **_kwargs):
        completed = []
        for row in rows:
            completed.append({
                **row,
                "static_eligibility": {
                    "checked": True,
                    "eligible": True,
                    "checks": {"candidate_rebuild": True},
                    "failures": [],
                    "n": 72,
                    "k": 2,
                },
                "structural_novelty": {
                    "checked": True,
                    "novel": True,
                    "relation": None,
                    "canonical_digest": "f" * 64,
                    "matched_reference": None,
                    "reference_digest": None,
                    "explicit_isomorphism": None,
                },
            })
        return completed, [], []

    monkeypatch.setattr(
        candidate_pool,
        "screen_css_results_with_deferred_cache",
        unsafe_digest_only_screen,
    )
    monkeypatch.setattr(
        candidate_pool,
        "structural_screen_runtime_fingerprint",
        lambda: {"sha256": "a" * 64},
    )

    with pytest.raises(
        ValueError,
        match="digest collision lacks pair or registry replay",
    ):
        candidate_pool.rank_candidate_files_with_structural_cache(
            [candidates],
            structural_cache_dir=tmp_path / "cache",
            structural_max_workers=2,
            structural_hard_timeout=1,
        )


def test_structural_snapshot_resolver_retries_same_cache_input(
    tmp_path,
    monkeypatch,
):
    row = {
        **_construction(0),
        "proof_score": {"status": "UNSCREENED", "rejected": False},
        "triage_identity": {
            "canonical_digest": "claim",
            "digest_kind": "structural-claim",
        },
    }
    screen_input = dict(row)
    screen_input.pop("n")
    screen_input.pop("k")
    input_sha256 = candidate_pool.structural_screen_input_sha256(
        screen_input
    )
    row["stage2_structural_screen"] = {
        "status": "UNRESOLVED",
        "retryable": True,
        "input_sha256": input_sha256,
    }
    attempts = 0

    def retry(rows, **_kwargs):
        nonlocal attempts
        attempts += 1
        assert len(rows) == 1
        assert candidate_pool.structural_screen_input_sha256(
            rows[0]
        ) == input_sha256
        if attempts == 1:
            return [], [{
                "candidate_index": 0,
                "input_sha256": input_sha256,
                "failure": {"kind": "hard_timeout", "retryable": True},
            }]
        return [{
            **rows[0],
            "static_eligibility": {
                "checked": True,
                "eligible": True,
                "checks": {"candidate_rebuild": True},
                "failures": [],
                "n": 72,
                "k": 4,
            },
            "structural_novelty": {
                "checked": True,
                "novel": True,
                "canonical_digest": "d" * 64,
            },
        }], []

    monkeypatch.setattr(
        candidate_pool,
        "annotate_css_results_with_deferred_cache",
        retry,
    )
    monkeypatch.setattr(
        candidate_pool,
        "structural_screen_runtime_fingerprint",
        lambda: {"sha256": "e" * 64},
    )
    monkeypatch.setattr(
        candidate_pool,
        "check_code_novelty",
        lambda *_args, **_kwargs: _novelty_result("d" * 64),
    )

    with pytest.raises(candidate_pool.StructuralSelectionDeferredError):
        candidate_pool.resolve_structural_snapshot_row_for_audit(
            row,
            cache_dir=tmp_path / "cache",
            max_workers=2,
            hard_timeout=1,
        )
    resolved = candidate_pool.resolve_structural_snapshot_row_for_audit(
        row,
        cache_dir=tmp_path / "cache",
        max_workers=2,
        hard_timeout=2,
    )

    assert attempts == 2
    assert resolved["canonical_digest"] == "d" * 64
    assert resolved["n"] == 72
    assert resolved["k"] == 4
    assert resolved["stage2_structural_screen"]["status"] == "COMPLETE"
    assert resolved["authoritative_geometry"]["selection_replay"][
        "cache_bound"
    ] is True


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
    assert ranked[0]["target_mode"] == TARGET_MODE_GIST
    assert ranked[0]["target"] == target_binding(72, 8, TARGET_MODE_GIST)
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
            "formulation": "css-sector-xor-cpsat-v1",
            "solver": "ortools-cp-sat",
            "success": False,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 14,
            "objective": None,
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


def test_jsonl_reader_rejects_unterminated_invalid_trailing_fragment(tmp_path):
    live = tmp_path / "live.jsonl"
    complete = _construction(1)
    live.write_text(json.dumps(complete) + "\n" + '{"trial":')

    with pytest.raises(ValueError, match="invalid JSON"):
        read_candidate_jsonl([live])

    malformed = tmp_path / "malformed.jsonl"
    malformed.write_text(json.dumps(complete) + "\n" + '{"trial":\n')
    with pytest.raises(ValueError, match="invalid JSON"):
        read_candidate_jsonl([malformed])

    valid_without_newline = tmp_path / "valid-no-newline.jsonl"
    valid_without_newline.write_text(json.dumps(complete))
    records, sources = read_candidate_jsonl([valid_without_newline])
    assert records == [complete]
    assert sources == [str(valid_without_newline)]


def test_worker_budget_prevents_solver_oversubscription():
    validate_worker_budget(2, 4, 8)
    with pytest.raises(ValueError, match="exceeds"):
        validate_worker_budget(3, 4, 8)
    with pytest.raises(ValueError, match="between 1 and 8"):
        validate_worker_budget(1, 9, 16)


def test_stage2_hard_wall_never_trusts_stale_terminal_artifact(tmp_path):
    digest = "e" * 64
    ranked = {
        **_construction(0),
        "triage_identity": {
            "canonical_digest": digest,
            "digest_kind": "registry-canonical",
        },
    }
    config = AuditConfig(state_dir=tmp_path, certify=False)
    path = state_paths(tmp_path, digest)["audit"]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({
        "schema_version": 1,
        "gate": "qldpc-frontier-xor-sector-screen",
        "status": "REJECTED",
        "candidate": {**_construction(1), "required_distance": 999},
        "required_distance": 999,
        "threshold_only": True,
        "completed_sectors": 1,
        "translation_symmetry": {"verified": True},
        "sectors": [{
            "sector": "X",
            "objective": 1,
            "operator": [1],
            "witness_verified": True,
        }],
    }))

    result = candidate_pool._stage2_hard_wall_result(
        ranked,
        config,
        hard_timeout_s=1,
        peer_timeout=False,
    )

    assert result["status"] == "UNRESOLVED"
    assert result["canonical_digest"] == digest
    assert result["completed_sectors"] == 0
    assert result["hard_wall"]["timed_out"] is True
    assert result["artifact_recovery"] == {
        "terminal_status_claimed": True,
        "strict_replay_status": "UNRESOLVED",
        "strict_replay_error": None,
        "retryable": True,
    }
    assert "recovered_after_worker_termination" not in result


def test_stage2_hard_wall_recovers_only_strictly_replayed_terminal_artifact(
    tmp_path,
):
    digest = "f" * 64
    ranked = {
        **_construction(0),
        "triage_identity": {
            "canonical_digest": digest,
            "digest_kind": "registry-canonical",
        },
    }
    config = AuditConfig(state_dir=tmp_path, certify=False)
    candidate = candidate_pool._construction_candidate(ranked, digest)
    symmetry = candidate_pool.verify_bb_translation_symmetry(candidate)
    assert symmetry["verified"] is True
    max_weight = int(candidate["required_distance"]) - 1
    sectors = [{
        "sector": sector,
        "formulation": "css-sector-xor-cpsat-v1",
        "solver": "ortools-cp-sat",
        "success": False,
        "threshold_infeasible": True,
        "status_name": "INFEASIBLE",
        "max_weight": max_weight,
        "objective": None,
        "operator": None,
        "anchor_indices": symmetry["orbit_representatives"],
    } for sector in ("X", "Z")]
    candidate_pool.write_artifact(
        state_paths(tmp_path, digest)["audit"],
        candidate,
        sectors,
        threshold_only=True,
        translation_symmetry=symmetry,
        cache_binding=candidate_pool._stage2_audit_cache_binding(
            candidate,
            symmetry,
        ),
    )

    result = candidate_pool._stage2_hard_wall_result(
        ranked,
        config,
        hard_timeout_s=1,
        peer_timeout=False,
    )

    assert result["status"] == "THRESHOLD_PROVEN"
    assert result["completed_sectors"] == 2
    assert result["recovered_after_worker_termination"] is True
    assert result["recovery_replay_verified"] is True
    assert result["certificate"] == {
        "attempted": False,
        "deferred": False,
    }


def test_stage2_hard_wall_rejects_source_stale_terminal_artifact(tmp_path):
    digest = "1" * 64
    ranked = {
        **_construction(0),
        "triage_identity": {
            "canonical_digest": digest,
            "digest_kind": "registry-canonical",
        },
    }
    config = AuditConfig(state_dir=tmp_path, certify=False)
    candidate = candidate_pool._construction_candidate(ranked, digest)
    symmetry = candidate_pool.verify_bb_translation_symmetry(candidate)
    max_weight = int(candidate["required_distance"]) - 1
    sectors = [{
        "sector": sector,
        "formulation": "css-sector-xor-cpsat-v1",
        "solver": "ortools-cp-sat",
        "success": False,
        "threshold_infeasible": True,
        "status_name": "INFEASIBLE",
        "max_weight": max_weight,
        "objective": None,
        "operator": None,
        "anchor_indices": symmetry["orbit_representatives"],
    } for sector in ("X", "Z")]
    stale_binding = candidate_pool._stage2_audit_cache_binding(
        candidate,
        symmetry,
    )
    stale_binding["source_fingerprint"] = "0" * 64
    candidate_pool.write_artifact(
        state_paths(tmp_path, digest)["audit"],
        candidate,
        sectors,
        threshold_only=True,
        translation_symmetry=symmetry,
        cache_binding=stale_binding,
    )

    result = candidate_pool._stage2_hard_wall_result(
        ranked,
        config,
        hard_timeout_s=1,
        peer_timeout=True,
    )

    assert result["status"] == "UNRESOLVED"
    assert result["completed_sectors"] == 0
    assert result["hard_wall"]["peer_timeout_interruption"] is True
    assert result["artifact_recovery"]["terminal_status_claimed"] is True
    assert result["artifact_recovery"]["retryable"] is True


def _basis_fastpath_ranked() -> dict:
    witness = {
        "side": "X",
        "index": 0,
        "dual_side": "Z",
        "dual_index": 0,
        "weight": 2,
        "bits": [1, 1] + [0] * 70,
    }
    return {
        **_construction(0),
        "triage_identity": {
            "canonical_digest": "2" * 64,
            "digest_kind": "registry-canonical",
        },
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "n": 72,
            "k": 2,
            "logical_basis_upper_bound": {
                "schema_version": 1,
                "kind": "qcode-logical-basis-upper-bound-v1",
                "method": "replayed-minimum-symplectic-basis-row",
                "available": True,
                "upper_bound": 2,
                "witness": witness,
                "report_sha256": "3" * 64,
            },
        },
    }


def test_default_bb_audit_replays_basis_rejection_before_xor(
    tmp_path,
    monkeypatch,
):
    ranked = _basis_fastpath_ranked()
    monkeypatch.setattr(
        candidate_pool,
        "replay_structural_logical_basis_rejection",
        lambda row, *, target_mode: SimpleNamespace(
            target_mode=target_mode,
            n=72,
            k=2,
            upper_bound=2,
            required_distance=21,
        ),
    )
    monkeypatch.setattr(
        candidate_pool,
        "verify_bb_translation_symmetry",
        lambda _candidate: pytest.fail(
            "replayed basis rejection must bypass symmetry and XOR"
        ),
    )
    monkeypatch.setattr(
        candidate_pool,
        "solve_sector",
        lambda _payload: pytest.fail(
            "replayed basis rejection must bypass the sector solver"
        ),
    )

    result = audit_candidate(
        ranked,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert result["status"] == "REJECTED"
    assert result["retry_required"] is False
    assert result["distance_upper_bound"] == 2
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_source"] == (
        "replayed-logical-basis-upper-bound"
    )
    assert result["completed_sectors"] == result["resumed_sectors"] == 0
    evidence = result["logical_basis_upper_bound"]
    unsigned = dict(evidence)
    evidence_sha256 = unsigned.pop("evidence_sha256")
    assert evidence_sha256 == candidate_pool._json_sha256(unsigned)
    assert evidence["fresh_rebuild_verified"] is True
    assert evidence["algebraic_replay_verified"] is True
    assert evidence["witness"] == ranked[
        "static_eligibility"
    ]["logical_basis_upper_bound"]["witness"]


def test_actual_twisted_torus_basis_witness_bypasses_xor(
    tmp_path,
    monkeypatch,
):
    bits = [int(index in {36, 39}) for index in range(72)]
    witness = {
        "side": "X",
        "index": 3,
        "dual_side": "Z",
        "dual_index": 3,
        "weight": 2,
        "bits": bits,
    }
    report_payload = {
        "schema_version": 1,
        "kind": "qcode-logical-basis-upper-bound-v1",
        "method": "replayed-minimum-symplectic-basis-row",
        "available": True,
        "upper_bound": 2,
        "witness": witness,
    }
    ranked = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 3]],
        "B_terms": [[0, 2], [0, 5], [1, 0], [1, 3]],
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 1,
        },
        "n": 72,
        "k": 36,
        "required_distance": 5,
        "triage_identity": {
            "canonical_digest": "4" * 64,
            "digest_kind": "registry-canonical",
        },
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "n": 72,
            "k": 36,
            "logical_basis_upper_bound": {
                **report_payload,
                "report_sha256": candidate_pool._json_sha256(report_payload),
            },
        },
    }
    monkeypatch.setattr(
        candidate_pool,
        "verify_bb_translation_symmetry",
        lambda _candidate: pytest.fail(
            "real basis replay must bypass symmetry and XOR"
        ),
    )

    result = audit_candidate(
        ranked,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert result["status"] == "REJECTED"
    assert result["distance_upper_bound"] == 2
    assert result["logical_basis_upper_bound"]["witness"] == witness
    assert result["logical_basis_upper_bound"]["fresh_rebuild_verified"] is True


@pytest.mark.parametrize("hinted_upper", [21, 999, True, None])
def test_nonrejecting_basis_hint_skips_fresh_replay(
    monkeypatch,
    hinted_upper,
):
    ranked = _basis_fastpath_ranked()
    ranked["static_eligibility"]["logical_basis_upper_bound"][
        "upper_bound"
    ] = hinted_upper
    monkeypatch.setattr(
        candidate_pool,
        "replay_structural_logical_basis_rejection",
        lambda *_args, **_kwargs: pytest.fail(
            "a non-rejecting scheduling hint must not rebuild the code"
        ),
    )

    result = candidate_pool._replayed_structural_basis_rejection_result(
        ranked,
        _construction(0),
        canonical_digest="2" * 64,
        target_mode=TARGET_MODE_SCALAR,
    )

    assert result is None


@pytest.mark.parametrize("mismatched_replay", [False, True])
def test_unavailable_or_mismatched_basis_replay_falls_through_to_xor(
    tmp_path,
    monkeypatch,
    mismatched_replay,
):
    ranked = _basis_fastpath_ranked()
    replayed = (
        SimpleNamespace(
            target_mode=TARGET_MODE_SCALAR,
            n=999,
            k=2,
            upper_bound=2,
            required_distance=21,
        )
        if mismatched_replay else None
    )
    monkeypatch.setattr(
        candidate_pool,
        "replay_structural_logical_basis_rejection",
        lambda _row, *, target_mode: replayed,
    )
    symmetry = {
        "verified": True,
        "orbit_representatives": [0, 36],
    }
    monkeypatch.setattr(
        candidate_pool,
        "verify_bb_translation_symmetry",
        lambda _candidate: symmetry,
    )
    safe_sectors = [{
        "sector": sector,
        "formulation": "css-sector-xor-cpsat-v1",
        "solver": "ortools-cp-sat",
        "success": False,
        "threshold_infeasible": True,
        "status_name": "INFEASIBLE",
        "max_weight": 20,
        "objective": None,
        "operator": None,
        "anchor_indices": [0, 36],
    } for sector in ("X", "Z")]
    monkeypatch.setattr(
        candidate_pool,
        "load_replayable_sectors",
        lambda *_args, **_kwargs: safe_sectors,
    )
    monkeypatch.setattr(
        candidate_pool,
        "solve_sector",
        lambda _payload: pytest.fail(
            "complete replayed XOR proof should not invoke the solver"
        ),
    )

    result = audit_candidate(
        ranked,
        AuditConfig(state_dir=tmp_path, certify=False),
    )

    assert result["status"] == "THRESHOLD_PROVEN"
    assert result["completed_sectors"] == 2
    assert "logical_basis_upper_bound" not in result


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
            "formulation": "css-sector-xor-cpsat-v1",
            "solver": "ortools-cp-sat",
            "success": False,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 20,
            "objective": None,
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
            "formulation": "css-sector-xor-cpsat-v1",
            "solver": "ortools-cp-sat",
            "success": False,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": max_weight,
            "objective": None,
            "operator": None,
            "anchor_indices": list(anchors),
        }

    def build(candidate, **kwargs):
        calls["built"].append((candidate, kwargs))
        certificate = {
            **_fake_certificate("cert-a", passed=True, exact=True),
            "claim": candidate,
        }
        certificate["certificate_sha256"] = _certificate_sha256(certificate)
        return certificate

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


def test_selection_and_certificate_caches_bind_installed_package_contents(
    tmp_path,
    monkeypatch,
):
    known_answer = tmp_path / "known.json"
    known_answer.write_text("{}\n")
    runtime = {"current": proof_runtime_fingerprint()}
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        lambda: runtime["current"],
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-stable",
    )
    rows = [_construction(1)]
    binding_before = candidate_pool._selection_binding(
        rows,
        top=1,
        known_answer_artifact=known_answer,
    )
    build_calls = []
    verification_calls = []

    def build(claim, **kwargs):
        build_calls.append(kwargs)
        return _fake_certificate(
            f"runtime-{len(build_calls)}",
            passed=True,
            exact=True,
        )

    def verify(certificate, **kwargs):
        verification_calls.append(kwargs)
        return {"passed": True}

    config = AuditConfig(
        state_dir=tmp_path / "state",
        known_answer_artifact=known_answer,
    )
    certify_candidate(
        rows[0],
        "runtime-bound",
        config,
        builder=build,
        verifier=verify,
    )

    runtime["current"] = json.loads(json.dumps(runtime["current"]))
    runtime["current"]["package_artifacts"]["networkx"]["files_sha256"] = (
        "f" * 64
    )
    binding_after = candidate_pool._selection_binding(
        rows,
        top=1,
        known_answer_artifact=known_answer,
    )
    second = certify_candidate(
        rows[0],
        "runtime-bound",
        config,
        builder=build,
        verifier=verify,
    )

    assert binding_after != binding_before
    assert len(build_calls) == len(verification_calls) == 2
    assert second["certificate_resumed"] is False
    assert second["verification_resumed"] is False
    metadata = json.loads(
        state_paths(
            config.state_dir,
            "runtime-bound",
        )["certificate_metadata"].read_text()
    )
    assert metadata["solver_runtime"] == runtime["current"]


@pytest.mark.parametrize(
    "dependency",
    (
        "humanize/audit_state.py",
            "humanize/state.py",
            "evaluation/coset_two_block_actions.v1.json",
            "evaluation/coset_two_block_actions.v2.json",
            "evaluation/selection_ledger.py",
        "scripts/screen_frontier_candidate.py",
        "scripts/screen_frontier_sat.py",
        "scripts/screen_frontier_twobga.py",
        "scripts/screen_frontier_xor.py",
    ),
)
def test_certificate_source_fingerprint_includes_audit_dependencies(
    tmp_path,
    monkeypatch,
    dependency,
):
    project = tmp_path / "qcode"
    for path in (
        project / "scripts" / "audit_candidate_pool.py",
        project / "scripts" / "stage2_structural_cache.py",
        project / "scripts" / "audit_direction_pool.py",
        project / "scripts" / "finalize_challenge.py",
        project / "scripts" / "screen_frontier_candidate.py",
        project / "scripts" / "screen_frontier_sat.py",
        project / "scripts" / "screen_frontier_twobga.py",
        project / "scripts" / "screen_frontier_xor.py",
        project / "tests" / "verify_known_answer_gate.py",
        project / "results" / "known_code_registry.json",
        project / "humanize" / "audit_state.py",
            project / "humanize" / "state.py",
            project / "evaluation" / "coset_two_block_actions.v1.json",
            project / "evaluation" / "coset_two_block_actions.v2.json",
            project / "evaluation" / "verifier.py",
        project / "evaluation" / "selection_ledger.py",
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
    source = project / dependency
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


def test_untyped_exact_negative_certificate_is_rebuilt(tmp_path):
    calls = []

    def build(claim, **kwargs):
        calls.append(kwargs)
        return _fake_certificate(
            f"untyped-{len(calls)}",
            passed=False,
            exact=True,
        )

    config = AuditConfig(state_dir=tmp_path)
    first = certify_candidate(
        _construction(1), "untyped-negative", config, builder=build,
    )
    second = certify_candidate(
        _construction(1), "untyped-negative", config, builder=build,
    )

    assert len(calls) == 2
    assert first["failure_disposition"]["status"] == "INCOMPLETE"
    assert second["certificate_resumed"] is False


def test_typed_candidate_rejection_is_terminally_cached(tmp_path):
    calls = []
    rejection = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }

    def build(claim, **kwargs):
        calls.append(kwargs)
        return _fake_certificate(
            "typed-rejection",
            passed=False,
            exact=True,
            failure_disposition=rejection,
        )

    config = AuditConfig(state_dir=tmp_path)
    first = certify_candidate(
        _construction(1), "typed-negative", config, builder=build,
    )
    second = certify_candidate(
        _construction(1), "typed-negative", config, builder=build,
    )

    assert len(calls) == 1
    assert first["failure_disposition"] == rejection
    assert second["certificate_resumed"] is True
    assert second["verification_resumed"] is True


def test_dependency_failure_cannot_be_cached_as_candidate_rejection(tmp_path):
    calls = []
    spoofed = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["KNOWN_ANSWER_GATE_UNVERIFIED"],
    }

    def build(claim, **kwargs):
        calls.append(kwargs)
        certificate = _fake_certificate(
            f"dependency-spoof-{len(calls)}",
            passed=False,
            exact=True,
            failure_disposition=spoofed,
        )
        certificate["final_gate"] = {
            "checks": {
                "known_answer_gate": False,
                "challenge_win": False,
            },
        }
        certificate["certificate_sha256"] = _certificate_sha256(certificate)
        return certificate

    config = AuditConfig(state_dir=tmp_path)
    first = certify_candidate(
        _construction(1), "dependency-spoof", config, builder=build,
    )
    second = certify_candidate(
        _construction(1), "dependency-spoof", config, builder=build,
    )

    assert len(calls) == 2
    assert first["failure_disposition"]["status"] == "INCOMPLETE"
    assert second["certificate_resumed"] is False


def test_certificate_cache_kind_mismatch_forces_rebuild(tmp_path):
    calls = []

    def build(claim, **kwargs):
        calls.append(kwargs)
        return _fake_certificate(
            f"kind-{len(calls)}",
            passed=True,
            exact=True,
        )

    config = AuditConfig(state_dir=tmp_path)
    certify_candidate(
        _construction(1),
        "wrong-cache-kind",
        config,
        builder=build,
        verifier=lambda *_args, **_kwargs: {"passed": True},
    )
    metadata_path = state_paths(
        tmp_path,
        "wrong-cache-kind",
    )["certificate_metadata"]
    metadata = json.loads(metadata_path.read_text())
    metadata["kind"] = "qldpc-certificate-verification-cache"
    metadata_path.write_text(json.dumps(metadata) + "\n")

    second = certify_candidate(
        _construction(1),
        "wrong-cache-kind",
        config,
        builder=build,
        verifier=lambda *_args, **_kwargs: {"passed": True},
    )

    assert len(calls) == 2
    assert second["certificate_resumed"] is False


def test_schema2_negative_cache_is_not_terminal(tmp_path):
    calls = []
    rejection = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }

    def build(claim, **kwargs):
        calls.append(kwargs)
        return _fake_certificate(
            f"schema-version-{len(calls)}",
            passed=False,
            exact=True,
            failure_disposition=rejection,
        )

    config = AuditConfig(state_dir=tmp_path)
    certify_candidate(
        _construction(1), "old-negative-cache", config, builder=build,
    )
    metadata_path = state_paths(
        tmp_path,
        "old-negative-cache",
    )["certificate_metadata"]
    metadata = json.loads(metadata_path.read_text())
    metadata["schema_version"] = 2
    metadata_path.write_text(json.dumps(metadata) + "\n")

    second = certify_candidate(
        _construction(1), "old-negative-cache", config, builder=build,
    )

    assert len(calls) == 2
    assert calls[1]["resume"] is False
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
    assert envelope["verification"]["passed"] is False
    assert envelope["verification"]["skipped"] is True
    assert envelope["verification"]["reason"] == (
        "certificate build did not pass the exact challenge gate"
    )
    assert envelope["verification"]["failure_disposition"]["status"] == (
        "INCOMPLETE"
    )


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
            "formulation": "css-sector-xor-cpsat-v1",
            "solver": "ortools-cp-sat",
            "success": False,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": 20,
            "objective": None,
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


def test_registry_unavailable_keeps_selection_cursor_at_retryable_barrier(
    tmp_path,
):
    row = {
        **_construction(0),
        "proof_score": {"status": "PROMISING", "rejected": False},
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
    }

    def canonicalizer(value):
        return canonicalize_for_audit(
            value,
            code_builder=lambda *args: _parameterized_fake_code(),
            registry_path=tmp_path / "temporarily-missing-registry.json",
        )

    selected, stats, page, ledger = candidate_pool._prepare_selection_page(
        [row],
        top=1,
        ledger_path=tmp_path / "selection.json",
        known_answer_artifact=tmp_path / "known-answer.json",
        canonicalizer=canonicalizer,
    )

    assert selected == []
    assert page is None
    assert ledger["cursor"] == 0
    assert ledger["pending"] is None
    assert stats["structural_unresolved_candidates"] == 1
    assert stats["unscanned_eligible_candidates"] == 1
    assert stats["selection_exhausted"] is False


def test_registry_source_change_keeps_selection_cursor_at_retryable_barrier(
    tmp_path,
    monkeypatch,
):
    row = {
        **_construction(0),
        "proof_score": {"status": "PROMISING", "rejected": False},
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
    }
    fingerprints = iter(("a" * 64, "b" * 64))
    monkeypatch.setattr(
        candidate_pool,
        "_novelty_source_fingerprint",
        lambda: next(fingerprints),
    )

    def canonicalizer(value):
        return canonicalize_for_audit(
            value,
            code_builder=lambda *args: _parameterized_fake_code(),
            novelty_checker=lambda *_args, **_kwargs: _novelty_result(
                "c" * 64
            ),
        )

    selected, stats, page, ledger = candidate_pool._prepare_selection_page(
        [row],
        top=1,
        ledger_path=tmp_path / "selection.json",
        known_answer_artifact=tmp_path / "known-answer.json",
        canonicalizer=canonicalizer,
    )

    assert selected == []
    assert page is None
    assert ledger["cursor"] == 0
    assert ledger["pending"] is None
    assert stats["structural_unresolved_candidates"] == 1
    assert stats["unscanned_eligible_candidates"] == 1
    assert stats["selection_exhausted"] is False


def test_incomplete_registry_replay_is_not_a_known_code_rejection():
    row = {
        **_construction(0),
        "proof_score": {"status": "PROMISING", "rejected": False},
        "triage_identity": {
            "canonical_digest": "claim-sha256:fallback",
            "digest_kind": "structural-claim",
        },
    }
    incomplete = {
        "status": "INCOMPLETE",
        "checked": False,
        "novel": None,
        "code_type": "css",
        "canonical_digest": "d" * 64,
        "registry_version": None,
        "registry_sha256": None,
        "matched_entries": [],
        "replay_policy": {
            "schema_version": 1,
            "policy": "explicit-construction-matrix-replay",
            "digest_terminal": False,
            "entry_construction_required": True,
            "explicit_matrix_replay_required": True,
            "indexed_entries": 0,
            "verified_entries": 0,
            "complete": False,
        },
        "failure": {
            "domain": "registry",
            "code": "REGISTRY_UNAVAILABLE_OR_INVALID",
            "detail": "temporary failure",
            "retryable": True,
            "terminal_candidate_rejection": False,
        },
    }

    selected, stats = select_audit_candidates(
        [row],
        1,
        canonicalizer=lambda value: canonicalize_for_audit(
            value,
            code_builder=lambda *args: _parameterized_fake_code(),
            novelty_checker=lambda *_args, **_kwargs: incomplete,
        ),
    )

    assert selected == []
    assert stats["known_codes_skipped"] == 0
    assert stats["structural_unresolved_candidates"] == 1
    assert stats["selection_exhausted"] is False


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
        "structural_unresolved_candidates": 0,
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
    deferred_payload = {
        "page_sha256": first_page["page_sha256"],
        "selected_digests": first_page["selected_digests"],
        "opaque_pipeline_owned_field": True,
    }
    ledger = acknowledge_selection_page(
        ledger,
        first_page,
        disposition="DEFERRED",
        deferred_entry={
            **deferred_payload,
            "entry_sha256": candidate_pool._json_sha256(
                deferred_payload
            ),
        },
    )
    deferred_sentinel = ledger["deferred_pages"][0]
    candidate_pool.atomic_write_json(ledger_path, ledger)

    second, second_stats, second_page, round_tripped_ledger = (
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
    assert round_tripped_ledger["deferred_pages"] == [deferred_sentinel]
    assert json.loads(ledger_path.read_text())["deferred_pages"] == [
        deferred_sentinel
    ]


def test_ranked_snapshot_reuses_ranked_pool_without_reranking(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(3)
    calls = []

    def ranker(paths):
        calls.append(tuple(paths))
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )

    first, first_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    second, second_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert first_cache_hit is False
    assert second_cache_hit is True
    assert first.identity == second.identity
    assert first.rows == second.rows == 3
    assert len(calls) == 1


def test_ranked_snapshot_reuses_executable_ctime_and_selection_uses_snapshot_binding(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(2)
    rank_calls = 0
    source_version = ["source-v1"]
    runtime = [proof_runtime_fingerprint()]

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        lambda: runtime[0],
    )

    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    _, _, first_page, _ = candidate_pool._prepare_snapshot_selection_page(
        snapshot,
        top=1,
        ledger_path=ledger_path,
        known_answer_artifact=tmp_path / "known.json",
        canonicalizer=_snapshot_canonicalizer,
    )

    runtime[0] = json.loads(json.dumps(runtime[0]))
    runtime[0]["interpreter"]["executable_file"]["ctime_ns"] += 1
    replayed_snapshot, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    assert cache_hit is True
    assert rank_calls == 1

    ledger_before = ledger_path.read_bytes()
    _, _, replayed_page, _ = (
        candidate_pool._prepare_snapshot_selection_page(
            replayed_snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )
    )
    assert replayed_page == first_page
    assert ledger_path.read_bytes() == ledger_before

    source_version[0] = "source-v2"
    live_binding = candidate_pool._selection_binding(
        (),
        top=1,
        known_answer_artifact=tmp_path / "known.json",
        ranked_snapshot_identity=replayed_snapshot.identity,
        ranked_size=replayed_snapshot.rows,
    )
    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="live snapshot dependencies changed",
    ):
        candidate_pool._prepare_snapshot_selection_page(
            replayed_snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )

    assert live_binding != first_page["binding_sha256"]
    assert ledger_path.read_bytes() == ledger_before


def test_snapshot_selection_source_mutation_fails_before_ledger_write(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(2)
    source_version = ["source-v1"]
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, _snapshot_counts(len(rows))),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    assert not ledger_path.exists()

    def mutate_source(row):
        source_version[0] = "source-v2"
        return _snapshot_canonicalizer(row)

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="live snapshot dependencies changed",
    ):
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=mutate_source,
        )

    assert not ledger_path.exists()


@pytest.mark.parametrize("ledger_progress", ("pending", "completed"))
def test_ranked_snapshot_dependency_mismatch_preserves_progressed_generation(
    tmp_path,
    monkeypatch,
    ledger_progress,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(2)
    rank_calls = 0
    source_version = ["source-v1"]

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    _, _, page, ledger = candidate_pool._prepare_snapshot_selection_page(
        snapshot,
        top=1,
        ledger_path=ledger_path,
        known_answer_artifact=tmp_path / "known.json",
        canonicalizer=_snapshot_canonicalizer,
    )
    if ledger_progress == "completed":
        ledger = acknowledge_selection_page(
            ledger,
            page,
            disposition="COMPLETED",
        )
        candidate_pool.atomic_write_json(ledger_path, ledger)

    protected_paths = (
        snapshot.snapshot_path,
        snapshot.offsets_path,
        snapshot.manifest_path,
        ledger_path,
    )
    protected_bytes = {
        path: path.read_bytes()
        for path in protected_paths
    }
    source_version[0] = "source-v2"

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="migration required",
    ):
        candidate_pool.prepare_ranked_snapshot(
            [candidate_input],
            ledger_path=ledger_path,
        )

    assert rank_calls == 1
    assert {
        path: path.read_bytes()
        for path in protected_paths
    } == protected_bytes


def test_ranked_snapshot_dependency_mismatch_can_rebuild_with_empty_ledger(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(2)
    rank_calls = 0
    source_version = ["source-v1"]

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    first, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    empty_ledger = new_selection_ledger(
        binding_sha256="e" * 64,
        snapshot_identity_sha256_value=(
            candidate_pool.snapshot_identity_sha256(first.identity)
        ),
        snapshot_rows=first.rows,
        eligible_rows=first.eligible_rows,
    )
    candidate_pool.atomic_write_json(ledger_path, empty_ledger)
    ledger_bytes = ledger_path.read_bytes()
    source_version[0] = "source-v2"

    rebuilt, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert cache_hit is False
    assert rank_calls == 2
    assert rebuilt.identity != first.identity
    assert ledger_path.read_bytes() == ledger_bytes


def test_existing_invalid_selection_ledger_never_becomes_genesis(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    ledger_path.write_text("{\"schema_version\":")
    ledger_bytes = ledger_path.read_bytes()
    rank_calls = []
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: rank_calls.append(tuple(paths)),
    )

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="not valid UTF-8 JSON",
    ):
        candidate_pool.prepare_ranked_snapshot(
            [candidate_input],
            ledger_path=ledger_path,
        )

    assert rank_calls == []
    assert ledger_path.read_bytes() == ledger_bytes


def test_selection_ledger_final_symlink_never_becomes_genesis(
    tmp_path,
    monkeypatch,
):
    target = tmp_path / "target.json"
    candidate_pool.atomic_write_json(
        target,
        new_selection_ledger(
            binding_sha256="a" * 64,
            snapshot_identity_sha256_value="b" * 64,
            snapshot_rows=1,
            eligible_rows=1,
        ),
    )
    ledger_path = tmp_path / "selection.json"
    ledger_path.symlink_to(target)
    rank_calls = []
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: rank_calls.append(tuple(paths)),
    )

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="regular nofollow file",
    ):
        candidate_pool.prepare_ranked_snapshot(
            [tmp_path / "candidates.jsonl"],
            ledger_path=ledger_path,
        )

    assert rank_calls == []
    assert ledger_path.is_symlink()


@pytest.mark.parametrize("failure_phase", ("prepare", "selection"))
def test_cli_classifies_ranked_snapshot_migration_required(
    tmp_path,
    monkeypatch,
    capsys,
    failure_phase,
):
    def raise_migration(*args, **kwargs):
        raise candidate_pool.RankedSnapshotMigrationRequired(
            "test migration boundary"
        )

    if failure_phase == "prepare":
        monkeypatch.setattr(
            candidate_pool,
            "prepare_ranked_snapshot",
            raise_migration,
        )
    else:
        snapshot = SimpleNamespace(counts={}, identity={})
        monkeypatch.setattr(
            candidate_pool,
            "prepare_ranked_snapshot",
            lambda *args, **kwargs: (snapshot, False),
        )
        monkeypatch.setattr(
            candidate_pool,
            "_prepare_snapshot_selection_page",
            raise_migration,
        )

    with pytest.raises(SystemExit) as raised:
        candidate_pool.main([
            str(tmp_path / "candidates.jsonl"),
            "--state-dir",
            str(tmp_path / "state"),
            "--ranked-output",
            str(tmp_path / "ranked.jsonl"),
            "--summary-output",
            str(tmp_path / "summary.json"),
            "--selection-ledger",
            str(tmp_path / "selection.json"),
        ])

    assert raised.value.code == 2
    assert (
        "RANKED_SNAPSHOT_MIGRATION_REQUIRED: "
        "test migration boundary"
    ) in capsys.readouterr().err


@pytest.mark.parametrize(
    "durable_kind",
    (
        "generation",
        "history",
        "deferred",
        "scheduler",
        "proof_config",
        "extra",
    ),
)
def test_only_strict_generation_zero_genesis_allows_snapshot_rebuild(
    tmp_path,
    monkeypatch,
    durable_kind,
):
    ledger_path = tmp_path / "selection.json"
    binding = "a" * 64
    identity = "b" * 64
    kwargs = {
        "binding_sha256": binding,
        "snapshot_identity_sha256_value": identity,
        "snapshot_rows": 1,
        "eligible_rows": 1,
    }
    if durable_kind == "generation":
        ledger = new_selection_ledger(**kwargs, generation=1)
    elif durable_kind == "history":
        ledger = new_selection_ledger(
            **kwargs,
            generation_history=[{"kind": "preserved-history"}],
        )
    elif durable_kind == "proof_config":
        ledger = new_selection_ledger(
            **kwargs,
            proof_config_sha256="c" * 64,
        )
    else:
        ledger = new_selection_ledger(**kwargs)
        if durable_kind == "deferred":
            scan = make_scan_evidence(
                snapshot_identity_sha256_value=identity,
                start_index=0,
                next_index=1,
                snapshot_rows=1,
                eligible_rows=1,
                selection_exhausted=True,
            )
            page = make_selection_page(
                binding_sha256=binding,
                snapshot_identity_sha256_value=identity,
                page_sequence=0,
                previous_ack_sha256=ledger["last_ack_sha256"],
                start_index=0,
                next_index=1,
                selected_digests=["candidate"],
                scan_evidence=scan,
            )
            ledger = install_pending_page(ledger, page)
            entry_payload = {"kind": "preserved-deferred"}
            ledger = acknowledge_selection_page(
                ledger,
                page,
                disposition="DEFERRED",
                deferred_entry={
                    **entry_payload,
                    "entry_sha256": candidate_pool._json_sha256(
                        entry_payload
                    ),
                },
            )
        elif durable_kind == "scheduler":
            ledger["adaptive_page_scheduler"] = {"preserved": True}
            ledger = seal_selection_ledger(ledger)
        else:
            ledger["future_extension"] = {"preserved": True}
            ledger = seal_selection_ledger(ledger)
    candidate_pool.atomic_write_json(ledger_path, ledger)
    rank_calls = []
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: rank_calls.append(tuple(paths)),
    )

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="contains durable state",
    ):
        candidate_pool.prepare_ranked_snapshot(
            [tmp_path / "candidates.jsonl"],
            ledger_path=ledger_path,
        )

    assert rank_calls == []


def test_rank_hook_cannot_publish_snapshot_over_new_pending_ledger(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(2)
    source_version = ["source-v1"]
    rank_calls = 0
    empty_ledger = None
    installed_pending = None

    def ranker(paths):
        nonlocal rank_calls, installed_pending
        rank_calls += 1
        if rank_calls == 2:
            assert empty_ledger is not None
            scan = make_scan_evidence(
                snapshot_identity_sha256_value=empty_ledger[
                    "snapshot_identity_sha256"
                ],
                start_index=0,
                next_index=1,
                snapshot_rows=empty_ledger["snapshot_rows"],
                eligible_rows=empty_ledger["eligible_rows"],
                selection_exhausted=False,
            )
            page = make_selection_page(
                binding_sha256=empty_ledger["binding_sha256"],
                snapshot_identity_sha256_value=empty_ledger[
                    "snapshot_identity_sha256"
                ],
                page_sequence=0,
                previous_ack_sha256=empty_ledger["last_ack_sha256"],
                start_index=0,
                next_index=1,
                selected_digests=["rank-hook-candidate"],
                scan_evidence=scan,
            )
            installed_pending = install_pending_page(empty_ledger, page)
            candidate_pool.atomic_write_json(
                ledger_path,
                installed_pending,
            )
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    empty_ledger = new_selection_ledger(
        binding_sha256="e" * 64,
        snapshot_identity_sha256_value=(
            candidate_pool.snapshot_identity_sha256(snapshot.identity)
        ),
        snapshot_rows=snapshot.rows,
        eligible_rows=snapshot.eligible_rows,
    )
    candidate_pool.atomic_write_json(ledger_path, empty_ledger)
    protected_paths = (
        snapshot.snapshot_path,
        snapshot.offsets_path,
        snapshot.manifest_path,
    )
    protected_bytes = {
        path: path.read_bytes()
        for path in protected_paths
    }
    source_version[0] = "source-v2"

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="selection ledger changed while ranking",
    ):
        candidate_pool.prepare_ranked_snapshot(
            [candidate_input],
            ledger_path=ledger_path,
        )

    assert rank_calls == 2
    assert json.loads(ledger_path.read_text()) == installed_pending
    assert {
        path: path.read_bytes()
        for path in protected_paths
    } == protected_bytes


def test_ranked_snapshot_target_mode_is_a_cache_dependency(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(1)
    calls = []

    def ranker(paths, *, target_mode=TARGET_MODE_GIST):
        calls.append(target_mode)
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )

    candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
        target_mode=TARGET_MODE_GIST,
    )
    _, scalar_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
        target_mode=TARGET_MODE_SCALAR,
    )

    assert scalar_cache_hit is False
    assert calls == [TARGET_MODE_GIST, TARGET_MODE_SCALAR]


def test_ranked_snapshot_page_decodes_only_rows_needed(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(300)
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, _snapshot_counts(len(rows))),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=tmp_path / "selection.json",
    )
    original_loads = json.loads
    decoded = []

    def tracked_loads(payload, *args, **kwargs):
        decoded.append(payload)
        return original_loads(payload, *args, **kwargs)

    monkeypatch.setattr(candidate_pool.json, "loads", tracked_loads)
    selected, stats, next_index = (
        candidate_pool._select_snapshot_audit_page(
            snapshot,
            1,
            start_index=0,
            seen_digests=(),
            canonicalizer=_snapshot_canonicalizer,
        )
    )

    assert len(selected) == 1
    assert next_index == 1
    assert stats["unscanned_eligible_candidates"] == 299
    assert len(decoded) == 1


def test_ranked_snapshot_ledger_paginates_without_reranking(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ledger_path = tmp_path / "selection.json"
    rows = _ranked_snapshot_rows(3)
    rank_calls = 0

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, first_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    first, _, first_page, _ = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )
    )
    ledger = json.loads(ledger_path.read_text())
    ledger = acknowledge_selection_page(
        ledger,
        first_page,
        disposition="COMPLETED",
    )
    candidate_pool.atomic_write_json(ledger_path, ledger)

    replayed_snapshot, second_cache_hit = (
        candidate_pool.prepare_ranked_snapshot(
            [candidate_input],
            ledger_path=ledger_path,
        )
    )
    second, _, second_page, _ = (
        candidate_pool._prepare_snapshot_selection_page(
            replayed_snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )
    )

    assert first_cache_hit is False
    assert second_cache_hit is True
    assert rank_calls == 1
    assert first[0]["source"] != second[0]["source"]
    assert second_page["start_index"] == first_page["next_index"]


def test_structural_unresolved_tail_retries_without_rotating_snapshot_or_cursor(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    rows[1] = {
        **rows[1],
        "stage2_structural_screen": {
            "status": "UNRESOLVED",
            "retryable": True,
            "input_sha256": "a" * 64,
        },
    }
    rows.sort(key=candidate_pool._ranked_selection_key)
    counts = {
        **_snapshot_counts(2),
        "structural_unresolved_candidates": 1,
    }
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, counts),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    assert cache_hit is False
    snapshot_identity = dict(snapshot.identity)
    resolved = False

    def canonicalizer(row):
        if (
            candidate_pool._is_structural_screen_unresolved(row)
            and not resolved
        ):
            raise candidate_pool.StructuralSelectionDeferredError("retry")
        return _snapshot_canonicalizer(row)

    first, first_stats, first_page, ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )
    assert len(first) == 1
    assert first_stats["selection_exhausted"] is False
    assert first_page["start_index"] == 0
    assert first_page["next_index"] == 1
    acknowledged = acknowledge_selection_page(
        ledger,
        first_page,
        disposition="COMPLETED",
    )
    candidate_pool.atomic_write_json(ledger_path, acknowledged)

    replayed_snapshot, replay_cache_hit = (
        candidate_pool.prepare_ranked_snapshot(
            [candidate_input],
            ledger_path=ledger_path,
        )
    )
    assert replay_cache_hit is True
    assert replayed_snapshot.identity == snapshot_identity
    blocked, blocked_stats, blocked_page, blocked_ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            replayed_snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )
    assert blocked == []
    assert blocked_page is None
    assert blocked_stats["structural_unresolved_candidates"] == 1
    assert blocked_stats["selection_exhausted"] is False
    assert blocked_ledger["cursor"] == 1
    assert blocked_ledger["pending"] is None

    resolved = True
    selected, final_stats, final_page, final_ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            replayed_snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )
    assert len(selected) == 1
    assert final_stats["selection_exhausted"] is True
    assert final_stats["structural_unresolved_candidates"] == 0
    assert final_page["start_index"] == 1
    assert final_page["next_index"] == 2
    assert final_ledger["cursor"] == 1
    assert final_ledger["pending"] == final_page
    assert replayed_snapshot.identity == snapshot_identity


@pytest.mark.parametrize(
    "first_resolution",
    ("STRUCTURAL_INELIGIBLE", "KNOWN_CODE", "STRUCTURAL_DUPLICATE"),
)
def test_empty_nonterminal_page_commits_only_to_next_unresolved_barrier(
    tmp_path,
    monkeypatch,
    first_resolution,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    for index, row in enumerate(rows):
        row["stage2_structural_screen"] = {
            "status": "UNRESOLVED",
            "retryable": True,
            "input_sha256": f"{index + 1:064x}",
        }
    rows.sort(key=candidate_pool._ranked_selection_key)
    counts = {
        **_snapshot_counts(2),
        "structural_unresolved_candidates": 2,
    }
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, counts),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    def canonicalizer(row):
        if row["source"] == "candidate-1":
            raise candidate_pool.StructuralSelectionDeferredError(
                "second barrier remains unresolved"
            )
        if first_resolution == "KNOWN_CODE":
            return {
                **row,
                "novelty": {
                    "checked": True,
                    "novel": False,
                    "canonical_digest": "known",
                },
            }
        return {
            **row,
            "campaign_skip_reason": first_resolution,
        }

    selected, stats, page, ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )

    assert selected == []
    assert page is not None
    assert page["selected_digests"] == []
    assert page["start_index"] == 0
    assert page["next_index"] == 1
    assert page["scan_evidence"]["selection_exhausted"] is False
    assert stats["selection_exhausted"] is False
    assert stats["structural_unresolved_candidates"] == 1

    acknowledged = acknowledge_selection_page(
        ledger,
        page,
        disposition="COMPLETED",
    )
    assert acknowledged["cursor"] == 1
    assert acknowledged["committed_digests"] == []
    candidate_pool.atomic_write_json(ledger_path, acknowledged)

    blocked, blocked_stats, blocked_page, blocked_ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=canonicalizer,
        )
    )
    assert blocked == []
    assert blocked_page is None
    assert blocked_ledger["cursor"] == 1
    assert blocked_ledger["pending"] is None
    assert blocked_stats["selection_exhausted"] is False
    assert blocked_stats["structural_unresolved_candidates"] == 1


@pytest.mark.parametrize(
    ("artifact_attribute", "error"),
    (
        ("snapshot_path", "data chunk hash mismatch"),
        ("offsets_path", "offset chunk hash mismatch"),
    ),
)
def test_ranked_snapshot_detects_same_stat_in_place_tampering(
    tmp_path,
    monkeypatch,
    artifact_attribute,
    error,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(3)
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, _snapshot_counts(len(rows))),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=tmp_path / "selection.json",
    )
    artifact_path = getattr(snapshot, artifact_attribute)
    original_stat = artifact_path.stat()
    payload = bytearray(artifact_path.read_bytes())
    payload[0] ^= 1
    with artifact_path.open("r+b") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    os.utime(
        artifact_path,
        ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns),
    )
    restored_stat = artifact_path.stat()
    assert restored_stat.st_ino == original_stat.st_ino
    assert restored_stat.st_size == original_stat.st_size
    assert restored_stat.st_mtime_ns == original_stat.st_mtime_ns

    with pytest.raises(ValueError, match=error):
        candidate_pool._select_snapshot_audit_page(
            snapshot,
            1,
            start_index=0,
            seen_digests=(),
            canonicalizer=_snapshot_canonicalizer,
        )


def test_ranked_snapshot_invalidates_changed_input_and_source(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    rank_calls = 0
    source_version = ["source-v1"]

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: source_version[0],
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    original_stat = candidate_input.stat()
    with candidate_input.open("r+b") as stream:
        stream.write(b"[]\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.utime(
        candidate_input,
        ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns),
    )
    changed_stat = candidate_input.stat()
    assert changed_stat.st_ino == original_stat.st_ino
    assert changed_stat.st_size == original_stat.st_size
    assert changed_stat.st_mtime_ns == original_stat.st_mtime_ns
    _, input_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    source_version[0] = "source-v2"
    _, source_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert input_cache_hit is False
    assert source_cache_hit is False
    assert rank_calls == 3


def test_ranked_snapshot_manifest_field_tamper_rebuilds_fail_closed(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    rank_calls = 0

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    manifest = json.loads(snapshot.manifest_path.read_text())
    manifest["created_at"] += 1
    candidate_pool.atomic_write_json(snapshot.manifest_path, manifest)

    _, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert cache_hit is False
    assert rank_calls == 2


def test_ranked_snapshot_eligible_count_forgery_fails_boundary_replay(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(3)
    rank_calls = 0

    def ranker(paths):
        nonlocal rank_calls
        rank_calls += 1
        return rows, _snapshot_counts(len(rows))

    monkeypatch.setattr(candidate_pool, "rank_candidate_files", ranker)
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    manifest = json.loads(snapshot.manifest_path.read_text())
    manifest["counts"]["eligible_candidates"] = 2
    manifest["counts"]["rejected_candidates"] = 1
    manifest["identity"]["eligible_rows"] = 2
    manifest["identity"]["counts_sha256"] = candidate_pool._json_sha256(
        manifest["counts"],
    )
    unsigned = dict(manifest)
    unsigned.pop("manifest_sha256")
    manifest["manifest_sha256"] = candidate_pool._json_sha256(unsigned)
    candidate_pool.atomic_write_json(snapshot.manifest_path, manifest)

    _, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert cache_hit is False
    assert rank_calls == 2


def test_ranked_snapshot_replays_real_eligible_terminal_boundary(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    rows[-1] = {
        **rows[-1],
        "proof_score": {
            "status": "REJECTED",
            "rejected": True,
        },
        "trusted_stage1_audit": {
            "validated": True,
            "outcome": "REJECTED",
        },
    }
    counts = _snapshot_counts(2)
    counts["eligible_candidates"] = 1
    counts["rejected_candidates"] = 1
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, counts),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"

    first, first_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    second, second_cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert first_cache_hit is False
    assert second_cache_hit is True
    assert first.rows == second.rows == 2
    assert first.eligible_rows == second.eligible_rows == 1


def test_zero_row_snapshot_emits_only_trusted_terminal_root_page(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("")
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: ([], _snapshot_counts(0)),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, cache_hit = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )

    assert cache_hit is False
    assert snapshot.rows == snapshot.eligible_rows == 0
    selected, stats, page, ledger = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )
    )
    assert selected == []
    assert stats["selection_exhausted"] is True
    assert page["start_index"] == page["next_index"] == 0
    assert page["page_sequence"] == 0
    assert page["scan_evidence"]["eligible_rows"] == 0
    assert ledger["cursor"] == 0
    assert ledger["pending"] == page


def test_legacy_selection_ledger_requires_explicit_migration(
    tmp_path,
    monkeypatch,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(2)
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, _snapshot_counts(len(rows))),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    _, _, first_page, _ = (
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )
    )
    forged = {
        "schema_version": 1,
        "gate": "qldpc-stage2-selection-ledger",
        "binding_sha256": first_page["binding_sha256"],
        "cursor": snapshot.eligible_rows,
        "committed_digests": ["forged-skip"],
        "completed_pages": 99,
        "pending": None,
    }
    candidate_pool.atomic_write_json(ledger_path, forged)
    ledger_bytes = ledger_path.read_bytes()

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="existing selection ledger is invalid",
    ):
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )

    assert ledger_path.read_bytes() == ledger_bytes


def test_stale_sealed_selection_ledger_progress_requires_migration(tmp_path):
    ledger_path = tmp_path / "selection.json"
    old_binding = "a" * 64
    old_snapshot = "b" * 64
    ledger = new_selection_ledger(
        binding_sha256=old_binding,
        snapshot_identity_sha256_value=old_snapshot,
        snapshot_rows=2,
        eligible_rows=2,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=old_snapshot,
        start_index=0,
        next_index=1,
        snapshot_rows=2,
        eligible_rows=2,
        selection_exhausted=False,
    )
    page = make_selection_page(
        binding_sha256=old_binding,
        snapshot_identity_sha256_value=old_snapshot,
        page_sequence=0,
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=0,
        next_index=1,
        selected_digests=["candidate"],
        scan_evidence=scan,
    )
    candidate_pool.atomic_write_json(
        ledger_path,
        install_pending_page(ledger, page),
    )
    ledger_bytes = ledger_path.read_bytes()

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="stale selection ledger",
    ):
        candidate_pool._load_selection_ledger(
            ledger_path,
            binding_sha256="c" * 64,
            snapshot_identity_sha256_value="d" * 64,
            snapshot_rows=3,
            eligible_rows=3,
        )

    assert ledger_path.read_bytes() == ledger_bytes


def test_stale_sealed_empty_selection_ledger_can_restart(tmp_path):
    ledger_path = tmp_path / "selection.json"
    candidate_pool.atomic_write_json(
        ledger_path,
        new_selection_ledger(
            binding_sha256="a" * 64,
            snapshot_identity_sha256_value="b" * 64,
            snapshot_rows=2,
            eligible_rows=2,
        ),
    )

    restarted = candidate_pool._load_selection_ledger(
        ledger_path,
        binding_sha256="c" * 64,
        snapshot_identity_sha256_value="d" * 64,
        snapshot_rows=3,
        eligible_rows=3,
    )

    assert restarted["binding_sha256"] == "c" * 64
    assert restarted["snapshot_identity_sha256"] == "d" * 64
    assert restarted["cursor"] == restarted["completed_pages"] == 0
    assert restarted["committed_digests"] == []
    assert restarted["pending"] is None


@pytest.mark.parametrize("forgery", ("cursor", "committed"))
def test_selection_ledger_ack_chain_rejects_forged_progress(
    tmp_path,
    monkeypatch,
    forgery,
):
    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    rows = _ranked_snapshot_rows(3)
    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths: (rows, _snapshot_counts(len(rows))),
    )
    monkeypatch.setattr(
        candidate_pool,
        "certificate_source_fingerprint",
        lambda: "source-v1",
    )
    monkeypatch.setattr(
        candidate_pool,
        "solver_runtime_fingerprint",
        _snapshot_solver_runtime,
    )
    ledger_path = tmp_path / "selection.json"
    snapshot, _ = candidate_pool.prepare_ranked_snapshot(
        [candidate_input],
        ledger_path=ledger_path,
    )
    _, _, page, _ = candidate_pool._prepare_snapshot_selection_page(
        snapshot,
        top=1,
        ledger_path=ledger_path,
        known_answer_artifact=tmp_path / "known.json",
        canonicalizer=_snapshot_canonicalizer,
    )
    ledger = acknowledge_selection_page(
        json.loads(ledger_path.read_text()),
        page,
        disposition="COMPLETED",
    )
    if forgery == "cursor":
        ledger["cursor"] = snapshot.eligible_rows
    else:
        ledger["committed_digests"].append("forged-digest")
    # Even an attacker who refreshes the outer progress seal cannot invent
    # the missing acknowledgement-chain history.
    candidate_pool.atomic_write_json(
        ledger_path,
        seal_selection_ledger(ledger),
    )

    with pytest.raises(
        candidate_pool.RankedSnapshotMigrationRequired,
        match="existing selection ledger is invalid",
    ):
        candidate_pool._prepare_snapshot_selection_page(
            snapshot,
            top=1,
            ledger_path=ledger_path,
            known_answer_artifact=tmp_path / "known.json",
            canonicalizer=_snapshot_canonicalizer,
        )


def test_deferred_ack_requires_exact_deferred_entry_sequence():
    binding = "a" * 64
    snapshot_identity = "b" * 64
    ledger = new_selection_ledger(
        binding_sha256=binding,
        snapshot_identity_sha256_value=snapshot_identity,
        snapshot_rows=2,
        eligible_rows=2,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=snapshot_identity,
        start_index=0,
        next_index=1,
        snapshot_rows=2,
        eligible_rows=2,
        selection_exhausted=False,
    )
    page = make_selection_page(
        binding_sha256=binding,
        snapshot_identity_sha256_value=snapshot_identity,
        page_sequence=0,
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=0,
        next_index=1,
        selected_digests=["deferred-candidate"],
        scan_evidence=scan,
    )
    ledger = install_pending_page(ledger, page)
    entry_payload = {"kind": "test-deferred-entry"}
    entry = {
        **entry_payload,
        "entry_sha256": candidate_pool._json_sha256(entry_payload),
    }
    acknowledged = acknowledge_selection_page(
        ledger,
        page,
        disposition="DEFERRED",
        deferred_entry=entry,
    )
    validate_selection_ledger(
        acknowledged,
        binding_sha256=binding,
        snapshot_identity_sha256_value=snapshot_identity,
        snapshot_rows=2,
        eligible_rows=2,
    )
    forged = dict(acknowledged)
    forged["deferred_pages"] = []

    with pytest.raises(ValueError, match="deferred acknowledgements"):
        validate_selection_ledger(
            seal_selection_ledger(forged),
            binding_sha256=binding,
            snapshot_identity_sha256_value=snapshot_identity,
            snapshot_rows=2,
            eligible_rows=2,
        )


def test_nonempty_all_rejected_root_page_can_be_acknowledged():
    binding = "a" * 64
    snapshot_identity = "b" * 64
    ledger = new_selection_ledger(
        binding_sha256=binding,
        snapshot_identity_sha256_value=snapshot_identity,
        snapshot_rows=1,
        eligible_rows=0,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=snapshot_identity,
        start_index=0,
        next_index=0,
        snapshot_rows=1,
        eligible_rows=0,
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=binding,
        snapshot_identity_sha256_value=snapshot_identity,
        page_sequence=0,
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=0,
        next_index=0,
        selected_digests=[],
        scan_evidence=scan,
    )
    ledger = install_pending_page(ledger, page)
    acknowledged = acknowledge_selection_page(
        ledger,
        page,
        disposition="COMPLETED",
    )

    assert acknowledged["cursor"] == 0
    assert acknowledged["completed_pages"] == 1
    assert acknowledged["pending"] is None
    assert len(acknowledged["ack_chain"]) == 1
