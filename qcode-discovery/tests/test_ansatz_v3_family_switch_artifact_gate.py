from __future__ import annotations

import copy
from pathlib import Path

import evaluation.ansatz_v3_contract as gate
from evaluation.formal_audit_quota import load_quota_contract


PROJECT = Path(__file__).resolve().parents[1]
FINITE = PROJECT / "configs/twisted_torus_ansatz_v3.finite_domain.v1.json"
QUOTA = PROJECT / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"


def _fixture() -> tuple[dict, dict, dict, dict]:
    finite = gate.load_finite_domain_contract(FINITE)
    quota = load_quota_contract(QUOTA)
    candidates = [{
        "canonical_digest": "a" * 64,
        "candidate_key": "b" * 20,
        "n": 100,
        "k": 1,
        "trusted_upper_bound": {
            "kind": "replayed-logical-witness",
            "replayed": True,
            "weight": 8,
        },
        "fom_gt_12_excluded": True,
    }]
    counts = {str(row["volume"]): row["quota"] for row in quota["volume_quotas"]}
    replay = {
        "realized_domain_manifest_sha256": "c" * 64,
        "stage2_selection_ledger_file_sha256": "d" * 64,
        "candidate_key_set_sha256": "e" * 64,
        "replayed_candidate_set_sha256": "f" * 64,
        "total_unique_candidates": 1,
        "candidates": candidates,
        "campaign": {
            "status": "search-complete",
            "rounds_completed": finite["search_budget"]["rounds"],
            "pending_round": None,
        },
        "formal_audit": {"unfilled_slots": 0, "volume_counts": counts},
    }
    evidence = {
        "schema_version": 1,
        "kind": gate.FAMILY_SWITCH_EVIDENCE_KIND,
        "representation_id": finite["representation_id"],
        "finite_domain_contract_sha256": finite["contract_sha256"],
        "formal_audit_quota_sha256": quota["contract_sha256"],
        "campaign": {
            "sealed": True,
            "rounds_completed": finite["search_budget"]["rounds"],
            "pending_round": None,
        },
        "realized_domain": {
            "manifest_complete": True,
            "total_unique_candidates": 1,
            "audited_unique_candidates": 1,
            "manifest_sha256": replay["realized_domain_manifest_sha256"],
            "candidate_key_set_sha256": replay["candidate_key_set_sha256"],
        },
        "stage2": {
            "ranked_snapshot_exhausted": True,
            "selection_ledger_pending": None,
            "unresolved_candidates": 0,
            "unknown_candidates": 0,
            "selection_ledger_sha256": replay["stage2_selection_ledger_file_sha256"],
            "replayed_candidate_set_sha256": replay["replayed_candidate_set_sha256"],
        },
        "candidates": candidates,
        "formal_audit": replay["formal_audit"],
        "trusted_novel_wins": 0,
        "unresolved_items": [],
    }
    return finite, quota, replay, evidence


def test_invented_replayed_rows_cannot_open_gate() -> None:
    finite, quota, _replay, evidence = _fixture()
    decision = gate.family_switch_decision(
        evidence, contract=finite, quota_contract=quota
    )
    assert decision["eligible_for_manual_family_transition"] is False
    assert "bound_artifact_replay_missing" in decision["block_reasons"]


def test_only_exact_fresh_artifact_replay_can_open_gate(monkeypatch, tmp_path) -> None:
    finite, quota, replay, evidence = _fixture()
    monkeypatch.setattr(gate, "replay_family_switch_artifacts", lambda **_kw: replay)
    decision = gate.family_switch_decision(
        evidence,
        contract=finite,
        quota_contract=quota,
        realized_domain_manifest_path=tmp_path / "domain.json",
        stage2_selection_ledger_path=tmp_path / "ledger.json",
    )
    assert decision["eligible_for_manual_family_transition"] is True

    forged = copy.deepcopy(evidence)
    forged["candidates"][0]["canonical_digest"] = "invented"
    decision = gate.family_switch_decision(
        forged,
        contract=finite,
        quota_contract=quota,
        realized_domain_manifest_path=tmp_path / "domain.json",
        stage2_selection_ledger_path=tmp_path / "ledger.json",
    )
    assert decision["eligible_for_manual_family_transition"] is False
    assert "candidate_witness_replay_mismatch" in decision["block_reasons"]
