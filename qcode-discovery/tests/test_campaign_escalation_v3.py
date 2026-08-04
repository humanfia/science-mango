"""Real-artifact integration coverage for campaign escalation policy v3."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

import humanize.flow as flow_module
from humanize.escalation import (
    ParentEvidenceError,
    plan_campaign_escalation,
    reconcile_campaign_escalation,
)


PARENT_REPRESENTATION = "css-bb-cover-algebra-generator-v2"
ANSATZ_REPRESENTATION = "css-bb-novel-ansatz-generator-v2"
ANSATZ_TEMPLATE = "css-bb-novel-ansatz-generator-v2"
MAX_ROUNDS = 12


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _write_jsonl(path: Path, rows: list[dict]) -> bytes:
    payload = b"".join(
        (
            json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
        ).encode("utf-8")
        for row in rows
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)
    return payload


def _install_repo(
    tmp_path: Path,
    *,
    target_representation: str = ANSATZ_REPRESENTATION,
    template_id: str = ANSATZ_TEMPLATE,
    portfolio_schema: int = 2,
    stage3_backend: str = "twobga-aux",
) -> Path:
    """Install one proof-compatible representation-change template."""

    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)

    evolution_config = repo / "evolve/config_ansatz_v2.yaml"
    evolution_config.parent.mkdir(parents=True, exist_ok=True)
    config_lines = [
        "qcode_search_portfolio:",
        "  enabled: true",
        f"  schema_version: {portfolio_schema}",
    ]
    if portfolio_schema == 3:
        config_lines.extend([
            "database:",
            "  num_islands: 5",
            "  feature_dimensions:",
            "    - algebraic_relation_type",
            "    - support_split_type",
            "    - geometry_twist_class",
            "  feature_bins:",
            "    algebraic_relation_type: 5",
            "    support_split_type: 6",
            "    geometry_twist_class: 3",
        ])
    evolution_config.write_text(
        "\n".join(config_lines) + "\n",
        encoding="utf-8",
    )
    evolution_seed = repo / "evolve/seed_ansatz_v2.py"
    evolution_seed.write_text(
        "def generate_candidates(ell, m):\n    return []\n",
        encoding="utf-8",
    )

    base_pipeline = repo / "configs/ansatz_child_base.json"
    _write_json(
        base_pipeline,
        {
            "run_id": "ansatz-child-base",
            "resume": True,
            "max_total_workers": 12,
            "stage1": {
                "max_rounds": MAX_ROUNDS,
                "evolution_config": "evolve/config_ansatz_v2.yaml",
                "evolution_seed": "evolve/seed_ansatz_v2.py",
                "search_representation_id": target_representation,
                "search_regime_policy_version": 3,
            },
            "stage3": {"backend": stage3_backend, "exact": True},
        },
    )
    registry_path = repo / "configs/registry.json"
    _write_json(
        registry_path,
        {
            "schema_version": 1,
            "kind": "qcode-campaign-template-registry",
            "templates": [
                {
                    "template_id": template_id,
                    "template_version": 1,
                    "description": "fresh schema-v2 ansatz representation",
                    "runner_kind": "five-stage-humanize",
                    "transition_kind": "representation_change",
                    "representation_id": target_representation,
                    "family_id": f"{target_representation}-family",
                    "checkpoint_compatibility_group": target_representation,
                    "proof_compatible": True,
                    "launch_compatible": True,
                    "auto_materialize": True,
                    "allowed_parent_representations": [PARENT_REPRESENTATION],
                    "allowed_machine_regimes": [
                        "representation_change_required"
                    ],
                    "base_pipeline": {
                        "path": "configs/ansatz_child_base.json",
                        "sha256": _sha256(base_pipeline),
                    },
                    "evolution_config": {
                        "path": "evolve/config_ansatz_v2.yaml",
                        "sha256": _sha256(evolution_config),
                    },
                    "evolution_seed": {
                        "path": "evolve/seed_ansatz_v2.py",
                        "sha256": _sha256(evolution_seed),
                    },
                    "required_stage3_backend": stage3_backend,
                }
            ],
        },
    )
    return repo


def _install_parent_pipeline(
    repo: Path,
    *,
    run_id: str,
    policy_version: int,
    template_id: str = ANSATZ_TEMPLATE,
) -> Path:
    path = repo / f"configs/{run_id}.json"
    _write_json(
        path,
        {
            "run_id": run_id,
            "resume": True,
            "stage1": {
                "max_rounds": MAX_ROUNDS,
                "search_representation_id": PARENT_REPRESENTATION,
                "search_regime_policy_version": policy_version,
                "stop_on_representation_change": True,
            },
            "auto_escalation": {
                "enabled": True,
                "registry": "configs/registry.json",
                "template_by_regime": {
                    "representation_change_required": template_id
                },
            },
        },
    )
    return path


def _install_sealed_history(
    repo: Path, *, run_id: str, policy_version: int
) -> tuple[Path, list[dict], dict]:
    """Create four exact-low rounds followed by eight exact-empty rounds.

    The history reaches family expansion in round four.  Under V2 the empty
    rounds break the exact-low streak and leave that directive in place.  V3
    treats them as neutral and converts the exhausted round-12 budget into a
    representation-change handoff.
    """

    run_root = repo / f"results/humanize/{run_id}"
    rounds_root = run_root / "rounds"
    rounds: list[dict] = []
    for number in range(1, MAX_ROUNDS + 1):
        round_dir = rounds_root / f"round-{number:03d}"
        exact_rows = []
        if number <= 4:
            exact_rows = [
                {
                    "n": 360,
                    "k": 8,
                    "d": 2,
                    "d_is_exact": True,
                    "stage": "exact",
                    "audit_attempt": {
                        "schema_version": 2,
                        "round": number,
                        "evidence": {"sealed": True},
                    },
                }
            ]
        milp_payload = _write_jsonl(round_dir / "milp.jsonl", exact_rows)
        exact_summary = flow_module._sealed_round_exact_summary(
            round_number=number,
            round_dir=round_dir,
            failure_feedback={
                "source_milp_sha256": hashlib.sha256(milp_payload).hexdigest(),
                "source_milp_bytes": len(milp_payload),
                "source_milp_rows": len(exact_rows),
            },
        )

        batch_rows = [
            {
                "A_terms": [[0, 0], [number, 0]],
                "B_terms": [[0, 0], [0, number]],
            },
            {
                "A_terms": [[0, 0], [number + 1, 0]],
                "B_terms": [[0, 0], [1, number]],
            },
        ]
        batch_payload = _write_jsonl(
            round_dir / "candidate-batch.jsonl", batch_rows
        )
        transaction = {
            "status": "committed",
            "candidate_source_rows": len(batch_rows),
            "candidate_source_sha256": hashlib.sha256(
                f"source-round-{number}".encode()
            ).hexdigest(),
            "candidate_batch_identity": {
                "sha256": hashlib.sha256(batch_payload).hexdigest(),
                "bytes": len(batch_payload),
                "rows": len(batch_rows),
            },
        }
        _write_json(round_dir / "evolution-transaction.json", transaction)
        diversity = flow_module._candidate_diversity_summary(
            transaction, batch_rows
        )

        summary = {
            "round": number,
            "search_regime_policy_version": policy_version,
            "trusted_win_total": 0,
            "sealed_exact_audit": exact_summary,
            "candidate_diversity": diversity,
        }
        regime = flow_module._replay_search_regime(
            [*rounds, summary],
            rounds_root=rounds_root,
            policy_version=policy_version,
            max_rounds=MAX_ROUNDS if policy_version == 3 else None,
        )
        summary["search_regime"] = regime
        rounds.append(summary)

    final_regime = flow_module._replay_search_regime(
        rounds,
        rounds_root=rounds_root,
        policy_version=policy_version,
        max_rounds=MAX_ROUNDS if policy_version == 3 else None,
    )
    state = {
        "run_id": run_id,
        "status": "search-complete",
        "current_round": MAX_ROUNDS,
        "pending_round": None,
        "round_phase": None,
        "config": {
            "max_rounds": MAX_ROUNDS,
            "search_representation_id": PARENT_REPRESENTATION,
            "search_regime_policy_version": policy_version,
            "stop_on_representation_change": True,
        },
        "rounds": rounds,
        "search_regime": final_regime,
        "trusted_win_count": 0,
    }
    if policy_version == 3:
        state["search_handoff_reason"] = "representation_change_required"
        state["search_handoff_at_round"] = MAX_ROUNDS
    state_path = run_root / "state.json"
    _write_json(state_path, state)
    return state_path, rounds, final_regime


@pytest.fixture
def sealed_exact_classifier(monkeypatch):
    """Isolate the formal evidence verifier, not the on-disk evidence replay."""

    def classify(row):
        attempt = row.get("audit_attempt")
        assert attempt == {
            "schema_version": 2,
            "round": attempt["round"],
            "evidence": {"sealed": True},
        }
        assert row["stage"] == "exact"
        assert row["d_is_exact"] is True
        return flow_module.AuditOutcome.EXACT

    monkeypatch.setattr(flow_module, "classify_evaluation", classify)


def test_v3_terminal_fallback_materializes_ansatz_idempotently(
    tmp_path, sealed_exact_classifier
):
    repo = _install_repo(tmp_path)
    run_id = "parent-v3"
    pipeline_config = _install_parent_pipeline(
        repo, run_id=run_id, policy_version=3
    )
    state_path, rounds, regime = _install_sealed_history(
        repo, run_id=run_id, policy_version=3
    )

    assert rounds[3]["search_regime"]["status"] == "expand_required"
    assert rounds[10]["search_regime"]["status"] == "expand_required"
    assert regime["status"] == "representation_change_required"
    assert regime["reason"] == "round_budget_exhausted_after_family_expansion"
    assert regime["evidence"]["round"] == MAX_ROUNDS
    assert regime["evidence"]["max_rounds"] == MAX_ROUNDS

    plan = plan_campaign_escalation(
        repo_dir=repo,
        parent_state_path=state_path,
        registry_path=Path("configs/registry.json"),
        template_id=ANSATZ_TEMPLATE,
    )
    assert plan.machine_regime == "representation_change_required"
    assert plan.transition_kind == "representation_change"
    assert plan.parent_representation_id == PARENT_REPRESENTATION
    assert plan.target_representation_id == ANSATZ_REPRESENTATION
    assert plan.materializable is True

    destination = Path("results/escalations/v3-ansatz-child.json")
    first = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=state_path,
        pipeline_config_path=pipeline_config,
        destination=destination,
    )
    assert first.disposition == "materialized"
    assert first.policy.source_search_regime_policy_version == 3
    assert first.policy.source_max_rounds == MAX_ROUNDS
    assert first.policy.source_stop_on_representation_change is True
    assert first.policy.serializable()["source_max_rounds"] == MAX_ROUNDS
    assert first.materialized is not None
    assert first.materialized.created is True
    first_payload = first.materialized.path.read_bytes()
    child = json.loads(first_payload)
    assert child["run_id"] == plan.child_run_id
    assert child["resume"] is True
    assert child["stage1"]["search_representation_id"] == ANSATZ_REPRESENTATION
    assert "stop_on_representation_change" not in child["stage1"]
    assert "auto_escalation" not in child
    assert "checkpoint" not in first_payload.decode().lower()

    second = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=state_path,
        pipeline_config_path=pipeline_config,
        destination=destination,
    )
    assert second.disposition == "materialized"
    assert second.materialized is not None
    assert second.materialized.created is False
    assert second.materialized.pipeline_sha256 == first.materialized.pipeline_sha256
    assert second.materialized.path.read_bytes() == first_payload


def test_v3_terminal_fallback_materializes_schema_v3_twisted_sat_child(
    tmp_path, sealed_exact_classifier
):
    twisted_representation = "css-bb-twisted-torus-generator-v1"
    repo = _install_repo(
        tmp_path,
        target_representation=twisted_representation,
        template_id=twisted_representation,
        portfolio_schema=3,
        stage3_backend="sat-sectors",
    )
    run_id = "parent-v3-twisted"
    pipeline_config = _install_parent_pipeline(
        repo,
        run_id=run_id,
        policy_version=3,
        template_id=twisted_representation,
    )
    state_path, _rounds, regime = _install_sealed_history(
        repo,
        run_id=run_id,
        policy_version=3,
    )
    assert regime["status"] == "representation_change_required"

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=state_path,
        pipeline_config_path=pipeline_config,
        destination=Path("results/escalations/v3-twisted-child.json"),
    )
    assert reconciled.disposition == "materialized"
    assert reconciled.materialized is not None
    child = json.loads(reconciled.materialized.path.read_text())
    assert child["stage1"]["search_representation_id"] == (
        twisted_representation
    )
    assert child["stage1"]["evolution_config"] == (
        "evolve/config_ansatz_v2.yaml"
    )
    assert child["stage3"] == {
        "backend": "sat-sectors",
        "exact": True,
    }
    assert "auto_escalation" not in child


def test_v3_auto_escalation_rejects_pipeline_budget_rebinding(
    tmp_path, sealed_exact_classifier
):
    repo = _install_repo(tmp_path)
    run_id = "parent-v3-rebound"
    pipeline_config = _install_parent_pipeline(
        repo, run_id=run_id, policy_version=3
    )
    state_path, _rounds, _regime = _install_sealed_history(
        repo, run_id=run_id, policy_version=3
    )
    rebound = json.loads(pipeline_config.read_text())
    rebound["stage1"]["max_rounds"] = MAX_ROUNDS + 1
    _write_json(pipeline_config, rebound)

    with pytest.raises(ParentEvidenceError, match="budget/handoff authority"):
        reconcile_campaign_escalation(
            repo_dir=repo,
            parent_state_path=state_path,
            pipeline_config_path=pipeline_config,
        )


def test_v2_same_sealed_history_stays_expand_and_cannot_select_ansatz(
    tmp_path, sealed_exact_classifier
):
    repo = _install_repo(tmp_path)
    run_id = "parent-v2"
    pipeline_config = _install_parent_pipeline(
        repo, run_id=run_id, policy_version=2
    )
    state_path, rounds, regime = _install_sealed_history(
        repo, run_id=run_id, policy_version=2
    )

    assert rounds[3]["search_regime"]["status"] == "expand_required"
    assert regime["status"] == "expand_required"
    assert regime["reason"] == (
        "trusted_exact_low_distance_streak_requires_family_expansion"
    )

    with pytest.raises(ParentEvidenceError, match="cannot select"):
        plan_campaign_escalation(
            repo_dir=repo,
            parent_state_path=state_path,
            registry_path=Path("configs/registry.json"),
            template_id=ANSATZ_TEMPLATE,
        )

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=state_path,
        pipeline_config_path=pipeline_config,
        destination=Path("results/escalations/must-not-exist.json"),
    )
    assert reconciled.disposition == "blocked"
    assert reconciled.materialized is None
    assert reconciled.block_reasons == ("no_template_for_machine_regime",)
    assert not (repo / "results/escalations/must-not-exist.json").exists()
