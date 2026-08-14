from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

import humanize.escalation as escalation_module
import humanize.flow as flow_module
import humanize.pipeline_process as process_control
from humanize.escalation import (
    MaterializationError,
    ParentEvidenceError,
    ProofIncompatibleTemplateError,
    RegistryError,
    load_template_registry,
    materialize_child_pipeline,
    parse_auto_escalation_policy,
    plan_campaign_escalation,
    reconcile_campaign_escalation,
    verify_materialized_child_pipeline,
)


REPO = Path(__file__).resolve().parents[1]


@pytest.fixture(autouse=True)
def _sealed_regime_replay(monkeypatch):
    """Keep fixture evidence small while asserting planner uses the replay API."""

    def replay(
        rounds,
        *,
        rounds_root=None,
        policy_version=None,
        max_rounds=None,
    ):
        assert rounds_root is not None
        if not rounds:
            return {
                "schema_version": 1,
                "kind": "qcode-humanize-search-regime",
                "status": "normal",
                "reason": "empty-test-fixture",
                "evidence": {"completed_rounds": 0},
            }
        return rounds[-1]["search_regime"]

    monkeypatch.setattr(escalation_module.flow_module, "_replay_search_regime", replay)


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


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


def _fixture_repo(tmp_path: Path, *, proof_compatible: bool = True) -> Path:
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    base = repo / "configs/base.json"
    config = repo / "evolve/config_expand.yaml"
    seed = repo / "evolve/seed_expand.py"
    _write_json(
        base,
        {
            "run_id": "base",
            "resume": True,
            "max_total_workers": 12,
            "stage1": {
                "max_rounds": 2,
                "evolution_config": "evolve/old.yaml",
                "evolution_seed": "evolve/old.py",
                "search_representation_id": "css-bb-v1",
            },
            "stage3": {"backend": "twobga-aux", "exact": True},
            "auto_escalation": {
                "enabled": True,
                "registry": "configs/registry.json",
                "template_by_regime": {"expand_required": "css-expand-v2"},
            },
        },
    )
    config.parent.mkdir(parents=True, exist_ok=True)
    config.write_text(
        "qcode_search_portfolio:\n  enabled: true\n  schema_version: 2\n",
        encoding="utf-8",
    )
    seed.write_text("def generate_candidates(ell, m):\n    return []\n", encoding="utf-8")
    template = {
        "template_id": "css-expand-v2",
        "template_version": 1,
        "description": "test CSS family expansion",
        "runner_kind": "five-stage-humanize",
        "transition_kind": "expand_family",
        "representation_id": "css-bb-v1",
        "family_id": "test-expand-v2",
        "checkpoint_compatibility_group": "test-expand-v2",
        "proof_compatible": proof_compatible,
        "launch_compatible": True,
        "auto_materialize": proof_compatible,
        "allowed_parent_representations": ["css-bb-v1"],
        "allowed_machine_regimes": ["expand_required"],
        "base_pipeline": {"path": "configs/base.json", "sha256": _sha(base)},
        "evolution_config": {
            "path": "evolve/config_expand.yaml",
            "sha256": _sha(config),
        },
        "evolution_seed": {
            "path": "evolve/seed_expand.py",
            "sha256": _sha(seed),
        },
        "required_stage3_backend": "twobga-aux",
    }
    _write_json(
        repo / "configs/registry.json",
        {
            "schema_version": 1,
            "kind": "qcode-campaign-template-registry",
            "templates": [template],
        },
    )
    # The parent launch policy is independently hash-bound by reconciliation;
    # it is not also used as the child template in these tests.
    (repo / "configs/parent_pipeline.json").write_bytes(base.read_bytes())
    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": "expand_required",
        "reason": "sealed-test-evidence",
        "evidence": {"rounds": [1]},
    }
    review = {
        "schema_version": 2,
        "verdict": "continue",
        "summary": "Continue from sealed machine evidence.",
        "risks": [],
        "recommended_focus": [],
        "lessons": [],
        "search_action": {
            "schema_version": 1,
            "advisory_only": True,
            "intent": "maintain",
            "horizon_rounds": 1,
            "focus": [],
            "evidence_refs": [],
            "rationale": "The reviewer cannot authorize campaign escalation.",
        },
    }
    review_path = (
        repo
        / "results/humanize/parent-run/rounds/round-001/review.json"
    )
    _write_json(review_path, review)
    review_payload = review_path.read_bytes()
    _write_json(
        repo / "results/humanize/parent-run/state.json",
        {
            "run_id": "parent-run",
            "status": "search-complete",
            "current_round": 1,
            "config": {"search_representation_id": "css-bb-v1"},
            "pending_round": None,
            "round_phase": None,
            "rounds": [
                {
                    "round": 1,
                    "search_regime": regime,
                    "review_binding": {
                        "schema_version": 1,
                        "artifact_sha256": hashlib.sha256(
                            review_payload
                        ).hexdigest(),
                        "artifact_bytes": len(review_payload),
                        "review_schema_version": 2,
                        "search_action": review["search_action"],
                    },
                }
            ],
            "search_regime": regime,
            "review": {"action": "stop"},
        },
    )
    return repo


def _plan(repo: Path, reviewer_action: object = None):
    return plan_campaign_escalation(
        repo_dir=repo,
        registry_path=Path("configs/registry.json"),
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        template_id="css-expand-v2",
        reviewer_action=reviewer_action,
    )


def _set_regime(repo: Path, status: str) -> None:
    parent_path = repo / "results/humanize/parent-run/state.json"
    parent = json.loads(parent_path.read_text())
    regime = dict(parent["search_regime"])
    regime["status"] = status
    parent["search_regime"] = regime
    parent["rounds"][-1]["search_regime"] = regime
    _write_json(parent_path, parent)


def _rewrite_bound_review(repo: Path, *, rationale: str) -> None:
    review_path = (
        repo
        / "results/humanize/parent-run/rounds/round-001/review.json"
    )
    review = json.loads(review_path.read_text())
    review["search_action"]["rationale"] = rationale
    _write_json(review_path, review)
    payload = review_path.read_bytes()
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["rounds"][-1]["review_binding"] = {
        "schema_version": 1,
        "artifact_sha256": hashlib.sha256(payload).hexdigest(),
        "artifact_bytes": len(payload),
        "review_schema_version": 2,
        "search_action": review["search_action"],
    }
    _write_json(state_path, state)


def _install_seven_round_v2_escalation_evidence(repo: Path) -> list[dict]:
    """Replace the compact fixture with transaction-bound policy-v2 history."""

    base_path = repo / "configs/base.json"
    base = json.loads(base_path.read_text())
    base["stage1"].update({
        "max_rounds": 7,
        "search_representation_id": "css-bb-v1",
        "search_regime_policy_version": 2,
        "stop_on_representation_change": True,
    })
    _write_json(base_path, base)

    parent_config_path = repo / "configs/parent_pipeline.json"
    parent_config = json.loads(parent_config_path.read_text())
    parent_config["stage1"].update({
        "max_rounds": 7,
        "search_representation_id": "css-bb-v1",
        "search_regime_policy_version": 2,
        "stop_on_representation_change": True,
    })
    parent_config["auto_escalation"]["template_by_regime"] = {
        "representation_change_required": "css-expand-v2"
    }
    _write_json(parent_config_path, parent_config)

    registry_path = repo / "configs/registry.json"
    registry = json.loads(registry_path.read_text())
    template = registry["templates"][0]
    template.update({
        "transition_kind": "representation_change",
        "representation_id": "css-ansatz-v2",
        "family_id": "test-ansatz-v2",
        "checkpoint_compatibility_group": "test-ansatz-v2",
        "allowed_machine_regimes": ["representation_change_required"],
        "base_pipeline": {
            "path": "configs/base.json",
            "sha256": _sha(base_path),
        },
    })
    _write_json(registry_path, registry)

    rounds_root = repo / "results/humanize/parent-run/rounds"
    rounds: list[dict] = []
    for number in range(1, 8):
        round_dir = rounds_root / f"round-{number:03d}"
        exact_row = {
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
        milp_payload = _write_jsonl(round_dir / "milp.jsonl", [exact_row])
        exact = flow_module._sealed_round_exact_summary(
            round_number=number,
            round_dir=round_dir,
            failure_feedback={
                "source_milp_sha256": hashlib.sha256(
                    milp_payload
                ).hexdigest(),
                "source_milp_bytes": len(milp_payload),
                "source_milp_rows": 1,
            },
        )

        batch_rows = [
            {
                "A_terms": [[0, 0], [1, 0]],
                "B_terms": [[0, 0], [0, number]],
            },
            {
                "A_terms": [[0, 0], [number + 1, 0]],
                "B_terms": [[0, 0], [0, 1]],
            },
        ]
        batch_payload = _write_jsonl(
            round_dir / "candidate-batch.jsonl", batch_rows
        )
        transaction = {
            "status": "committed",
            "candidate_source_rows": len(batch_rows),
            "candidate_source_sha256": hashlib.sha256(
                f"sealed-source-round-{number}".encode("utf-8")
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

        review = {
            "schema_version": 2,
            "verdict": "continue",
            "summary": f"Review of sealed round {number}.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
            "search_action": {
                "schema_version": 1,
                "advisory_only": True,
                "intent": "change_bb_search_representation",
                "horizon_rounds": 1,
                "focus": [],
                "evidence_refs": [
                    {
                        "source": "round_history",
                        "round": number,
                        "candidate_key": None,
                    }
                ],
                "rationale": (
                    f"Round {number} is advisory context only; sealed machine "
                    "evidence controls escalation."
                ),
            },
        }
        review_path = round_dir / "review.json"
        _write_json(review_path, review)
        review_binding = flow_module._review_artifact_binding(
            review_path, review
        )

        summary = {
            "round": number,
            "search_regime_policy_version": 2,
            "sealed_exact_audit": exact,
            "candidate_diversity": diversity,
            "review_binding": review_binding,
        }
        regime = flow_module._replay_search_regime(
            [*rounds, summary],
            rounds_root=rounds_root,
            policy_version=2,
        )
        summary["search_regime"] = regime
        rounds.append(summary)

    final_regime = flow_module._replay_search_regime(
        rounds,
        rounds_root=rounds_root,
        policy_version=2,
    )
    assert final_regime["status"] == "representation_change_required"
    state_path = repo / "results/humanize/parent-run/state.json"
    _write_json(
        state_path,
        {
            "run_id": "parent-run",
            "status": "search-complete",
            "current_round": 7,
            "config": {
                "search_representation_id": "css-bb-v1",
                "search_regime_policy_version": 2,
                "stop_on_representation_change": True,
            },
            "pending_round": None,
            "round_phase": None,
            "rounds": rounds,
            "search_regime": final_regime,
            "search_handoff_reason": "representation_change_required",
            "search_handoff_at_round": 7,
        },
    )
    return rounds


def test_checked_in_registry_marks_real_incompatible_templates_fail_closed():
    registry = load_template_registry(repo_dir=REPO)
    current = registry.template("css-bb-novel-ansatz-generator-v2")
    assert current.representation_id == "css-bb-novel-ansatz-generator-v2"
    assert current.allowed_parent_representations == (
        "css-bb-cover-algebra-generator-v2",
    )
    assert current.transition_kind == "representation_change"
    assert current.proof_compatible is True
    assert current.launch_compatible is True
    assert current.auto_materialize is True
    assert current.base_pipeline is not None
    assert current.base_pipeline.path == (
        "configs/five_stage_campaign.ansatz_child_v2.json"
    )
    ansatz = registry.template("css-bb-novel-ansatz-v1")
    assert ansatz.proof_compatible is True
    assert ansatz.launch_compatible is False
    assert ansatz.auto_materialize is False
    pbb = registry.template("pbb-noncss-v1")
    assert pbb.proof_compatible is False
    assert pbb.launch_compatible is False
    assert pbb.auto_materialize is False

    policy = parse_auto_escalation_policy(
        repo_dir=REPO,
        pipeline_config_path=Path(
            "configs/five_stage_campaign.cover_algebra.auto_v2.json"
        ),
    )
    assert policy.enabled is True
    assert policy.source_search_representation_id == (
        "css-bb-cover-algebra-generator-v2"
    )
    assert policy.template_by_regime == {
        "representation_change_required": (
            "css-bb-novel-ansatz-generator-v2"
        )
    }


def test_real_v2_sealed_history_stably_materializes_and_launches_child(
    tmp_path, monkeypatch
):
    # This file's compact tests normally stub regime replay.  Remove that
    # autouse patch for this integration test so escalation must replay every
    # transaction-bound round through the production policy-v2 implementation.
    monkeypatch.undo()

    def classify_sealed_exact(row):
        attempt = row.get("audit_attempt")
        assert attempt == {
            "schema_version": 2,
            "round": attempt["round"],
            "evidence": {"sealed": True},
        }
        assert row["stage"] == "exact"
        assert row["d_is_exact"] is True
        return flow_module.AuditOutcome.EXACT

    # The scientific checkpoint verifier is outside this orchestration test;
    # only its outcome is isolated.  The real replay still re-reads and hashes
    # all seven MILP, diversity-transaction, batch, and review artifacts.
    monkeypatch.setattr(
        flow_module, "classify_evaluation", classify_sealed_exact
    )
    repo = _fixture_repo(tmp_path)
    rounds = _install_seven_round_v2_escalation_evidence(repo)
    rounds_root = repo / "results/humanize/parent-run/rounds"

    replayed = flow_module._replay_search_regime(
        rounds,
        rounds_root=rounds_root,
        policy_version=2,
    )
    assert replayed["status"] == "representation_change_required"
    assert replayed["evidence"]["rounds"] == list(range(1, 8))
    for summary in rounds:
        assert flow_module._validated_bound_round_review(
            summary, rounds_root
        )["schema_version"] == 2

    first_plan = _plan(repo)
    first_reconciliation = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path(
            "results/humanize/parent-run/state.json"
        ),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert first_reconciliation.plan == first_plan
    assert first_plan.machine_regime == "representation_change_required"
    assert first_plan.transition_kind == "representation_change"

    stable_destination = Path("results/escalations/sealed-v2-child.json")
    first_child = materialize_child_pipeline(
        first_plan, destination=stable_destination
    )
    first_bytes = first_child.path.read_bytes()
    first_value = json.loads(first_bytes)
    assert first_value["resume"] is True
    assert first_value["stage1"]["search_representation_id"] == (
        "css-ansatz-v2"
    )

    # Change only reviewer advice and its byte binding.  Neither child identity
    # nor executable config may change because escalation authority is solely
    # the canonical sealed machine evidence above.
    state_path = repo / "results/humanize/parent-run/state.json"
    state_sha_before = _sha(state_path)
    review_path = rounds_root / "round-007/review.json"
    review = json.loads(review_path.read_text())
    review["search_action"]["intent"] = "maintain"
    review["search_action"]["rationale"] = (
        "Changed advisory after sealing; it cannot select the child."
    )
    _write_json(review_path, review)
    state = json.loads(state_path.read_text())
    state["rounds"][-1]["review_binding"] = (
        flow_module._review_artifact_binding(review_path, review)
    )
    _write_json(state_path, state)
    assert _sha(state_path) != state_sha_before

    second_plan = _plan(repo)
    second_reconciliation = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path(
            "results/humanize/parent-run/state.json"
        ),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
        destination=stable_destination,
    )
    assert second_reconciliation.materialized is not None
    assert second_reconciliation.materialized.created is False
    assert second_plan.machine_evidence_sha256 == (
        first_plan.machine_evidence_sha256
    )
    assert second_plan.idempotency_key == first_plan.idempotency_key
    assert second_plan.child_run_id == first_plan.child_run_id
    assert second_plan.plan_sha256 == first_plan.plan_sha256
    assert first_child.path.read_bytes() == first_bytes

    launches = []

    def fake_launcher(**kwargs):
        launches.append(kwargs)
        return {
            "run_id": kwargs["run_id"],
            "config_path": str(Path(kwargs["config_path"]).resolve()),
            "config_sha256": kwargs["expected_config_sha256"],
            "pid": 4321,
            "proc_starttime": 987654,
        }

    outcome = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=repo / "configs/parent_pipeline.json",
        parent_run_id="parent-run",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=fake_launcher,
        status_reader=lambda **_kwargs: {
            "status": "not-started",
            "alive": False,
            "process": None,
        },
    )
    assert outcome is not None
    assert outcome["disposition"] == "materialized"
    assert outcome["launch"]["status"] == "started"
    assert len(launches) == 1
    launched_config = Path(launches[0]["config_path"])
    assert launches[0]["run_id"] == first_plan.child_run_id
    assert json.loads(launched_config.read_text())["resume"] is True
    assert launched_config.read_bytes() == first_bytes


def test_only_machine_expand_regime_gates_and_reviewer_is_advisory(tmp_path):
    repo = _fixture_repo(tmp_path)
    plan = _plan(repo, reviewer_action={"action": "stop", "score": 0})
    assert plan.materializable is True

    state_path = repo / "results/humanize/parent-run/state.json"
    parent = json.loads(state_path.read_text())
    parent["search_regime"]["status"] = "normal"
    parent["rounds"][-1]["search_regime"]["status"] = "normal"
    _write_json(state_path, parent)
    with pytest.raises(ParentEvidenceError, match="machine regime"):
        _plan(repo, reviewer_action={"action": "expand_required"})


def test_omitted_reviewer_action_comes_only_from_last_round_binding(tmp_path):
    repo = _fixture_repo(tmp_path)
    derived = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert derived.reviewer_action_advisory == {
        "schema_version": 1,
        "advisory_only": True,
        "intent": "maintain",
        "horizon_rounds": 1,
        "focus": [],
        "evidence_refs": [],
        "rationale": "The reviewer cannot authorize campaign escalation.",
    }

    explicit = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
        reviewer_action={"intent": "do-not-launch"},
    )
    assert explicit.reviewer_action_advisory == {"intent": "do-not-launch"}
    assert explicit.plan is not None and derived.plan is not None
    # Reviewer advice is excluded from the machine decision identity.
    assert explicit.plan.idempotency_key == derived.plan.idempotency_key
    assert explicit.plan.child_run_id == derived.plan.child_run_id
    assert explicit.plan.plan_sha256 == derived.plan.plan_sha256


@pytest.mark.parametrize("corruption", ["missing", "tampered"])
def test_invalid_reviewer_advisory_cannot_block_machine_escalation(
    tmp_path,
    corruption,
):
    repo = _fixture_repo(tmp_path)
    review_path = (
        repo
        / "results/humanize/parent-run/rounds/round-001/review.json"
    )
    if corruption == "missing":
        review_path.unlink()
    else:
        review = json.loads(review_path.read_text())
        review["summary"] = "Changed after the round binding was sealed."
        _write_json(review_path, review)

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path(
            "results/humanize/parent-run/state.json"
        ),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
        destination=Path(
            f"results/escalations/reviewer-{corruption}-child.json"
        ),
    )

    assert reconciled.disposition == "materialized"
    assert reconciled.materialized is not None
    assert reconciled.reviewer_action_advisory is None
    assert reconciled.reviewer_action_advisory_status == "unavailable"
    assert reconciled.reviewer_action_advisory_error is not None
    assert reconciled.reviewer_action_advisory_error["classification"]
    sidecar = reconciled.serializable()
    assert sidecar["reviewer_action_advisory"] is None
    assert sidecar["reviewer_action_advisory_status"] == "unavailable"
    assert sidecar["reviewer_action_advisory_error"]["message"]


@pytest.mark.parametrize(
    "corruption",
    ["missing-markers", "wrong-round", "stop-disabled"],
)
def test_representation_escalation_requires_atomic_policy_v2_handoff(
    tmp_path,
    corruption,
):
    repo = _fixture_repo(tmp_path)
    _set_regime(repo, "representation_change_required")
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["config"].update({
        "search_regime_policy_version": 2,
        "stop_on_representation_change": True,
    })
    state["rounds"][-1]["search_regime_policy_version"] = 2
    state["search_handoff_reason"] = "representation_change_required"
    state["search_handoff_at_round"] = state["current_round"]
    if corruption == "missing-markers":
        state.pop("search_handoff_reason")
        state.pop("search_handoff_at_round")
    elif corruption == "wrong-round":
        state["search_handoff_at_round"] = state["current_round"] + 1
    else:
        state["config"]["stop_on_representation_change"] = False
    _write_json(state_path, state)

    with pytest.raises(ParentEvidenceError, match="handoff"):
        plan_campaign_escalation(
            repo_dir=repo,
            registry_path=Path("configs/registry.json"),
            parent_state_path=Path(
                "results/humanize/parent-run/state.json"
            ),
            template_id="css-expand-v2",
        )


def test_policy_v5_handoff_is_authorized_and_binds_scientific_progress(
    tmp_path,
):
    repo = _fixture_repo(tmp_path)
    _set_regime(repo, "representation_change_required")
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["config"].update({
        "search_regime_policy_version": 5,
        "stop_on_representation_change": True,
        "max_rounds": 12,
    })
    summary = state["rounds"][-1]
    summary["search_regime_policy_version"] = 5
    summary["trusted_win_total"] = 0
    summary["sealed_scientific_progress"] = {
        "progress_sha256": "1" * 64,
        "test_bound_coordinate": 1,
    }
    state["trusted_win_count"] = 0
    state["search_handoff_reason"] = "representation_change_required"
    state["search_handoff_at_round"] = state["current_round"]
    _write_json(state_path, state)

    first = escalation_module._validated_parent_machine_evidence(
        repo=repo,
        parent_state_path=Path(
            "results/humanize/parent-run/state.json"
        ),
        require_escalation_regime=True,
    )
    assert first.search_regime_policy_version == 5
    assert first.stop_on_representation_change is True

    state = json.loads(state_path.read_text())
    state["rounds"][-1]["sealed_scientific_progress"][
        "test_bound_coordinate"
    ] = 2
    _write_json(state_path, state)
    second = escalation_module._validated_parent_machine_evidence(
        repo=repo,
        parent_state_path=Path(
            "results/humanize/parent-run/state.json"
        ),
        require_escalation_regime=True,
    )
    assert second.machine_evidence_sha256 != first.machine_evidence_sha256


def test_legacy_search_action_extra_is_not_structured_escalation_advice(tmp_path):
    repo = _fixture_repo(tmp_path)
    review_path = (
        repo
        / "results/humanize/parent-run/rounds/round-001/review.json"
    )
    legacy = {
        "verdict": "continue",
        "summary": "Historical permissive reviewer artifact.",
        "risks": [],
        "recommended_focus": [],
        "lessons": [],
        # This name was a legal arbitrary extra under the legacy contract.  It
        # must not be reinterpreted as a reviewer-v2 structured action.
        "search_action": {"intent": "change_bb_search_representation"},
    }
    _write_json(review_path, legacy)
    binding = escalation_module.flow_module._review_artifact_binding(
        review_path,
        escalation_module.flow_module.validate_review(legacy),
    )
    assert binding["review_schema_version"] == 1
    assert binding["search_action"] is None

    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["rounds"][-1]["review_binding"] = binding
    _write_json(state_path, state)

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert reconciled.reviewer_action_advisory is None


def test_parent_must_be_terminal_transaction_clear_and_regime_replay_exact(
    tmp_path, monkeypatch
):
    repo = _fixture_repo(tmp_path)
    state_path = repo / "results/humanize/parent-run/state.json"
    parent = json.loads(state_path.read_text())
    parent["status"] = "running"
    _write_json(state_path, parent)
    with pytest.raises(ParentEvidenceError, match="parent status"):
        _plan(repo)

    parent["status"] = "incomplete-unresolved"
    parent["pending_round"] = 2
    parent["round_phase"] = "audit"
    _write_json(state_path, parent)
    with pytest.raises(ParentEvidenceError, match="unfinished round"):
        _plan(repo)

    parent["pending_round"] = None
    parent["round_phase"] = None
    _write_json(state_path, parent)
    monkeypatch.setattr(
        escalation_module.flow_module,
        "_replay_search_regime",
        lambda _rounds, *, rounds_root=None, policy_version=None,
        max_rounds=None: {
            "schema_version": 1,
            "kind": "qcode-humanize-search-regime",
            "status": "normal",
            "reason": "mismatch",
            "evidence": {},
        },
    )
    with pytest.raises(ParentEvidenceError, match="disagrees"):
        _plan(repo)


def test_materializes_fresh_hash_bound_idempotent_child_pipeline(tmp_path):
    repo = _fixture_repo(tmp_path)
    plan = _plan(repo, reviewer_action="do-not-expand")
    destination = Path("results/escalations/child.json")
    first = materialize_child_pipeline(plan, destination=destination)
    payload = first.path.read_bytes()
    value = json.loads(payload)
    assert first.created is True
    assert value["run_id"] == plan.child_run_id != plan.parent_run_id
    assert value["resume"] is True
    assert "auto_escalation" not in value
    assert "stop_on_representation_change" not in value["stage1"]
    assert value["stage1"]["evolution_config"] == "evolve/config_expand.yaml"
    assert value["stage1"]["evolution_seed"] == "evolve/seed_expand.py"
    assert value["stage1"]["search_representation_id"] == "css-bb-v1"
    provenance = value["campaign_escalation"]
    assert provenance["parent_run_id"] == "parent-run"
    assert "reviewer_action_advisory" not in provenance
    assert "parent_state_sha256" not in provenance
    assert provenance["machine_evidence_sha256"] == (
        plan.machine_evidence_sha256
    )
    assert provenance["registry_sha256"] == plan.registry_sha256
    assert provenance["template_entry_sha256"] == plan.template_entry_sha256
    assert len(provenance["lineage_sha256"]) == 64
    assert len(provenance["provenance_sha256"]) == 64
    assert "checkpoint" not in payload.decode().lower()

    replay = _plan(repo, reviewer_action="do-not-expand")
    assert replay.child_run_id == plan.child_run_id
    assert replay.idempotency_key == plan.idempotency_key
    second = materialize_child_pipeline(replay, destination=destination)
    assert second.created is False
    assert second.pipeline_sha256 == first.pipeline_sha256
    assert first.path.read_bytes() == payload


def test_reviewer_only_change_keeps_plan_child_id_and_child_bytes_stable(tmp_path):
    repo = _fixture_repo(tmp_path)
    first_plan = _plan(repo)
    first = materialize_child_pipeline(
        first_plan, destination=Path("results/escalations/reviewer-stable.json")
    )
    first_payload = first.path.read_bytes()
    old_state_sha = _sha(repo / "results/humanize/parent-run/state.json")

    _rewrite_bound_review(repo, rationale="A different advisory-only rationale.")
    assert _sha(repo / "results/humanize/parent-run/state.json") != old_state_sha
    second_plan = _plan(repo)
    second = materialize_child_pipeline(
        second_plan, destination=Path("results/escalations/reviewer-stable.json")
    )

    assert second_plan.machine_evidence_sha256 == first_plan.machine_evidence_sha256
    assert second_plan.idempotency_key == first_plan.idempotency_key
    assert second_plan.child_run_id == first_plan.child_run_id
    assert second.pipeline_sha256 == first.pipeline_sha256
    assert second.path.read_bytes() == first_payload


def test_worker_reverification_rejects_asset_tamper_after_materialization(tmp_path):
    repo = _fixture_repo(tmp_path)
    materialized = materialize_child_pipeline(
        _plan(repo), destination=Path("results/escalations/tamper.json")
    )
    with (repo / "evolve/seed_expand.py").open("a", encoding="utf-8") as stream:
        stream.write("# replaced after preflight\n")

    with pytest.raises(MaterializationError, match="hash mismatch|changed"):
        verify_materialized_child_pipeline(
            repo_dir=repo,
            config_path=materialized.path,
            expected_pipeline_sha256=materialized.pipeline_sha256,
        )


def test_parent_state_run_directory_and_current_round_are_bound(tmp_path):
    repo = _fixture_repo(tmp_path)
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["current_round"] = 2
    _write_json(state_path, state)
    with pytest.raises(ParentEvidenceError, match="current_round"):
        _plan(repo)

    state["current_round"] = 1
    misplaced = repo / "results/humanize/different-run/state.json"
    _write_json(misplaced, state)
    with pytest.raises(ParentEvidenceError, match="containing run directory"):
        plan_campaign_escalation(
            repo_dir=repo,
            registry_path=Path("configs/registry.json"),
            parent_state_path=Path("results/humanize/different-run/state.json"),
            template_id="css-expand-v2",
        )


def test_registry_must_match_between_policy_and_plan_reads(tmp_path, monkeypatch):
    repo = _fixture_repo(tmp_path)
    original = escalation_module.plan_campaign_escalation

    def mutate_then_plan(**kwargs):
        registry_path = repo / "configs/registry.json"
        registry = json.loads(registry_path.read_text())
        registry["templates"][0]["description"] = "changed between reads"
        _write_json(registry_path, registry)
        return original(**kwargs)

    monkeypatch.setattr(
        escalation_module, "plan_campaign_escalation", mutate_then_plan
    )
    with pytest.raises(RegistryError, match="between policy and plan"):
        reconcile_campaign_escalation(
            repo_dir=repo,
            parent_state_path=Path("results/humanize/parent-run/state.json"),
            pipeline_config_path=Path("configs/parent_pipeline.json"),
        )


@pytest.mark.parametrize("tamper", ["config", "registry"])
def test_launch_snapshot_change_is_pending_and_never_spawns(tmp_path, tamper):
    repo = _fixture_repo(tmp_path)
    config_path = repo / "configs/parent_pipeline.json"
    policy = parse_auto_escalation_policy(
        repo_dir=repo, pipeline_config_path=config_path
    )
    if tamper == "config":
        config = json.loads(config_path.read_text())
        config["auto_escalation"]["enabled"] = False
        _write_json(config_path, config)
    else:
        registry_path = repo / "configs/registry.json"
        registry = json.loads(registry_path.read_text())
        registry["templates"][0]["description"] = "replaced during parent run"
        _write_json(registry_path, registry)
    launches = []

    outcome = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=config_path,
        parent_run_id="parent-run",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        expected_pipeline_config_sha256=policy.pipeline_config_sha256,
        expected_registry_sha256=policy.registry_sha256,
        launcher=lambda **kwargs: launches.append(kwargs),
    )

    assert outcome is not None
    assert outcome["disposition"] == "pending"
    assert outcome["launch"]["status"] == "not-started"
    assert launches == []


def test_registry_or_source_tamper_after_plan_is_rejected(tmp_path):
    repo = _fixture_repo(tmp_path)
    plan = _plan(repo)
    with (repo / "evolve/config_expand.yaml").open("a", encoding="utf-8") as stream:
        stream.write("tampered: true\n")
    with pytest.raises(MaterializationError, match="plan replay failed"):
        materialize_child_pipeline(
            plan, destination=Path("results/escalations/child.json")
        )


def test_plan_object_tamper_is_rejected(tmp_path):
    repo = _fixture_repo(tmp_path)
    plan = _plan(repo)
    forged = replace(plan, child_run_id="forged-child")
    with pytest.raises(MaterializationError, match="changed"):
        materialize_child_pipeline(
            forged, destination=Path("results/escalations/child.json")
        )


def test_symlink_and_path_escape_are_rejected(tmp_path):
    repo = _fixture_repo(tmp_path)
    real = repo / "configs/registry.json"
    link = repo / "configs/registry-link.json"
    link.symlink_to(real)
    with pytest.raises(RegistryError, match="symlink"):
        load_template_registry(repo_dir=repo, registry_path=Path("configs/registry-link.json"))

    plan = _plan(repo)
    with pytest.raises(MaterializationError, match="escapes repository"):
        materialize_child_pipeline(plan, destination=tmp_path / "outside.json")


def test_claimed_launch_compatibility_requires_portfolio_schema_v2(tmp_path):
    repo = _fixture_repo(tmp_path)
    config = repo / "evolve/config_expand.yaml"
    config.write_text(
        "qcode_search_portfolio:\n  enabled: true\n  schema_version: 1\n",
        encoding="utf-8",
    )
    registry_path = repo / "configs/registry.json"
    registry = json.loads(registry_path.read_text())
    registry["templates"][0]["evolution_config"]["sha256"] = _sha(config)
    _write_json(registry_path, registry)
    with pytest.raises(RegistryError, match="schema_version 2"):
        load_template_registry(repo_dir=repo, registry_path=Path("configs/registry.json"))


def test_noncss_representation_plan_is_never_materialized(tmp_path):
    repo = _fixture_repo(tmp_path)
    config = repo / "evolve/config_noncss.yaml"
    seed = repo / "evolve/seed_noncss.py"
    config.write_text("max_iterations: 1\n", encoding="utf-8")
    seed.write_text("# noncss\n", encoding="utf-8")
    registry_path = repo / "configs/registry.json"
    registry = json.loads(registry_path.read_text())
    registry["templates"] = [
        {
            "template_id": "pbb-v1",
            "template_version": 1,
            "description": "blocked PBB",
            "runner_kind": "five-stage-humanize",
            "transition_kind": "representation_change",
            "representation_id": "pbb-noncss-v1",
            "family_id": "pbb-v1",
            "checkpoint_compatibility_group": "pbb-v1",
            "proof_compatible": False,
            "launch_compatible": False,
            "auto_materialize": False,
            "allowed_parent_representations": ["css-bb-v1"],
            "allowed_machine_regimes": ["representation_change_required"],
            "base_pipeline": None,
            "evolution_config": {
                "path": "evolve/config_noncss.yaml",
                "sha256": _sha(config),
            },
            "evolution_seed": {
                "path": "evolve/seed_noncss.py",
                "sha256": _sha(seed),
            },
            "required_stage3_backend": None,
        }
    ]
    _write_json(registry_path, registry)
    _set_regime(repo, "representation_change_required")
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["config"].update({
        "search_regime_policy_version": 2,
        "stop_on_representation_change": True,
    })
    state["rounds"][-1]["search_regime_policy_version"] = 2
    state["search_handoff_reason"] = "representation_change_required"
    state["search_handoff_at_round"] = state["current_round"]
    _write_json(state_path, state)
    plan = plan_campaign_escalation(
        repo_dir=repo,
        registry_path=Path("configs/registry.json"),
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        template_id="pbb-v1",
    )
    assert plan.materializable is False
    assert "proof_incompatible" in plan.block_reasons
    with pytest.raises(ProofIncompatibleTemplateError):
        materialize_child_pipeline(
            plan, destination=Path("results/escalations/pbb.json")
        )


def test_strict_auto_policy_parser_and_reconcile_materialization(tmp_path):
    repo = _fixture_repo(tmp_path)
    policy = parse_auto_escalation_policy(
        repo_dir=repo,
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert policy.enabled is True
    assert policy.registry_path == "configs/registry.json"
    assert policy.source_search_representation_id == "css-bb-v1"
    assert policy.template_by_regime == {
        "expand_required": "css-expand-v2"
    }

    planned = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert planned.disposition == "materializable"
    assert planned.plan is not None
    assert planned.materialized is None

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
        destination=Path("results/escalations/reconciled.json"),
    )
    assert reconciled.disposition == "materialized"
    assert reconciled.materialized is not None
    assert reconciled.materialized.path.is_file()


def test_reconcile_records_missing_mapping_as_blocked(tmp_path):
    repo = _fixture_repo(tmp_path)
    config_path = repo / "configs/parent_pipeline.json"
    config = json.loads(config_path.read_text())
    config["auto_escalation"]["template_by_regime"] = {}
    _write_json(config_path, config)

    reconciled = reconcile_campaign_escalation(
        repo_dir=repo,
        parent_state_path=Path("results/humanize/parent-run/state.json"),
        pipeline_config_path=Path("configs/parent_pipeline.json"),
    )
    assert reconciled.disposition == "blocked"
    assert reconciled.block_reasons == ("no_template_for_machine_regime",)


def test_auto_policy_is_strict_and_binds_parent_search_identity(tmp_path):
    repo = _fixture_repo(tmp_path)
    config_path = repo / "configs/parent_pipeline.json"
    config = json.loads(config_path.read_text())
    config["auto_escalation"]["unexpected"] = True
    _write_json(config_path, config)
    with pytest.raises(RegistryError, match="unknown=unexpected"):
        parse_auto_escalation_policy(
            repo_dir=repo,
            pipeline_config_path=Path("configs/parent_pipeline.json"),
        )

    config["auto_escalation"].pop("unexpected")
    _write_json(config_path, config)
    state_path = repo / "results/humanize/parent-run/state.json"
    state = json.loads(state_path.read_text())
    state["config"]["search_representation_id"] = "different-generator-v2"
    _write_json(state_path, state)
    with pytest.raises(ParentEvidenceError, match="disagrees with pipeline"):
        reconcile_campaign_escalation(
            repo_dir=repo,
            parent_state_path=Path("results/humanize/parent-run/state.json"),
            pipeline_config_path=Path("configs/parent_pipeline.json"),
        )
