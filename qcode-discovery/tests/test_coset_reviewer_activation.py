"""Reviewer proposals can select only sealed, installed coset renderers."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from evolve import coset_policy_dsl_v3 as policy_v3
from evolve.coset_mutation_preflight import (
    CosetMutationRuntimeError,
    InvalidCosetMutation,
    preflight_coset_policy,
)
from evolve.coset_policy_dispatch import parse_and_render_activated_policy
from evolve.coset_search_contract import (
    COSET_ACTION_CATALOG_V2_MANIFEST_ID,
    COSET_RENDERER_ACTIVATION_JSON_ENV,
    COSET_RENDERER_V2_ID,
    COSET_RENDERER_V3_ID,
    coset_batch_map_descriptor_registered,
    coset_renderer_activation_document,
    default_coset_renderer_activation,
    trusted_coset_renderer_activation_from_document,
)
from humanize.coset_renderer_review import (
    ReviewerRendererResolutionError,
    resolve_reviewer_renderer_action,
    validate_reviewer_renderer_resolution,
)
from humanize import flow as flow_module
from humanize.flow import FlowConfig, HumanizeFlow
from humanize.reviewer import ReviewError, build_review_prompt, validate_review
from humanize.state import atomic_write_json


REVIEW_SHA256 = "a" * 64


def _focus(dimension: str, value: str) -> dict:
    return {
        "dimension": dimension,
        "value": value,
        "direction": "increase",
        "priority": "high",
    }


def _review(*focus: dict) -> dict:
    return {
        "schema_version": 2,
        "verdict": "continue",
        "summary": "Select a source-owned renderer for the next round.",
        "risks": [],
        "recommended_focus": [],
        "lessons": [],
        "search_action": {
            "schema_version": 1,
            "advisory_only": True,
            "intent": "change_bb_search_representation",
            "horizon_rounds": 1,
            "focus": list(focus),
            "evidence_refs": [],
            "rationale": "Use the installed registry and fail closed.",
        },
    }


def _resolve(review: dict) -> dict:
    validated = validate_review(review, require_current=True)
    resolution = resolve_reviewer_renderer_action(
        validated["search_action"],
        source_round=7,
        target_round=8,
        review_artifact_sha256=REVIEW_SHA256,
    )
    assert resolution is not None
    return resolution


def test_implicit_installed_action_activation_is_sealed_to_next_round():
    review = _review(_focus("support_split_type", "2+4"))
    resolution = _resolve(review)

    assert resolution["status"] == "activated"
    assert resolution["source_round"] == 7
    assert resolution["target_round"] == 8
    assert resolution["review_artifact_sha256"] == REVIEW_SHA256
    activation = resolution["renderer_activation"]
    assert activation["approved_support_splits"] == [[2, 4]]
    assert resolution["renderer_activation_sha256"] == (
        activation["activation_sha256"]
    )
    assert validate_reviewer_renderer_resolution(
        resolution,
        search_action=review["search_action"],
    ) == resolution


def test_explicit_installed_activation_drives_static_dispatch_and_map():
    review = _review(
        _focus("renderer_descriptor_id", COSET_RENDERER_V3_ID),
        _focus(
            "catalog_manifest_id", COSET_ACTION_CATALOG_V2_MANIFEST_ID
        ),
        _focus("catalog_kind", "action"),
        _focus("support_split_type", "3+3"),
    )
    resolution = _resolve(review)
    activation_document = resolution["renderer_activation"]
    activation = trusted_coset_renderer_activation_from_document(
        activation_document
    )
    policy = policy_v3.default_policy(support_split=(3, 3))
    rendered = parse_and_render_activated_policy(
        policy_v3.canonical_policy_json(policy), activation
    )
    descriptor = coset_batch_map_descriptor_registered(
        rendered.candidates,
        policy_sha256=rendered.policy_sha256,
        renderer_activation=activation_document,
    )

    assert rendered.activation == activation_document
    assert descriptor["renderer_activation"] == activation_document
    assert descriptor["batch"]["renderer_activation_sha256"] == (
        activation_document["activation_sha256"]
    )


@pytest.mark.parametrize("catalog_kind", ("action", "cover", "protograph"))
def test_unknown_catalogs_produce_non_executable_handoff(catalog_kind):
    review = _review(
        _focus("renderer_descriptor_id", COSET_RENDERER_V3_ID),
        _focus("catalog_manifest_id", f"unknown-{catalog_kind}-catalog-v1"),
        _focus("catalog_kind", catalog_kind),
        _focus("support_split_type", "2+4"),
    )
    resolution = _resolve(review)

    assert resolution["status"] == "representation_expansion_handoff"
    assert resolution["renderer_activation"] is None
    assert resolution["renderer_activation_sha256"] is None
    handoff = resolution["representation_expansion_handoff"]
    assert handoff["execution_permitted"] is False
    assert handoff["reason"] == "catalog_manifest_not_installed"


def test_unknown_renderer_and_unsupported_split_never_execute():
    unknown = _resolve(_review(
        _focus("renderer_descriptor_id", "unknown-renderer-v1"),
        _focus(
            "catalog_manifest_id", COSET_ACTION_CATALOG_V2_MANIFEST_ID
        ),
        _focus("catalog_kind", "action"),
        _focus("support_split_type", "2+4"),
    ))
    unsupported = _resolve(
        _review(_focus("support_split_type", "2+2"))
    )

    assert unknown["representation_expansion_handoff"]["reason"] == (
        "renderer_descriptor_not_installed"
    )
    assert unsupported["representation_expansion_handoff"]["reason"] == (
        "support_split_not_installed"
    )
    assert unknown["representation_expansion_handoff"][
        "execution_permitted"
    ] is False
    assert unsupported["representation_expansion_handoff"][
        "execution_permitted"
    ] is False


@pytest.mark.parametrize(
    "focus",
    (
        (_focus("renderer_descriptor_id", COSET_RENDERER_V3_ID),),
        (
            _focus("support_split_type", "2+4"),
            _focus("support_split_type", "3+3"),
        ),
    ),
)
def test_incomplete_or_ambiguous_proposal_is_a_handoff(focus):
    resolution = _resolve(_review(*focus))
    assert resolution["status"] == "representation_expansion_handoff"
    assert resolution["representation_expansion_handoff"][
        "execution_permitted"
    ] is False


def test_unsafe_reviewer_identifier_is_rejected_before_resolution():
    review = _review(
        _focus("renderer_descriptor_id", "builtins.eval(payload)"),
        _focus(
            "catalog_manifest_id", COSET_ACTION_CATALOG_V2_MANIFEST_ID
        ),
        _focus("catalog_kind", "action"),
        _focus("support_split_type", "2+4"),
    )
    with pytest.raises(ReviewError, match="registry identifier is unsafe"):
        validate_review(review, require_current=True)


def test_resolution_tampering_fails_exact_replay():
    review = _review(_focus("support_split_type", "2+4"))
    resolution = _resolve(review)
    tampered = copy.deepcopy(resolution)
    tampered["target_round"] = 9

    with pytest.raises(ReviewerRendererResolutionError):
        validate_reviewer_renderer_resolution(
            tampered,
            search_action=review["search_action"],
        )


def test_preflight_propagates_selected_activation_without_fallback(
    tmp_path, monkeypatch
):
    selected = _resolve(
        _review(_focus("support_split_type", "2+4"))
    )["renderer_activation"]
    monkeypatch.setenv(
        COSET_RENDERER_ACTIVATION_JSON_ENV,
        json.dumps(selected, sort_keys=True, separators=(",", ":")),
    )
    accepted_policy = policy_v3.default_policy(support_split=(2, 4))
    accepted_path = tmp_path / "accepted.json"
    accepted_path.write_text(policy_v3.canonical_policy_json(accepted_policy))
    accepted = preflight_coset_policy(accepted_path, hard_timeout_s=15.0)

    assert accepted.renderer_activation == selected
    assert {tuple(row["support_split"]) for row in accepted.candidates} == {
        (2, 4)
    }

    rejected_policy = policy_v3.default_policy(support_split=(3, 3))
    rejected_path = tmp_path / "rejected.json"
    rejected_path.write_text(policy_v3.canonical_policy_json(rejected_policy))
    with pytest.raises(InvalidCosetMutation, match="dsl_invalid"):
        preflight_coset_policy(rejected_path, hard_timeout_s=15.0)


def test_tampered_activation_environment_fails_before_any_fallback(
    tmp_path, monkeypatch
):
    selected = _resolve(
        _review(_focus("support_split_type", "2+4"))
    )["renderer_activation"]
    selected["approved_support_splits"] = [[3, 3]]
    monkeypatch.setenv(
        COSET_RENDERER_ACTIVATION_JSON_ENV,
        json.dumps(selected, sort_keys=True, separators=(",", ":")),
    )
    path = tmp_path / "policy.json"
    path.write_text(policy_v3.canonical_policy_json(
        policy_v3.default_policy(support_split=(3, 3))
    ))

    with pytest.raises(
        CosetMutationRuntimeError, match="renderer_activation_invalid"
    ):
        preflight_coset_policy(path, hard_timeout_s=15.0)


def test_flow_binds_reviewer_activation_to_exact_next_round_invocation(
    tmp_path, monkeypatch
):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    round_one = rounds_root / "round-001"
    round_two = rounds_root / "round-002"
    round_one.mkdir(parents=True)
    round_two.mkdir()
    review = validate_review(
        _review(_focus("support_split_type", "2+4")),
        require_current=True,
    )
    review_path = round_one / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )
    resolution_binding = flow_module._seal_round_renderer_resolution(
        round_number=1,
        round_dir=round_one,
        review=review,
        review_binding=review_binding,
    )
    assert resolution_binding is not None
    summary = {
        "round": 1,
        "review_binding": review_binding,
        flow_module.COSET_RENDERER_RESOLUTION_SUMMARY_FIELD: (
            resolution_binding
        ),
    }
    state = {"current_round": 1, "rounds": [summary]}
    config = FlowConfig(
        repo_dir=project,
        run_id="reviewer-next-round-activation-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )
    activation_path = flow_module._materialize_round_renderer_activation(
        config, state, round_two
    )
    assert activation_path is not None
    activation = json.loads(activation_path.read_text())
    assert activation["approved_support_splits"] == [[2, 4]]

    context_path = flow_module._freeze_round_context(
        config,
        state,
        round_two,
    )
    context = context_path.read_text()
    assert "## Independent reviewer search advisories" in context
    assert '"value": "2+4"' in context
    live_archive = tmp_path / "negative-archive.json"
    monkeypatch.setenv(
        "QCODE_COSET_NEGATIVE_ARCHIVE_PATH", str(live_archive)
    )
    launch = flow_module._evolution_launch_binding(
        config,
        context_path=context_path,
    )
    invocation = flow_module._fresh_invocation_binding(
        config,
        codex_identity=None,
        codex_version=None,
        codex_cwd=None,
        launch_binding=launch,
    )
    flow_module._validate_invocation_binding(config, invocation, launch)

    activation_descriptor = launch["coset_renderer_activation"]
    assert activation_descriptor["path"] == str(activation_path)
    assert activation_descriptor["sha256"] == hashlib.sha256(
        activation_path.read_bytes()
    ).hexdigest()
    assert invocation[
        flow_module.COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
    ] == activation["activation_sha256"]


def test_flow_rejected_renderer_advisory_uses_trusted_default_next_round(
    tmp_path,
):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    round_one = rounds_root / "round-001"
    round_two = rounds_root / "round-002"
    round_one.mkdir(parents=True)
    round_two.mkdir()
    review = validate_review(_review(
        _focus("renderer_descriptor_id", COSET_RENDERER_V3_ID),
        _focus("catalog_manifest_id", "unknown-protograph-v1"),
        _focus("catalog_kind", "protograph"),
        _focus("support_split_type", "2+4"),
    ), require_current=True)
    review_path = round_one / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )
    resolution_binding = flow_module._seal_round_renderer_resolution(
        round_number=1,
        round_dir=round_one,
        review=review,
        review_binding=review_binding,
    )
    assert resolution_binding is not None
    summary = {
        "round": 1,
        "review_binding": review_binding,
        flow_module.COSET_RENDERER_RESOLUTION_SUMMARY_FIELD: (
            resolution_binding
        ),
    }
    state = {"current_round": 1, "rounds": [summary]}
    config = FlowConfig(
        repo_dir=project,
        run_id="reviewer-handoff-no-fallback-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )
    activation_path = flow_module._materialize_round_renderer_activation(
        config, state, round_two
    )
    assert activation_path is not None
    assert json.loads(activation_path.read_text()) == (
        coset_renderer_activation_document(
            default_coset_renderer_activation()
        )
    )

    resolution = flow_module._validated_bound_renderer_resolution(
        summary, rounds_root
    )
    state.update({
        "status": "search-complete",
        "renderer_expansion_handoff_at_round": 1,
        "renderer_expansion_handoff_sha256": resolution[
            "resolution_sha256"
        ],
    })
    assert flow_module._validated_renderer_expansion_handoff(
        state, rounds_root
    ) == "search-complete"


def test_rejected_reviewer_renderer_advisory_does_not_stop_flow(tmp_path):
    project = Path(flow_module.__file__).resolve().parents[1]
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_text(json.dumps({
        "ell": 10,
        "m": 6,
        "n": 120,
        "k": 8,
        "d": 2,
        "fom": 8 * 4 / 120,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }) + "\n")

    rejected = validate_review(_review(
        _focus("renderer_descriptor_id", COSET_RENDERER_V2_ID),
        _focus(
            "catalog_manifest_id", COSET_ACTION_CATALOG_V2_MANIFEST_ID
        ),
        _focus("catalog_kind", "action"),
        _focus("support_split_type", "3+3"),
    ), require_current=True)

    class Reviewer:
        def review(self, _prompt, _round_dir):
            return copy.deepcopy(rejected)

    config = FlowConfig(
        repo_dir=repo,
        run_id="rejected-renderer-advisory-continues",
        max_rounds=2,
        candidate_file=source,
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        search_regime_policy_version=3,
        stop_on_representation_change=True,
        milp_top=0,
    )
    completed = HumanizeFlow(config, reviewer=Reviewer()).run()

    assert completed["status"] == "search-complete"
    assert completed["current_round"] == 2
    assert len(completed["rounds"]) == 2
    assert "renderer_expansion_handoff_at_round" not in completed
    assert "renderer_expansion_handoff_sha256" not in completed
    first_resolution = flow_module._validated_bound_renderer_resolution(
        completed["rounds"][0],
        repo
        / "results"
        / "humanize"
        / config.run_id
        / "rounds",
    )
    assert first_resolution is not None
    assert first_resolution["status"] == "representation_expansion_handoff"
    assert first_resolution["representation_expansion_handoff"][
        "execution_permitted"
    ] is False

    rounds_root = (
        repo / "results" / "humanize" / config.run_id / "rounds"
    )
    replay_state = copy.deepcopy(completed)
    replay_state["current_round"] = 1
    replay_state["rounds"] = [copy.deepcopy(completed["rounds"][0])]
    replay_state["search_regime"] = copy.deepcopy(
        completed["rounds"][0]["search_regime"]
    )
    context_path = flow_module._freeze_round_context(
        config,
        replay_state,
        rounds_root / "round-002",
    )
    context = context_path.read_text()
    assert "## Independent reviewer search advisories" not in context
    assert COSET_RENDERER_V2_ID not in context

    events = [
        json.loads(line)
        for line in (
            repo / "results" / "humanize" / config.run_id / "events.jsonl"
        ).read_text().splitlines()
    ]
    round_one = next(
        row
        for row in events
        if row.get("event") == "round_completed"
        and row.get("round_number") == 1
    )
    assert round_one["stop"] is False
    assert any(
        row.get("event") == "search_renderer_expansion_deferred"
        and row.get("round_number") == 1
        and row.get("execution_permitted") is False
        for row in events
    )


def test_prompt_exposes_only_installed_registry_and_handoff_semantics():
    prompt = build_review_prompt(
        round_number=7,
        contract={},
        candidates=[],
        audited=[],
        archive_top=[],
        trusted_exact_history=[],
        trusted_exact_wins=[],
        round_history=[],
        memory="",
    )
    assert COSET_RENDERER_V3_ID in prompt
    assert COSET_RENDERER_V2_ID not in prompt
    assert COSET_ACTION_CATALOG_V2_MANIFEST_ID in prompt
    assert "sealed non-executable advisory" in prompt
    assert "never stop the machine" in prompt
    assert "never module/callable names" in prompt
