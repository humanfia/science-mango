"""Reviewer proposals can select only sealed, installed coset renderers."""

from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from evolve import coset_policy_dsl_v3 as policy_v3
from evolve.coset_mutation_preflight import (
    CosetMutationRuntimeError,
    InvalidCosetMutation,
    preflight_coset_policy,
)
from evolve.coset_policy_dispatch import (
    CosetPolicyDispatchError,
    parse_and_render_activated_policy,
)
from evolve.coset_search_contract import (
    COSET_ACTION_CATALOG_V2_MANIFEST_ID,
    COSET_RENDERER_ACTIVATION_JSON_ENV,
    COSET_RENDERER_V2_ID,
    COSET_RENDERER_V3_ID,
    coset_batch_map_descriptor_registered,
    coset_renderer_activation_document,
    default_coset_renderer_activation,
    trusted_coset_renderer_descriptor,
    trusted_coset_renderer_activation_from_document,
)
from humanize import coset_renderer_review as renderer_review_module
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
ROUND_FIVE_REVIEW_SHA256 = (
    "1ccb9f0319a9fa28bceba9788b326110641a775ea6c6a5c993531a2ae5c6ed9c"
)


def _focus(
    dimension: str,
    value: str,
    *,
    direction: str = "increase",
) -> dict:
    return {
        "dimension": dimension,
        "value": value,
        "direction": direction,
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


def _sealed_flow_review_summary(
    rounds_root: Path,
    round_number: int,
    review_value: dict,
) -> tuple[dict, dict]:
    round_dir = rounds_root / f"round-{round_number:03d}"
    round_dir.mkdir(parents=True, exist_ok=True)
    review = validate_review(review_value, require_current=True)
    review_path = round_dir / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )
    resolution_binding = flow_module._seal_round_renderer_resolution(
        round_number=round_number,
        round_dir=round_dir,
        review=review,
        review_binding=review_binding,
    )
    summary = {
        "round": round_number,
        "review_binding": review_binding,
    }
    if resolution_binding is not None:
        summary[flow_module.COSET_RENDERER_RESOLUTION_SUMMARY_FIELD] = (
            resolution_binding
        )
    return summary, review


def _context_search_actions(text: str) -> list[dict]:
    marker = "## Independent reviewer search advisories\n"
    if marker not in text:
        return []
    encoded = text.split(marker, 1)[1].split(
        "```json\n", 1
    )[1].split("\n```", 1)[0]
    return json.loads(encoded)


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


def test_decrease_split_activation_excludes_only_the_selected_split():
    review = _review(_focus(
        "support_split_type",
        "4+2",
        direction="decrease",
    ))
    resolution = _resolve(review)
    descriptor = trusted_coset_renderer_descriptor(
        descriptor_id=COSET_RENDERER_V3_ID
    )
    expected = [
        list(split)
        for split in descriptor.support_splits
        if split != (4, 2)
    ]

    assert resolution["reviewer_proposal"][
        "support_split_direction"
    ] == "decrease"
    assert resolution["renderer_activation"][
        "approved_support_splits"
    ] == expected
    activation = trusted_coset_renderer_activation_from_document(
        resolution["renderer_activation"]
    )
    accepted = policy_v3.default_policy(support_split=(2, 4))
    parse_and_render_activated_policy(
        policy_v3.canonical_policy_json(accepted), activation
    )
    rejected = policy_v3.default_policy(support_split=(4, 2))
    with pytest.raises(ValueError, match="support split is not approved"):
        parse_and_render_activated_policy(
            policy_v3.canonical_policy_json(rejected), activation
        )


def test_maintain_split_activation_keeps_exact_selected_split():
    review = _review(_focus(
        "support_split_type",
        "3+2",
        direction="maintain",
    ))
    resolution = _resolve(review)

    assert resolution["reviewer_proposal"][
        "support_split_direction"
    ] == "maintain"
    assert resolution["renderer_activation"][
        "approved_support_splits"
    ] == [[3, 2]]


def test_decrease_with_empty_installed_complement_seals_handoff(monkeypatch):
    installed = trusted_coset_renderer_descriptor(
        descriptor_id=COSET_RENDERER_V3_ID
    )
    singleton = replace(installed, support_splits=((4, 2),))
    monkeypatch.setattr(
        renderer_review_module,
        "trusted_coset_renderer_descriptor",
        lambda *, descriptor_id: singleton,
    )
    review = _review(_focus(
        "support_split_type",
        "4+2",
        direction="decrease",
    ))

    resolution = _resolve(review)

    assert resolution["status"] == "representation_expansion_handoff"
    assert resolution["renderer_proposal"] is None
    assert resolution["renderer_activation"] is None
    handoff = resolution["representation_expansion_handoff"]
    assert handoff["reason"] == "support_split_complement_empty"
    assert handoff["execution_permitted"] is False


def test_legacy_direction_blind_resolution_remains_exactly_replayable():
    review = _review(_focus(
        "support_split_type",
        "4+2",
        direction="decrease",
    ))
    action = validate_review(review, require_current=True)["search_action"]
    legacy = renderer_review_module._resolve_reviewer_renderer_action(
        action,
        source_round=5,
        target_round=6,
        review_artifact_sha256=ROUND_FIVE_REVIEW_SHA256,
        legacy=True,
    )
    assert legacy is not None

    assert legacy["schema_version"] == 1
    assert legacy["renderer_activation"][
        "approved_support_splits"
    ] == [[4, 2]]
    assert legacy["reviewer_proposal_sha256"] == (
        "92fd52c19c59c978a3e9f090da65cc6e5ba4e5e41623ccfe8ea0aaca56f09c6a"
    )
    assert legacy["renderer_activation_sha256"] == (
        "b2425ec851285d6e6bc82ed80dbc45d6454e812618febad25c88f3da25cc259c"
    )
    assert legacy["resolution_sha256"] == (
        "ba6fc687879b2706980a24bba63166e1879bfdbe4c723e409ae1291aeb069c1b"
    )
    assert validate_reviewer_renderer_resolution(
        legacy, search_action=action
    ) == legacy
    current = resolve_reviewer_renderer_action(
        action,
        source_round=5,
        target_round=6,
        review_artifact_sha256=ROUND_FIVE_REVIEW_SHA256,
    )
    assert current is not None
    assert [4, 2] not in current["renderer_activation"][
        "approved_support_splits"
    ]


def test_legacy_handoff_proposal_and_hashes_remain_frozen():
    review = _review(
        _focus(
            "renderer_descriptor_id",
            "unknown-renderer-v1",
            direction="decrease",
        ),
        _focus(
            "catalog_manifest_id",
            COSET_ACTION_CATALOG_V2_MANIFEST_ID,
            direction="increase",
        ),
        _focus("catalog_kind", "action", direction="maintain"),
        _focus("support_split_type", "4+2", direction="decrease"),
    )
    action = validate_review(review, require_current=True)["search_action"]

    legacy = renderer_review_module._resolve_reviewer_renderer_action(
        action,
        source_round=5,
        target_round=6,
        review_artifact_sha256=REVIEW_SHA256,
        legacy=True,
    )

    assert legacy is not None
    assert legacy["schema_version"] == 1
    assert legacy["status"] == "representation_expansion_handoff"
    assert legacy["reviewer_proposal_sha256"] == (
        "7478fe71fc9f5f1bc36ffc5ae4ac7b688366cc00cd73f56dc3e35823b27e8320"
    )
    handoff = legacy["representation_expansion_handoff"]
    assert handoff["handoff_sha256"] == (
        "2e4ff2dcac9ced7a7229a1334c1cff927c9028853707eb3acc424c4b99e350b3"
    )
    assert legacy["resolution_sha256"] == (
        "4c25fb33b4eb722d9e2bbe8788d4f9aeab907f97b9721cd691b15dc99131f7a6"
    )
    assert validate_reviewer_renderer_resolution(
        legacy,
        search_action=action,
    ) == legacy


def test_flow_recovery_preserves_valid_legacy_resolution_bytes(tmp_path):
    rounds_root = tmp_path / "rounds"
    round_one = rounds_root / "round-001"
    round_one.mkdir(parents=True)
    review = validate_review(_review(_focus(
        "support_split_type",
        "4+2",
        direction="decrease",
    )), require_current=True)
    review_path = round_one / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )
    legacy = renderer_review_module._resolve_reviewer_renderer_action(
        review["search_action"],
        source_round=1,
        target_round=2,
        review_artifact_sha256=review_binding["artifact_sha256"],
        legacy=True,
    )
    assert legacy is not None
    resolution_path = (
        round_one / flow_module.COSET_RENDERER_RESOLUTION_FILENAME
    )
    atomic_write_json(resolution_path, legacy)
    original = resolution_path.read_bytes()

    binding = flow_module._seal_round_renderer_resolution(
        round_number=1,
        round_dir=round_one,
        review=review,
        review_binding=review_binding,
    )

    assert binding is not None
    assert resolution_path.read_bytes() == original
    assert json.loads(original)["schema_version"] == 1
    assert binding["activation_sha256"] == legacy[
        "renderer_activation_sha256"
    ]


def test_v2_resolution_direction_tampering_fails_exact_replay():
    review = _review(_focus("support_split_type", "2+4"))
    resolution = _resolve(review)
    changed_action = copy.deepcopy(review["search_action"])
    changed_action["focus"][0]["direction"] = "decrease"

    with pytest.raises(
        ReviewerRendererResolutionError,
        match="does not replay exactly",
    ):
        validate_reviewer_renderer_resolution(
            resolution,
            search_action=changed_action,
        )


def test_unhashable_renderer_direction_fails_with_resolution_error():
    action = validate_review(
        _review(_focus("support_split_type", "2+4")),
        require_current=True,
    )["search_action"]
    action = copy.deepcopy(action)
    action["focus"][0]["direction"] = ["decrease"]

    with pytest.raises(
        ReviewerRendererResolutionError,
        match="direction is invalid",
    ):
        resolve_reviewer_renderer_action(
            action,
            source_round=1,
            target_round=2,
            review_artifact_sha256=REVIEW_SHA256,
        )


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


def test_newest_overlapping_renderer_advisory_matches_strict_activation(
    tmp_path,
):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    older_value = _review(_focus("support_split_type", "2+3"))
    older_value["search_action"]["horizon_rounds"] = 2
    older, _ = _sealed_flow_review_summary(rounds_root, 2, older_value)
    newest_value = _review(_focus("support_split_type", "3+2"))
    newest_value["search_action"]["horizon_rounds"] = 2
    newest, _ = _sealed_flow_review_summary(rounds_root, 3, newest_value)
    round_four = rounds_root / "round-004"
    round_four.mkdir()
    state = {
        "current_round": 3,
        "rounds": [{"round": 1}, older, newest],
    }
    config = FlowConfig(
        repo_dir=project,
        run_id="newest-overlapping-renderer-advisory-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )

    activation_path = flow_module._materialize_round_renderer_activation(
        config, state, round_four
    )
    activation_document = json.loads(activation_path.read_text())
    assert activation_document["approved_support_splits"] == [[3, 2]]
    context = flow_module._freeze_round_context(
        config, state, round_four
    ).read_text()
    assert '"value": "3+2"' in context
    assert '"value": "2+3"' not in context

    activation = trusted_coset_renderer_activation_from_document(
        activation_document
    )
    rejected = policy_v3.default_policy(support_split=(2, 3))
    with pytest.raises(
        CosetPolicyDispatchError,
        match="support split is not approved",
    ):
        parse_and_render_activated_policy(
            policy_v3.canonical_policy_json(rejected), activation
        )


def test_overlapping_nonconflicting_advisory_dimensions_are_both_retained(
    tmp_path,
):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    older_value = _review(_focus(
        "mutation_tactic", "novel_structure_exploration"
    ))
    older_value["search_action"]["horizon_rounds"] = 2
    older, _ = _sealed_flow_review_summary(rounds_root, 2, older_value)
    newest_value = _review(_focus("support_split_type", "3+2"))
    newest_value["search_action"]["horizon_rounds"] = 2
    newest, _ = _sealed_flow_review_summary(rounds_root, 3, newest_value)
    round_four = rounds_root / "round-004"
    round_four.mkdir()
    config = FlowConfig(
        repo_dir=project,
        run_id="nonconflicting-overlapping-advisory-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )
    context = flow_module._freeze_round_context(
        config,
        {"current_round": 3, "rounds": [{"round": 1}, older, newest]},
        round_four,
    ).read_text()
    actions = _context_search_actions(context)

    assert [row["round"] for row in actions] == [2, 3]
    assert '"value": "novel_structure_exploration"' in context
    assert '"value": "3+2"' in context


def test_handoff_nonrenderer_focus_shadows_older_same_dimension(tmp_path):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    older_value = _review(
        _focus("support_split_type", "2+4"),
        _focus("mutation_tactic", "novel_structure_exploration"),
    )
    older_value["search_action"]["horizon_rounds"] = 2
    older, _ = _sealed_flow_review_summary(rounds_root, 1, older_value)
    handoff_value = _review(
        _focus("renderer_descriptor_id", COSET_RENDERER_V3_ID),
        _focus("catalog_manifest_id", "unknown-action-catalog-v1"),
        _focus("catalog_kind", "action"),
        _focus("support_split_type", "2+3"),
        _focus("mutation_tactic", "repair_x_low_weight"),
    )
    handoff_value["search_action"]["horizon_rounds"] = 2
    handoff, _ = _sealed_flow_review_summary(
        rounds_root, 2, handoff_value
    )
    round_three = rounds_root / "round-003"
    round_three.mkdir()
    config = FlowConfig(
        repo_dir=project,
        run_id="handoff-nonrenderer-newest-wins-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )

    activation_path = flow_module._materialize_round_renderer_activation(
        config,
        {"current_round": 2, "rounds": [older, handoff]},
        round_three,
    )
    assert json.loads(activation_path.read_text()) == (
        coset_renderer_activation_document(
            default_coset_renderer_activation()
        )
    )
    context = flow_module._freeze_round_context(
        config,
        {"current_round": 2, "rounds": [older, handoff]},
        round_three,
    ).read_text()
    actions = _context_search_actions(context)

    assert [row["round"] for row in actions] == [2]
    assert '"value": "repair_x_low_weight"' in context
    assert '"value": "novel_structure_exploration"' not in context
    assert '"value": "2+4"' not in context
    assert '"value": "2+3"' not in context
    assert "unknown-action-catalog-v1" not in context


def test_reject_round_keeps_action_for_audit_but_seals_no_resolution(
    tmp_path,
):
    rounds_root = tmp_path / "rounds"
    round_one = rounds_root / "round-001"
    round_one.mkdir(parents=True)
    review_value = _review(_focus("support_split_type", "2+4"))
    review_value["verdict"] = "reject_round"
    review = validate_review(review_value, require_current=True)
    review_path = round_one / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )

    assert review_binding["search_action"] == review["search_action"]
    assert flow_module._seal_round_renderer_resolution(
        round_number=1,
        round_dir=round_one,
        review=review,
        review_binding=review_binding,
    ) is None
    assert not (
        round_one / flow_module.COSET_RENDERER_RESOLUTION_FILENAME
    ).exists()
    summary = {"round": 1, "review_binding": review_binding}
    assert flow_module._bound_executable_search_action(
        summary, rounds_root, 2
    ) is None


def test_historical_reject_resolution_cannot_execute_and_defaults_next_round(
    tmp_path,
):
    project = Path(flow_module.__file__).resolve().parents[1]
    rounds_root = tmp_path / "rounds"
    round_one = rounds_root / "round-001"
    round_two = rounds_root / "round-002"
    round_one.mkdir(parents=True)
    round_two.mkdir()
    review_value = _review(_focus("support_split_type", "2+4"))
    review_value["verdict"] = "reject_round"
    review = validate_review(review_value, require_current=True)
    review_path = round_one / "review.json"
    atomic_write_json(review_path, review)
    review_binding = flow_module._review_artifact_binding(
        review_path, review
    )

    # Reproduce an artifact emitted by the old controller, which resolved the
    # copied action without consulting the authenticated verdict.
    historical_resolution = resolve_reviewer_renderer_action(
        review["search_action"],
        source_round=1,
        target_round=2,
        review_artifact_sha256=review_binding["artifact_sha256"],
    )
    assert historical_resolution is not None
    resolution_path = (
        round_one / flow_module.COSET_RENDERER_RESOLUTION_FILENAME
    )
    atomic_write_json(resolution_path, historical_resolution)
    descriptor = flow_module._file_descriptor(
        resolution_path, "historical reviewer renderer resolution"
    )
    resolution_binding = {
        **descriptor,
        "status": historical_resolution["status"],
        "source_round": 1,
        "target_round": 2,
        "activation_sha256": historical_resolution[
            "renderer_activation_sha256"
        ],
        "resolution_sha256": historical_resolution["resolution_sha256"],
    }
    summary = {
        "round": 1,
        "review_binding": review_binding,
        flow_module.COSET_RENDERER_RESOLUTION_SUMMARY_FIELD: (
            resolution_binding
        ),
    }
    assert flow_module._validated_bound_renderer_resolution(
        summary, rounds_root
    ) is None

    config = FlowConfig(
        repo_dir=project,
        run_id="historical-reject-default-renderer-test",
        evolution_evaluator="coset-two-block",
        evolution_config=project / "evolve/coset_config_v3.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v3.py",
        search_representation_id="css-coset-two-block-actions-v3",
        milp_top=0,
    )
    state = {"current_round": 1, "rounds": [summary]}
    activation_path = flow_module._materialize_round_renderer_activation(
        config, state, round_two
    )
    assert json.loads(activation_path.read_text()) == (
        coset_renderer_activation_document(
            default_coset_renderer_activation()
        )
    )
    context_path = flow_module._freeze_round_context(
        config, state, round_two
    )
    assert "Independent reviewer search advisories" not in (
        context_path.read_text()
    )


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
    assert "direction=decrease" in prompt
    assert "authorizes every installed split except that value" in prompt
    assert "never stop the machine" in prompt
    assert "never module/callable names" in prompt
