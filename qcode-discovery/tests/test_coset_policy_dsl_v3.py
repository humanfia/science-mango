"""Fail-closed contracts for trusted coset renderer v3."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from openevolve import Config
from openevolve.database import Program

from evaluation.coset_two_block import build_coset_candidate
from evolve import coset_policy_dsl as policy_v2
from evolve import coset_policy_dsl_v3 as policy_v3
from evolve import run_evolution as launcher
from evolve.coset_policy_dispatch import (
    parse_and_render_activated_policy,
    parse_and_render_registered_policy,
)
from evolve.coset_mutation_preflight import preflight_coset_policy
from evolve.coset_search_contract import (
    COSET_ACTION_CATALOG_V2_MANIFEST_ID,
    COSET_MAP_SCHEMA_VERSION_V3,
    COSET_RENDERER_V2_CHECKPOINT_GROUP,
    COSET_RENDERER_V3_CHECKPOINT_GROUP,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID_V3,
    TRUSTED_COSET_SUPPORT_SPLITS,
    activate_coset_renderer_proposal,
    coset_batch_map_descriptor_registered,
    coset_renderer_activation_document,
    coset_renderer_proposal_document,
    coset_renderer_portfolio_contract,
    trusted_coset_catalog_registry_document,
)
from humanize import flow as flow_module
from humanize.flow import FlowConfig
from humanize.pipeline import PipelineConfig


PROJECT = Path(__file__).resolve().parents[1]
V2_SEED = PROJECT / "evolve/coset_seed_solution_v2.py"
V3_SEED = PROJECT / "evolve/coset_seed_solution_v3.py"
V3_CONFIG = PROJECT / "evolve/coset_config_v3.yaml"
V3_CAMPAIGN = (
    PROJECT / "configs/five_stage_campaign.coset_two_block_actions_v3.json"
)


@pytest.mark.parametrize("support_split", TRUSTED_COSET_SUPPORT_SPLITS)
def test_every_whitelisted_split_renders_and_builds(support_split):
    policy = policy_v3.default_policy(support_split=support_split)
    encoded = policy_v3.canonical_policy_json(policy)
    assert policy_v3.parse_policy(encoded) == policy

    candidates = policy_v3.render_candidates(policy)
    assert len(candidates) == 384
    assert len({json.dumps(row, sort_keys=True) for row in candidates}) == 384
    assert {tuple(row["support_split"]) for row in candidates} == {
        support_split
    }
    code = build_coset_candidate(candidates[0])
    assert code.num_qudits > 0
    assert code.matrix_x.shape[1] == code.num_qudits
    assert code.matrix_z.shape[1] == code.num_qudits

    descriptor = coset_batch_map_descriptor_registered(
        candidates,
        policy_sha256=policy_v3.policy_digest(policy),
    )
    assert descriptor["schema_version"] == COSET_MAP_SCHEMA_VERSION_V3
    assert descriptor["support_split"] == list(support_split)
    assert descriptor["coordinates"]["coset_support_split_bucket"] == (
        TRUSTED_COSET_SUPPORT_SPLITS.index(support_split)
    )
    assert descriptor["renderer_activation"]["activation_sha256"]


def test_v3_seed_is_canonical_and_uses_only_static_dispatch():
    payload = V3_SEED.read_text().strip()
    rendered = parse_and_render_registered_policy(payload)
    assert rendered.descriptor.descriptor_id == COSET_RENDERER_V3_ID
    assert rendered.descriptor.representation_id == COSET_REPRESENTATION_ID_V3
    assert policy_v3.canonical_policy_json(rendered.policy) == payload
    assert len(rendered.candidates) == 384
    assert rendered.activation is not None
    assert rendered.activation["activation_sha256"]

    # Exercise the production mutation child, not only the in-process API.
    preflight = preflight_coset_policy(V3_SEED, hard_timeout_s=15.0)
    assert preflight.policy_sha256 == rendered.policy_sha256
    assert len(preflight.candidates) == 384


def test_reviewer_proposal_validates_activates_and_really_renders():
    proposal = coset_renderer_proposal_document(
        renderer_descriptor_id=COSET_RENDERER_V3_ID,
        catalog_manifest_id=COSET_ACTION_CATALOG_V2_MANIFEST_ID,
        support_splits=TRUSTED_COSET_SUPPORT_SPLITS,
    )
    activation = activate_coset_renderer_proposal(proposal)
    activation_document = coset_renderer_activation_document(activation)
    assert activation_document["catalog_handler_id"] == (
        "action-catalog-v2-static"
    )
    assert len(activation_document["activation_sha256"]) == 64

    rendered = parse_and_render_activated_policy(
        V3_SEED.read_text(), activation
    )
    assert len(rendered.candidates) == 384


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("catalog_kind", "cover"),
        ("catalog_kind", "protograph"),
        ("catalog_manifest_id", "reviewer-supplied-arbitrary-module"),
        ("catalog_manifest_sha256", "0" * 64),
        ("renderer_descriptor_id", "reviewer.eval(payload)"),
    ),
)
def test_unknown_or_tampered_reviewer_catalog_never_activates(field, value):
    proposal = coset_renderer_proposal_document()
    proposal[field] = value
    with pytest.raises(ValueError):
        activate_coset_renderer_proposal(proposal)


def test_policy_cannot_supply_code_or_unknown_registry_fields():
    document = policy_v3.policy_document(policy_v3.default_policy())
    document["callable"] = "builtins.eval"
    with pytest.raises(policy_v3.CosetPolicyV3Error, match="fields are not exact"):
        policy_v3.parse_policy(json.dumps(document))

    document.pop("callable")
    document["renderer_registry_sha256"] = "0" * 64
    with pytest.raises(policy_v3.CosetPolicyV3Error, match="registry"):
        policy_v3.parse_policy(json.dumps(document))


def test_explicit_v2_migration_replays_supports_but_epochs_stay_distinct():
    v2_payload = V2_SEED.read_text()
    old_rows = policy_v2.render_candidates(policy_v2.parse_policy(v2_payload))
    migrated = policy_v3.migrate_v2_policy(v2_payload)
    new_rows = policy_v3.render_candidates(migrated)
    project = lambda row: (
        row["action_id"],
        tuple(row["left_support"]),
        tuple(row["right_support"]),
    )
    assert {project(row) for row in new_rows} == {
        project(row) for row in old_rows
    }
    assert COSET_RENDERER_V2_CHECKPOINT_GROUP != (
        COSET_RENDERER_V3_CHECKPOINT_GROUP
    )
    with pytest.raises(policy_v3.CosetPolicyV3Error):
        policy_v3.parse_policy(v2_payload)
    with pytest.raises(policy_v2.CosetPolicyError):
        policy_v2.parse_policy(V3_SEED.read_text())


def test_v2_checkpoint_fails_closed_under_v3_config():
    v2_program = Program(
        id="v2",
        code=V2_SEED.read_text(),
        metrics={launcher.COSET_GENOME_FORMAT_ID_METRIC: 1.0},
    )
    database = SimpleNamespace(programs={v2_program.id: v2_program})
    with pytest.raises(RuntimeError, match="renderer epoch is incompatible"):
        launcher._strict_coset_checkpoint_genome_kind(
            database,
            expected_map_schema_version=COSET_MAP_SCHEMA_VERSION_V3,
        )


def test_v3_launcher_and_humanize_defaults_select_registered_epoch():
    assert launcher.DEFAULT_CONFIG_COSET_TWO_BLOCK.endswith(
        "coset_config_v3.yaml"
    )
    assert launcher.SEED_SOLUTION_COSET_TWO_BLOCK.endswith(
        "coset_seed_solution_v3.py"
    )
    assert launcher._coset_search_portfolio_schema_version(V3_CONFIG) == 4
    config = Config.from_yaml(str(V3_CONFIG))
    assert launcher._validated_coset_search_portfolio_config(config, 4) == 53

    flow_config = FlowConfig(
        repo_dir=PROJECT,
        run_id="renderer-v3-default-contract",
        evolution_evaluator="coset-two-block",
        search_representation_id=COSET_REPRESENTATION_ID_V3,
    )
    assert flow_module._expected_evolution_config(flow_config) == V3_CONFIG
    assert flow_module._expected_evolution_seed(flow_config) == V3_SEED
    invocation = flow_module._fresh_invocation_binding(
        flow_config,
        codex_identity=None,
        codex_version=None,
        codex_cwd=None,
    )
    assert len(invocation[
        flow_module.COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
    ]) == 64
    flow_contract = flow_module._coset_search_portfolio_contract_from_config(
        V3_CONFIG
    )
    renderer_contract = coset_renderer_portfolio_contract(
        COSET_REPRESENTATION_ID_V3
    )
    assert flow_contract == (
        4,
        tuple(renderer_contract["feature_dimensions"]),
        renderer_contract["feature_bins"],
    )


def test_v3_five_stage_template_uses_the_new_renderer_and_sat_gate():
    campaign = PipelineConfig.from_json(V3_CAMPAIGN, repo_dir=PROJECT)
    assert campaign.flow_config is not None
    assert campaign.flow_config.evolution_config == V3_CONFIG
    assert campaign.flow_config.evolution_seed == V3_SEED
    assert campaign.flow_config.search_representation_id == (
        COSET_REPRESENTATION_ID_V3
    )
    assert campaign.stage2_compact_low_weight_max_weight == 4


def test_flow_config_and_explicit_yaml_representation_mismatch_fails_closed():
    flow_config = FlowConfig(
        repo_dir=PROJECT,
        run_id="renderer-epoch-mismatch",
        evolution_config=V3_CONFIG,
        evolution_evaluator="coset-two-block",
        search_representation_id=policy_v2.COSET_REPRESENTATION_ID,
    )
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="disagrees with the coset evolution config",
    ):
        flow_module._expected_evolution_seed(flow_config)


def test_dependency_fingerprint_includes_all_v3_execution_sources():
    required = {
        "coset_policy_dsl_v3",
        "coset_policy_dispatch",
        "coset_negative_archive",
        "coset_sparse_kernel_oracle",
        "coset_witness_symmetry_verifier",
    }
    assert required <= set(launcher.COSET_EVALUATOR_DEPENDENCIES)
    for name in required:
        assert (PROJECT / launcher.COSET_EVALUATOR_DEPENDENCIES[name]).is_file()
    assert trusted_coset_catalog_registry_document()["manifests"][0][
        "handler_id"
    ] == "action-catalog-v2-static"
