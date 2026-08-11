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
    COSET_MAP_SCHEMA_METRIC,
    COSET_PROOF_LADDER_SCHEMA_VERSION,
    COSET_PROOF_LADDER_VERSION_METRIC,
    TRUSTED_COSET_SUPPORT_SPLITS,
    activate_coset_renderer_proposal,
    coset_batch_map_descriptor_registered,
    coset_renderer_activation_document,
    coset_renderer_proposal_document,
    coset_renderer_portfolio_contract,
    trusted_coset_catalog_registry_document,
    trusted_coset_renderer_activation_from_document,
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
V3_GPT56_FULL_CAMPAIGN = (
    PROJECT
    / "configs/five_stage_campaign.coset_two_block_actions_v3."
    "gpt56sol_full_orbit_review_fix_v1_20260809.json"
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


def test_only_2_plus_4_activation_drives_exact_mutation_walk_bounds():
    proposal = coset_renderer_proposal_document(
        renderer_descriptor_id=COSET_RENDERER_V3_ID,
        catalog_manifest_id=COSET_ACTION_CATALOG_V2_MANIFEST_ID,
        support_splits=((2, 4),),
    )
    activation_document = coset_renderer_activation_document(
        activate_coset_renderer_proposal(proposal)
    )

    prompt = launcher._coset_mutation_bounds_prompt(activation_document)

    assert (
        "action_id=coset2bga-l120-m32-s3-degree60-v2: "
        "left indices 0..118; right indices 0..28; walk offset "
        "0..434825; walk stride 1..434825, "
        "gcd(stride,434826)=1."
    ) in prompt
    assert "2850525" not in prompt
    assert "keep actions in ascending action_id order" in prompt
    assert "left and right indices must be strictly increasing" in prompt
    assert "strictly lexicographically increasing by (left,right)" in prompt
    assert "rejects noncanonical ordering instead of repairing it" in prompt

    config = Config.from_yaml(str(V3_CONFIG))
    assert "canonicalizes generated candidates" in config.prompt.system_message
    assert "Policy arrays are not repaired" in config.prompt.system_message


def test_activation_compatible_program_ids_exclude_other_support_splits():
    proposal = coset_renderer_proposal_document(
        renderer_descriptor_id=COSET_RENDERER_V3_ID,
        catalog_manifest_id=COSET_ACTION_CATALOG_V2_MANIFEST_ID,
        support_splits=((2, 4),),
    )
    activation_document = coset_renderer_activation_document(
        activate_coset_renderer_proposal(proposal)
    )
    programs = {
        "split-3-plus-3": Program(
            id="split-3-plus-3",
            code=policy_v3.canonical_policy_json(
                policy_v3.default_policy(support_split=(3, 3))
            ),
        ),
        "split-2-plus-4": Program(
            id="split-2-plus-4",
            code=policy_v3.canonical_policy_json(
                policy_v3.default_policy(support_split=(2, 4))
            ),
        ),
    }
    database = SimpleNamespace(programs=programs)

    compatible = launcher._activation_compatible_coset_program_ids(
        database,
        activation_document,
    )

    assert set(compatible) == {"split-2-plus-4"}


@pytest.mark.parametrize(
    ("support_splits", "expected_report_schema"),
    (
        (((2, 4),), 3),
        (((2, 4), (2, 3), (3, 2), (3, 3)), 4),
    ),
)
def test_activation_bridge_replaces_incompatible_epoch_with_evaluated_root(
    monkeypatch,
    support_splits,
    expected_report_schema,
):
    proposal = coset_renderer_proposal_document(
        renderer_descriptor_id=COSET_RENDERER_V3_ID,
        catalog_manifest_id=COSET_ACTION_CATALOG_V2_MANIFEST_ID,
        support_splits=support_splits,
    )
    activation_document = coset_renderer_activation_document(
        activate_coset_renderer_proposal(proposal)
    )
    old_split = (3, 3) if expected_report_schema == 3 else (4, 2)
    old = Program(
        id=f"old-{old_split[0]}-plus-{old_split[1]}",
        code=policy_v3.canonical_policy_json(
            policy_v3.default_policy(support_split=old_split)
        ) + "\n",
        metrics={},
        metadata={"island": 0},
        iteration_found=25,
    )
    database = SimpleNamespace(
        config=SimpleNamespace(num_islands=5, archive_size=192),
        programs={old.id: old},
        last_iteration=25,
        current_island=0,
        island_generations=[0] * 5,
        last_migration_generation=0,
        islands=[{old.id}, set(), set(), set(), set()],
        island_feature_maps=[{} for _ in range(5)],
        archive={old.id},
        best_program_id=old.id,
        island_best_programs=[old.id, None, None, None, None],
        feature_stats={},
        diversity_cache={},
        diversity_reference_set=[],
    )
    source_program_set_sha256 = launcher._coset_checkpoint_program_set_sha256(
        database
    )

    def fake_root_evaluation(
        _evaluator_path,
        code,
        *,
        expected_contract_id,
        wall_timeout,
        expected_map_schema_version,
    ):
        del wall_timeout
        rendered = parse_and_render_activated_policy(
            code,
            trusted_coset_renderer_activation_from_document(
                activation_document
            ),
        )
        descriptor = coset_batch_map_descriptor_registered(
            rendered.candidates,
            policy_sha256=rendered.policy_sha256,
            renderer_activation=rendered.activation,
        )
        metrics = {
            "combined_score": 0.0,
            launcher.MAP_DESCRIPTOR_VERSION_METRIC: float(
                launcher.MAP_DESCRIPTOR_VERSION
            ),
            launcher.COSET_GENOME_FORMAT_ID_METRIC: (
                launcher.COSET_TYPED_DSL_GENOME_FORMAT_ID_V3
            ),
            COSET_MAP_SCHEMA_METRIC: float(expected_map_schema_version),
            COSET_PROOF_LADDER_VERSION_METRIC: float(
                COSET_PROOF_LADDER_SCHEMA_VERSION
            ),
            **{
                name: float(value)
                for name, value in descriptor["coordinates"].items()
            },
        }
        return metrics, {}, {
            "path": "/tmp/candidates.jsonl",
            "start_offset": 10,
            "end_offset": 20,
            "sha256": "a" * 64,
            "bytes": 10,
            "wal_clean": True,
        }

    monkeypatch.setattr(
        launcher,
        "_execute_coset_checkpoint_root_evaluation",
        fake_root_evaluation,
    )
    report = launcher._install_coset_activation_bridge_epoch(
        database,
        source_checkpoint={
            "path": "/tmp/checkpoint_25",
            "sha256": "b" * 64,
            "last_iteration": 25,
            "programs": 1,
        },
        evaluator_path="/tmp/evaluator.py",
        expected_contract_id=17,
        wall_timeout=10.0,
        cascade_threshold=2.0,
        expected_map_schema_version=COSET_MAP_SCHEMA_VERSION_V3,
        activation_document=activation_document,
    )

    assert report["schema_version"] == expected_report_schema
    assert report["source_program_set_sha256"] == source_program_set_sha256
    if expected_report_schema == 3:
        assert report["approved_support_split"] == [2, 4]
    else:
        assert report["approved_support_splits"] == [
            list(split) for split in support_splits
        ]
        assert report["root_support_split"] == [2, 4]
    assert list(database.programs) == [report["root_program_id"]]
    assert old.id not in set().union(*database.islands)
    assert launcher._activation_compatible_coset_program_ids(
        database, activation_document
    ) == (report["root_program_id"],)


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


def test_gpt56_full_orbit_review_campaign_keeps_production_budget():
    raw = json.loads(V3_GPT56_FULL_CAMPAIGN.read_text())
    assert raw["run_id"] == (
        "qcode-coset-two-block-actions-v3-scalar-proof-v1-gpt56sol-"
        "20260809-full-orbit-fix-v1"
    )
    assert raw["max_total_workers"] == 12
    assert raw["stage1"]["max_rounds"] == 12
    assert raw["stage1"]["iterations_per_round"] == 25
    assert raw["stage1"]["model"] == "gpt-5.6-sol"
    assert raw["stage1"]["reasoning_effort"] == "xhigh"
    assert raw["stage1"]["review_model"] == "gpt-5.6-sol"
    assert raw["stage1"]["review_effort"] == "xhigh"
    assert raw["stage2"]["top"] == 48
    assert raw["stage3"]["top"] == 0
    assert raw["certificate"]["total_timeout"] == 86400
    assert raw["strict"]["total_timeout"] == 21600
    assert raw["review"] == {
        "enabled": True,
        "model": "gpt-5.6-sol",
        "effort": "xhigh",
    }

    campaign = PipelineConfig.from_json(
        V3_GPT56_FULL_CAMPAIGN,
        repo_dir=PROJECT,
    )
    assert campaign.flow_config is not None
    assert campaign.flow_config.search_representation_id == (
        COSET_REPRESENTATION_ID_V3
    )
    assert campaign.flow_config.max_rounds == 12
    assert campaign.flow_config.iterations_per_round == 25


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
