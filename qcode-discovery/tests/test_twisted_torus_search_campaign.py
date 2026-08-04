"""Contracts for the expanded twisted-torus search representation."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest
from openevolve import Config

from evaluation.search_contract import (
    FINAL_GATE_PARETO_LATTICES,
    LEGACY_GEOMETRY_CONTRACT,
    TARGET_CELL_VOLUMES,
    TWISTED_TARGET_LATTICES,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    allowed_twists,
    geometry_contract_for_representation,
    lattices_for_geometry_contract,
    stage2_deep_lattices_for_geometry_contract,
)
from evolve import openevolve_evaluator as evaluator
from evolve import run_evolution as launcher
from evolve.seed_solution_twisted_torus import (
    CHALLENGE_TERM_SPLITS,
    MAX_TWISTED_POOL,
    MIN_CANDIDATES_PER_TWIST,
    _canonical_candidate_key,
    _default_twisted_pool_limit,
    _staggered_proposals,
    generate_candidates,
)
from humanize.escalation import (
    load_template_registry,
    parse_auto_escalation_policy,
)
from humanize.pipeline import PipelineConfig


PROJECT = Path(__file__).resolve().parents[1]
EVOLUTION_CONFIG = PROJECT / "evolve/config_twisted_torus.yaml"
PIPELINE_CONFIG = PROJECT / "configs/five_stage_campaign.twisted_torus_v1.json"
GEOMETRY_AUTO_CONFIG = (
    PROJECT
    / "configs/five_stage_campaign.cover_algebra.geometry_auto_v1.json"
)
REPRESENTATION_ID = "css-bb-twisted-torus-generator-v1"


def test_expanded_contract_covers_all_ordered_factor_shapes_and_twists():
    expected_targets = tuple(
        (ell, volume // ell)
        for volume in TARGET_CELL_VOLUMES
        for ell in range(2, volume)
        if volume % ell == 0 and volume // ell >= 2
    )
    assert TWISTED_TARGET_LATTICES == expected_targets
    assert len(TWISTED_TARGET_LATTICES) == 46

    contracted = lattices_for_geometry_contract(
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    assert contracted[: len(FINAL_GATE_PARETO_LATTICES)] == (
        FINAL_GATE_PARETO_LATTICES
    )
    assert len(contracted) == 49
    assert sum(
        len(allowed_twists(
            ell,
            m,
            contract=TWISTED_TORUS_GEOMETRY_CONTRACT,
        ))
        for ell, m in contracted
    ) == 876
    assert sum(_default_twisted_pool_limit(m) for _ell, m in contracted) == 3888
    assert 6 in allowed_twists(
        6, 30, contract=TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    assert len(stage2_deep_lattices_for_geometry_contract(
        LEGACY_GEOMETRY_CONTRACT
    )) == 11
    assert len(stage2_deep_lattices_for_geometry_contract(
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )) == 7
    assert geometry_contract_for_representation(REPRESENTATION_ID) == (
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    assert geometry_contract_for_representation(
        "css-bb-cover-algebra-generator-v2"
    ) == LEGACY_GEOMETRY_CONTRACT
    assert geometry_contract_for_representation(
        "css-bb-novel-ansatz-generator-v2"
    ) == LEGACY_GEOMETRY_CONTRACT
    assert geometry_contract_for_representation("css-bb-custom-v9") is None
    assert geometry_contract_for_representation(None) is None
    assert launcher._validated_search_geometry_contract(2) is None
    assert launcher._validated_search_geometry_contract(None) is None
    with pytest.raises(RuntimeError, match="schema v3 requires"):
        launcher._validated_search_geometry_contract(3)


def test_private_evaluator_env_selects_expanded_contract_before_import():
    script = (
        "import json; "
        "from evaluation.search_contract import "
        "ACTIVE_GEOMETRY_CONTRACT,EVOLUTION_LATTICES; "
        "from evolve.openevolve_evaluator import "
        "STAGE1_LATTICES,STAGE2_DEEP_LATTICES; "
        "from evolve.run_evolution import STAGE2_DEEP_LATTICE_COUNT; "
        "from evolve.run_evolution import "
        "_validated_search_geometry_contract; "
        "print(json.dumps([ACTIVE_GEOMETRY_CONTRACT,len(EVOLUTION_LATTICES),"
        "STAGE1_LATTICES,len(STAGE2_DEEP_LATTICES),"
        "STAGE2_DEEP_LATTICE_COUNT,"
        "_validated_search_geometry_contract(3)]))"
    )
    environment = dict(os.environ)
    environment["QCODE_SEARCH_GEOMETRY_CONTRACT"] = (
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    completed = subprocess.run(
        [sys.executable, "-c", script],
        cwd=PROJECT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    (
        active,
        count,
        probes,
        evaluator_deep,
        launcher_deep,
        launch_contract,
    ) = json.loads(completed.stdout)
    assert active == TWISTED_TORUS_GEOMETRY_CONTRACT
    assert count == 49
    assert probes == [[12, 6], [10, 10], [12, 12], [6, 30]]
    assert evaluator_deep == launcher_deep == 7
    assert launch_contract == TWISTED_TORUS_GEOMETRY_CONTRACT


def test_twisted_launcher_binds_contract_to_ids_invocation_and_failure_envelope(
    tmp_path,
):
    candidate_log = (tmp_path / "twisted-run/all_codes.jsonl").resolve()
    script = r'''import json
import os
from evolve import openevolve_evaluator as evaluator
from evolve import run_evolution as launcher

candidate_log = os.environ["TEST_CANDIDATE_LOG"]
os.environ[evaluator.CANDIDATE_LOG_PATH_ENV] = candidate_log
os.environ.pop(evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV, None)
dependencies = launcher._evaluator_dependency_identities()
launcher_id = launcher._winner_preflight_contract_id(
    launcher.EVALUATOR,
    dependencies,
    candidate_log_path=candidate_log,
)
evaluator_id = evaluator._current_winner_preflight_contract_id()

invocation = {
    "model_names": ["test-model"],
    "reasoning_effort": None,
    "codex_cli": False,
    "max_parallel_evaluations": 1,
    "api_base": "http://localhost:4000/v1",
    "temperature_disabled": False,
    "codex_version": None,
    "codex_cwd": None,
    "codex_executable_mode": None,
    launcher.SEARCH_GEOMETRY_CONTRACT_FIELD:
        launcher.TWISTED_TORUS_GEOMETRY_CONTRACT,
}
validated = launcher._validated_invocation_binding(invocation, None, None)
schema2_rejected = False
try:
    launcher._validated_search_geometry_contract(2)
except RuntimeError:
    schema2_rejected = True
missing_rejected = False
try:
    launcher._validated_invocation_binding(
        {key: value for key, value in invocation.items()
         if key != launcher.SEARCH_GEOMETRY_CONTRACT_FIELD},
        None,
        None,
    )
except RuntimeError:
    missing_rejected = True
wrong_rejected = False
try:
    launcher._validated_invocation_binding(
        {
            **invocation,
            launcher.SEARCH_GEOMETRY_CONTRACT_FIELD: "rectangular-v1",
        },
        None,
        None,
    )
except RuntimeError:
    wrong_rejected = True

os.environ[evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV] = "12345"
failure = evaluator._winner_preflight_failure_result(
    "bounded test failure", timed_out=True
)
recognized = launcher._exact_incomplete_winner_preflight_markers(
    failure, expected_contract_id=12345
)
failure_with_extra = dict(failure)
failure_with_extra["unbound_geometry_metric"] = 0.0
extra_rejected = launcher._exact_incomplete_winner_preflight_markers(
    failure_with_extra, expected_contract_id=12345
) is None
quota_metrics = evaluator._run_evaluation(
    lambda _ell, _m: [
        {
            "A_terms": [(0, 0), (1, 0)],
            "B_terms": [(0, 1), (1, 1)],
            "geometry": {
                "schema_version": 1,
                "family": "twisted_torus",
                "twist": twist,
            },
        }
        for twist in range(2)
    ],
    [(2, 2)],
    quick=True,
    candidate_log_path=candidate_log + ".quota",
)
quota_rejected = (
    quota_metrics["lattices_completed"] == 0
    and quota_metrics["lattice_failures"] == 1
    and any("twist quota is incomplete" in error
            for error in quota_metrics["errors"])
)
print(json.dumps({
    "launcher_id": launcher_id,
    "evaluator_id": evaluator_id,
    "invocation_contract": validated[
        launcher.SEARCH_GEOMETRY_CONTRACT_FIELD
    ],
    "schema2_rejected": schema2_rejected,
    "missing_rejected": missing_rejected,
    "wrong_rejected": wrong_rejected,
    "failure_recognized": recognized is not None,
    "extra_rejected": extra_rejected,
    "quota_rejected": quota_rejected,
}))
'''
    environment = dict(os.environ)
    environment["QCODE_SEARCH_GEOMETRY_CONTRACT"] = (
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    environment["TEST_CANDIDATE_LOG"] = str(candidate_log)
    completed = subprocess.run(
        [sys.executable, "-c", script],
        cwd=PROJECT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    result = json.loads(completed.stdout)
    assert result["launcher_id"] == result["evaluator_id"]
    assert result["invocation_contract"] == (
        TWISTED_TORUS_GEOMETRY_CONTRACT
    )
    assert result["schema2_rejected"] is True
    assert result["missing_rejected"] is True
    assert result["wrong_rejected"] is True
    assert result["failure_recognized"] is True
    assert result["extra_rejected"] is True
    assert result["quota_rejected"] is True


def test_twisted_seed_is_deterministic_legal_bounded_and_q_complete():
    first = generate_candidates(2, 90)
    second = generate_candidates(2, 90)
    assert first == second
    assert len(first) == _default_twisted_pool_limit(90) == 270
    assert len(first) <= MAX_TWISTED_POOL

    twist_counts = Counter(
        int(row["geometry"]["twist"]) for row in first
    )
    assert set(twist_counts) == set(range(90))
    assert max(twist_counts.values()) - min(twist_counts.values()) <= 1
    assert min(twist_counts.values()) >= MIN_CANDIDATES_PER_TWIST
    assert len({
        (
            row["geometry"]["twist"],
            _canonical_candidate_key(
                row["A_terms"],
                row["B_terms"],
                2,
                90,
                twist=row["geometry"]["twist"],
            ),
        )
        for row in first
    }) == len(first)
    for row in first:
        assert set(row) == {"A_terms", "B_terms", "geometry"}
        assert row["geometry"] == {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": row["geometry"]["twist"],
        }
        A = row["A_terms"]
        B = row["B_terms"]
        assert (len(A), len(B)) in CHALLENGE_TERM_SPLITS
        assert len(A) + len(B) <= 6
        assert len(A) == len(set(A))
        assert len(B) == len(set(B))
        assert sorted(A) != sorted(B)


def test_high_m_stagger_samples_beyond_a_shared_prefix():
    proposals = list(range(1200))
    sampled = {
        q: _staggered_proposals(
            proposals,
            ell=2,
            m=90,
            twist=q,
            sample_size=4,
        )
        for q in range(90)
    }
    assert all(rows[0] == 0 for rows in sampled.values())
    exposed = {value for rows in sampled.values() for value in rows[1:]}
    assert len(exposed) > 200
    assert max(exposed) > 1000


def test_translation_canonicalization_uses_twisted_relation():
    ell, m, twist = 6, 30, 6
    A = [(0, 0), (5, 2), (3, 7)]
    B = [(1, 4), (4, 11)]
    translated_a = [(x + 4, y + 9) for x, y in A]
    translated_b = [(x + 4, y + 9) for x, y in B]
    assert _canonical_candidate_key(
        A, B, ell, m, twist=twist
    ) == _canonical_candidate_key(
        translated_a,
        translated_b,
        ell,
        m,
        twist=twist,
    )


def test_openevolve_identity_preserves_legacy_and_binds_nonzero_twist():
    legacy = {
        "ell": 6,
        "m": 30,
        "A_terms": [(0, 0), (1, 0)],
        "B_terms": [(0, 1), (1, 1)],
    }
    explicit_zero = {
        **legacy,
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 0,
        },
    }
    twisted = {
        **legacy,
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 6,
        },
    }
    assert evaluator._definition_key(legacy) == evaluator._definition_key(
        explicit_zero
    )
    assert evaluator._definition_key(twisted) != evaluator._definition_key(
        legacy
    )
    legacy_payload = evaluator._candidate_definition_payload(
        (legacy["A_terms"], legacy["B_terms"]), ell=6, m=30
    )
    zero_payload = evaluator._candidate_definition_payload(
        {
            "A_terms": explicit_zero["A_terms"],
            "B_terms": explicit_zero["B_terms"],
            "geometry": explicit_zero["geometry"],
        },
        ell=6,
        m=30,
    )
    assert legacy_payload == zero_payload


def test_schema_v3_config_pipeline_and_registered_template_are_bound():
    evolution = Config.from_yaml(str(EVOLUTION_CONFIG))
    assert launcher._search_portfolio_schema_version(EVOLUTION_CONFIG) == 3
    assert launcher._validated_search_portfolio_config(
        evolution, schema_version=3
    ) == 42
    assert evolution.database.feature_dimensions == [
        "algebraic_relation_type",
        "support_split_type",
        "geometry_twist_class",
    ]
    assert evolution.evaluator.timeout == 2400

    pipeline = PipelineConfig.from_json(
        PIPELINE_CONFIG,
        repo_dir=PROJECT,
        run_id="twisted-torus-template-test",
    )
    assert pipeline.flow_config is not None
    assert pipeline.flow_config.search_representation_id == REPRESENTATION_ID
    assert pipeline.flow_config.evolution_config == EVOLUTION_CONFIG
    assert pipeline.flow_config.evolution_seed == (
        PROJECT / "evolve/seed_solution_twisted_torus.py"
    )
    assert pipeline.stage3_backend == "sat-sectors"

    registry = load_template_registry(repo_dir=PROJECT)
    template = registry.template(REPRESENTATION_ID)
    assert template.representation_id == REPRESENTATION_ID
    assert template.checkpoint_compatibility_group == REPRESENTATION_ID
    assert template.proof_compatible is True
    assert template.launch_compatible is True
    assert template.auto_materialize is True
    assert template.required_stage3_backend == "sat-sectors"
    for bound in (
        template.base_pipeline,
        template.evolution_config,
        template.evolution_seed,
    ):
        assert bound is not None
        payload = (PROJECT / bound.path).read_bytes()
        assert hashlib.sha256(payload).hexdigest() == bound.sha256


def test_geometry_auto_entry_selects_twisted_template_without_rebinding_old_entries():
    pipeline = PipelineConfig.from_json(
        GEOMETRY_AUTO_CONFIG,
        repo_dir=PROJECT,
        run_id="geometry-auto-entry-test",
    )
    assert pipeline.flow_config is not None
    assert pipeline.flow_config.search_representation_id == (
        "css-bb-cover-algebra-generator-v2"
    )
    assert pipeline.flow_config.search_regime_policy_version == 3
    assert pipeline.flow_config.stop_on_representation_change is True

    policy = parse_auto_escalation_policy(
        repo_dir=PROJECT,
        pipeline_config_path=GEOMETRY_AUTO_CONFIG,
    )
    assert policy.enabled is True
    assert policy.source_search_representation_id == (
        "css-bb-cover-algebra-generator-v2"
    )
    assert policy.source_search_regime_policy_version == 3
    assert policy.source_max_rounds == 12
    assert policy.source_stop_on_representation_change is True
    assert policy.template_by_regime == {
        "representation_change_required": REPRESENTATION_ID,
    }
