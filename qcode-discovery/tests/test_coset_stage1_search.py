"""Contracts for the independent coset two-block Stage-1 representation."""

from __future__ import annotations

import ast
import copy
import json
import math
import os
import signal
import subprocess
import sys
from collections import Counter
from pathlib import Path

import numpy as np
import pytest
from openevolve import Config

from evaluation.coset_action_catalog import action_catalog_sha256
from evolve import coset_openevolve_evaluator as evaluator
from evolve import coset_seed_solution as seed_module
from evolve import run_evolution as launcher
from evolve.coset_search_contract import (
    COSET_REPRESENTATION_ID,
    action_search_view,
    action_search_views,
    candidate_digest,
    normalize_candidate,
    quota_by_normality,
)
from evolve.coset_seed_solution import generate_candidates
from humanize import flow as flow_module
from scripts import audit_candidate_pool as candidate_pool


PROJECT = Path(__file__).resolve().parents[1]
EVOLUTION_CONFIG = PROJECT / "evolve/coset_config.yaml"
EVOLUTION_SEED = PROJECT / "evolve/coset_seed_solution.py"
PIPELINE_CONFIG = (
    PROJECT / "configs/five_stage_campaign.coset_two_block_v1.json"
)


def _published_candidate():
    view = next(
        item for item in action_search_views()
        if item.published_left_support is not None
    )
    return normalize_candidate({
        "schema_version": 1,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": view.action_id,
        "left_support": list(view.published_left_support),
        "right_support": list(view.published_right_support),
    })


def test_catalog_drives_balanced_normal_and_nonnormal_seed_pool():
    views = action_search_views()
    assert {(view.subgroup_normal, view.block_size) for view in views} == {
        (False, 112),
        (True, 72),
    }
    published = next(view for view in views if not view.subgroup_normal)
    assert len(published.left_element_ids) == 224
    assert len(published.right_element_ids) == 28
    assert published.published_left_support is not None
    assert published.published_right_support is not None

    quotas = quota_by_normality(views, 31)
    assert sum(quotas.values()) == 31
    assert sum(
        quota for view in views if not view.subgroup_normal
        for quota in (quotas[view.action_id],)
    ) == 24
    assert sum(
        quota for view in views if view.subgroup_normal
        for quota in (quotas[view.action_id],)
    ) == 7
    first = generate_candidates(32)
    second = generate_candidates(32)
    assert first == second
    assert len(first) == len({json.dumps(row, sort_keys=True) for row in first}) == 32
    counts = Counter(row["action_id"] for row in first)
    assert {
        by_normality: sum(
            counts[view.action_id]
            for view in views
            if view.subgroup_normal is by_normality
        )
        for by_normality in (False, True)
    } == {False: 24, True: 8}
    by_id = {view.action_id: view for view in views}
    for raw in first:
        candidate = normalize_candidate(raw)
        view = by_id[candidate["action_id"]]
        assert len(candidate["left_support"]) == 3
        assert len(candidate["right_support"]) == 3
        assert view.left_identity_id in candidate["left_support"]
        assert view.right_identity_id in candidate["right_support"]


def test_fallback_pool_is_deterministic_but_changes_with_evolved_support(
    monkeypatch,
):
    baseline_proposals = copy.deepcopy(seed_module._propose_coset_supports())
    monkeypatch.setattr(
        seed_module,
        "_propose_coset_supports",
        lambda: copy.deepcopy(baseline_proposals),
    )
    baseline = seed_module.generate_candidates(64)
    assert baseline == seed_module.generate_candidates(64)

    mutated_proposals = copy.deepcopy(baseline_proposals)
    target = mutated_proposals[0]
    view = next(
        item for item in action_search_views()
        if item.action_id == target["action_id"]
    )
    replacement = next(
        element for element in view.left_element_ids
        if element not in target["left_support"]
    )
    target["left_support"][1] = replacement
    monkeypatch.setattr(
        seed_module,
        "_propose_coset_supports",
        lambda: copy.deepcopy(mutated_proposals),
    )
    mutated = seed_module.generate_candidates(64)
    assert mutated == seed_module.generate_candidates(64)

    baseline_digests = {candidate_digest(row) for row in baseline}
    mutated_digests = {candidate_digest(row) for row in mutated}
    # A single accepted structural mutation re-keys both action traversals;
    # only the other explicit proposal anchors should normally overlap.
    assert len(baseline_digests & mutated_digests) <= 8


def test_candidate_schema_rejects_bb_fields_proof_claims_and_bad_supports():
    candidate = _published_candidate()
    for forbidden in ("distance", "bp_distance", "hx", "ell"):
        with pytest.raises(ValueError, match="unknown fields"):
            normalize_candidate({**candidate, forbidden: 99})
    with pytest.raises(ValueError, match=r"3\+3"):
        normalize_candidate({**candidate, "left_support": candidate["left_support"][:2]})
    with pytest.raises(ValueError, match="duplicate"):
        normalize_candidate({
            **candidate,
            "left_support": [candidate["left_support"][0]] * 3,
        })
    with pytest.raises(ValueError, match="incompatible"):
        normalize_candidate({**candidate, "representation_id": "css-bb-v1"})


def test_published_action_rebuilds_exact_k_and_combined_degree_six():
    row = evaluator._static_candidate(_published_candidate())
    assert (row["n"], row["k"], row["rank_x"], row["rank_z"]) == (
        224,
        12,
        106,
        106,
    )
    assert row["css_commutation"] is True
    assert row["max_check_weight"] == 6
    # Each sector contributes degree three. The challenge degree is their sum,
    # not max(HX degree, HZ degree).
    assert row["max_qubit_degree"] == 6
    assert row["tanner_components"] == 1
    assert row["static_legal"] is True
    assert row["construction"] == {
        "kind": "coset-two-block-v1",
        "action_id": row["action_id"],
        "action_catalog_sha256": action_catalog_sha256(),
        "left_support": row["candidate"]["left_support"],
        "right_support": row["candidate"]["right_support"],
    }


def test_disconnected_tanner_graph_is_not_statically_legal(monkeypatch):
    candidate = _published_candidate()
    hx = np.zeros((112, 224), dtype=np.uint8)
    hz = np.zeros((112, 224), dtype=np.uint8)
    monkeypatch.setattr(
        evaluator,
        "_matrix_pair_from_builder",
        lambda _candidate: (hx, hz),
    )
    row = evaluator._static_candidate(candidate)
    assert row["css_commutation"] is True
    assert row["tanner_components"] == 448
    assert row["static_legal"] is False


def test_fitness_ignores_decoder_upper_bounds_and_uses_only_proof_signals():
    base = {
        "static_legal": True,
        "threshold_rejected": False,
        "n": 224,
        "k": 12,
        "distance_lower_bound": None,
        "exact_distance": None,
    }
    baseline = evaluator._fitness(base)
    assert evaluator._fitness({
        **base,
        "bp_distance_upper_bound": 10_000,
        "decoder_logical_weight": 10_000,
    }) == baseline
    assert evaluator._fitness({**base, "distance_lower_bound": 5}) > baseline
    assert evaluator._fitness({**base, "exact_distance": 16}) > baseline
    assert evaluator._fitness({**base, "threshold_rejected": True}) == 0.0


def test_evaluator_emits_numeric_metrics_and_stage2_rebuildable_rows(
    tmp_path,
    monkeypatch,
):
    program = tmp_path / "program.py"
    program.write_text(
        "from evolve.coset_seed_solution import generate_candidates as _seed\n"
        "def generate_candidates():\n"
        "    return _seed(2)\n"
    )
    candidate_log = (tmp_path / "all_codes.jsonl").resolve()
    monkeypatch.setenv(evaluator.CANDIDATE_LOG_PATH_ENV, str(candidate_log))
    monkeypatch.setenv(evaluator.PREFLIGHT_CONTRACT_ID_ENV, "12345")

    result = evaluator.evaluate_stage1(str(program))
    metrics = result.metrics
    assert metrics
    assert all(
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
        for value in metrics.values()
    )
    assert metrics[evaluator.EVALUATOR_KIND_ID_METRIC] == 1.0
    assert metrics[evaluator.ACTION_CATALOG_ID_METRIC] == float(
        int(action_catalog_sha256()[:13], 16)
    )
    assert "winner_preflight_lattices" not in metrics
    assert metrics[evaluator.PREFLIGHT_UNIT_KIND_ID_METRIC] == 1.0
    assert metrics[evaluator.PREFLIGHT_UNITS_METRIC] == 2.0
    assert metrics[evaluator.PREFLIGHT_ACTION_STRATA_METRIC] == 2.0
    launcher._validated_winner_preflight_markers(
        metrics,
        expected_contract_id=12345,
        evaluator_kind="coset-two-block",
    )
    with pytest.raises(RuntimeError, match="marker"):
        launcher._validated_winner_preflight_markers(
            metrics,
            expected_contract_id=12345,
            evaluator_kind="default",
        )
    assert metrics["winner_preflight_contract_id"] == 12345.0
    assert metrics["winner_preflight_winner_capable_persisted"] == metrics[
        "winner_preflight_winner_capable_eligible"
    ]
    rows = [json.loads(line) for line in candidate_log.read_text().splitlines()]
    assert rows
    assert metrics["candidate_log_records_persisted"] == len(rows)
    terminal = [
        row for row in rows if row.get("search_status") == "terminal_negative"
    ]
    assert terminal
    assert metrics["low_weight_rejections"] == len(terminal)
    assert metrics["winner_preflight_winner_capable_persisted"] == (
        len(rows) - len(terminal)
    )
    for row in rows:
        construction = row["construction"]
        assert set(construction) == {
            "kind",
            "action_id",
            "action_catalog_sha256",
            "left_support",
            "right_support",
        }
        assert construction["action_catalog_sha256"] == action_catalog_sha256()
    feedback = flow_module._build_search_oracle_feedback(
        round_number=1,
        source_candidate_batch={
            "path": "candidate-batch.jsonl",
            "sha256": "a" * 64,
            "bytes": candidate_log.stat().st_size,
            "rows": len(rows),
        },
        candidate_rows=rows,
    )
    assert feedback["observations"]
    assert all(
        observation["semantics"] == "negative_upper_bound_witness"
        for observation in feedback["observations"]
    )
    ranked, counts = candidate_pool.rank_candidate_files([candidate_log])
    assert counts["trusted_search_oracle_rejections"] == len(terminal)
    assert counts["rejected_candidates"] >= len(terminal)
    assert sum(
        candidate_pool._is_trusted_terminal_rejection(row) for row in ranked
    ) >= len(terminal)
    tampered = copy.deepcopy(terminal[0])
    tampered["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    tampered_log = tmp_path / "tampered-oracle.jsonl"
    tampered_log.write_text(json.dumps(tampered, sort_keys=True) + "\n")
    tampered_ranked, tampered_counts = candidate_pool.rank_candidate_files(
        [tampered_log]
    )
    assert tampered_counts.get("trusted_search_oracle_rejections", 0) == 0
    assert tampered_counts["eligible_candidates"] == 1
    assert not candidate_pool._is_trusted_terminal_rejection(
        tampered_ranked[0]
    )
    assert result.artifacts["evaluator_kind"] == "coset-two-block"
    assert result.artifacts["distance_semantics"][
        "bp_upper_bound_positive_credit"
    ] is False
    assert "negative-only evidence" in result.artifacts[
        "low_weight_oracle_failures"
    ]
    assert terminal[0]["action_id"] in result.artifacts[
        "low_weight_oracle_failures"
    ]


def test_evaluator_fails_closed_when_one_action_stratum_cannot_build(
    tmp_path,
    monkeypatch,
):
    program = tmp_path / "program.py"
    program.write_text(
        "from evolve.coset_seed_solution import generate_candidates as _seed\n"
        "def generate_candidates():\n"
        "    return _seed(2)\n"
    )
    original = evaluator._static_candidate
    failed_action = next(
        view.action_id for view in action_search_views()
        if view.subgroup_normal
    )

    def fail_one_action(candidate):
        if candidate["action_id"] == failed_action:
            raise RuntimeError("injected catalog builder failure")
        return original(candidate)

    monkeypatch.setattr(evaluator, "_static_candidate", fail_one_action)
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "all_codes.jsonl").resolve()),
    )
    monkeypatch.setenv(evaluator.PREFLIGHT_CONTRACT_ID_ENV, "12345")
    with pytest.raises(RuntimeError, match="every enabled action stratum"):
        evaluator.evaluate_stage1(str(program))


def test_cached_stage2_replays_and_excludes_coset_search_oracle_witness(
    tmp_path,
):
    normal_control = next(
        candidate for candidate in generate_candidates(2)
        if action_search_view(candidate["action_id"]).subgroup_normal
    )
    evaluated = evaluator._static_candidate(normal_control)
    evaluator._run_oracle(evaluated)
    evaluated["fitness"] = evaluator._fitness(evaluated)
    assert evaluated["oracle_outcome"] == "SAT"
    assert evaluated["threshold_rejected"] is True

    candidate_log = tmp_path / "oracle-negative.jsonl"
    candidate_log.write_text(
        json.dumps(evaluator._safe_json_row(evaluated), sort_keys=True) + "\n"
    )
    ranked, counts = candidate_pool.rank_candidate_files_with_structural_cache(
        [candidate_log],
        structural_cache_dir=tmp_path / "structural-cache",
        structural_max_workers=1,
        structural_hard_timeout=60.0,
    )
    assert len(ranked) == 1
    assert counts["trusted_search_oracle_rejections"] == 1
    assert counts["eligible_candidates"] == 0
    assert ranked[0]["trusted_search_oracle_rejection"] == {
        "validated": True,
        "outcome": "REJECTED",
        "source": "low_weight_oracle",
        "required_distance": ranked[0]["required_distance"],
        "witness_weight": evaluated["low_weight_witness"]["weight"],
        "oracle_evidence_sha256": evaluated["low_weight_oracle"][
            "evidence_sha256"
        ],
        "replay_policy": "exact-construction-current-source",
    }


def test_coset_candidate_log_recovers_sigkill_through_shared_wal(tmp_path):
    candidate_log = (tmp_path / "crash/all_codes.jsonl").resolve()
    candidate_log.parent.mkdir()
    script = """
import os
import signal
from evolve import openevolve_evaluator as shared
from evolve.coset_openevolve_evaluator import (
    _append_candidate_rows,
    _fitness,
    _static_candidate,
)
from evolve.coset_seed_solution import generate_candidates

row = _static_candidate(generate_candidates(2)[0])
row.update({
    "oracle_outcome": "NOT_RUN",
    "oracle_threshold": None,
    "low_weight_oracle": None,
    "distance_lower_bound": None,
    "low_weight_witness": None,
    "threshold_rejected": False,
    "search_status": "unresolved",
})
row["fitness"] = _fitness(row)

def crash_after_partial(descriptor, payload):
    os.write(descriptor, payload[:max(1, len(payload) // 3)])
    os.kill(os.getpid(), signal.SIGKILL)

shared._write_candidate_log_payload = crash_after_partial
_append_candidate_rows([row])
"""
    environment = dict(os.environ)
    environment[evaluator.CANDIDATE_LOG_PATH_ENV] = str(candidate_log)
    crashed = subprocess.run(
        [sys.executable, "-c", script],
        cwd=PROJECT,
        env=environment,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert crashed.returncode == -signal.SIGKILL
    wal_path = candidate_log.with_name(candidate_log.name + ".candidate-wal")
    assert wal_path.is_file()
    assert not candidate_log.read_bytes().endswith(b"\n")

    row = evaluator._static_candidate(generate_candidates(2)[1])
    row.update({
        "oracle_outcome": "NOT_RUN",
        "oracle_threshold": None,
        "low_weight_oracle": None,
        "distance_lower_bound": None,
        "low_weight_witness": None,
        "threshold_rejected": False,
        "search_status": "unresolved",
    })
    row["fitness"] = evaluator._fitness(row)
    previous = os.environ.get(evaluator.CANDIDATE_LOG_PATH_ENV)
    os.environ[evaluator.CANDIDATE_LOG_PATH_ENV] = str(candidate_log)
    try:
        assert evaluator._append_candidate_rows([row]) == 1
    finally:
        if previous is None:
            os.environ.pop(evaluator.CANDIDATE_LOG_PATH_ENV, None)
        else:
            os.environ[evaluator.CANDIDATE_LOG_PATH_ENV] = previous

    rows = [json.loads(line) for line in candidate_log.read_text().splitlines()]
    assert len(rows) == 2
    assert {item["action_id"] for item in rows} == {
        candidate["action_id"] for candidate in generate_candidates(2)
    }
    assert not wal_path.exists()


def test_coset_evaluator_has_no_decoder_import():
    source = Path(evaluator.__file__).read_text()
    tree = ast.parse(source)
    imports = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom))
        for alias in node.names
    }
    assert not any("bp" in name.lower() or "decoder" in name.lower() for name in imports)


def test_coset_config_selects_action_normality_and_orbit_map():
    config = Config.from_yaml(EVOLUTION_CONFIG)
    assert config.random_seed == 47
    assert config.evaluator.cascade_thresholds[0] > 1.0
    assert config.database.num_islands == 4
    assert config.database.feature_dimensions == [
        "coset_action_family",
        "coset_subgroup_normality",
        "coset_support_orbit",
    ]
    assert config.database.feature_bins == {
        "coset_action_family": 4,
        "coset_subgroup_normality": 2,
        "coset_support_orbit": 8,
    }
    campaign = json.loads(PIPELINE_CONFIG.read_text())
    assert campaign["stage1"].get(
        "evaluator_kind",
        campaign["stage1"].get("evolution_evaluator"),
    ) == "coset-two-block"
    assert campaign["stage1"]["search_representation_id"] == (
        COSET_REPRESENTATION_ID
    )


def test_launcher_rejects_cross_evaluator_resume_and_catalog_change():
    coset_metrics = {
        launcher.EVALUATOR_KIND_ID_METRIC: 1.0,
        launcher.ACTION_CATALOG_ID_METRIC: float(
            launcher._coset_action_catalog_contract_id()
        ),
    }
    assert launcher._checkpoint_evaluator_kind(
        {}, expected_kind="default", label="legacy BB checkpoint"
    ) == "default"
    assert launcher._checkpoint_evaluator_kind(
        coset_metrics,
        expected_kind="coset-two-block",
        label="coset checkpoint",
    ) == "coset-two-block"
    with pytest.raises(RuntimeError, match="not default"):
        launcher._checkpoint_evaluator_kind(
            coset_metrics,
            expected_kind="default",
            label="coset checkpoint",
        )
    with pytest.raises(RuntimeError, match="start a fresh checkpoint"):
        launcher._checkpoint_evaluator_kind(
            {},
            expected_kind="coset-two-block",
            label="BB checkpoint",
        )
    with pytest.raises(RuntimeError, match="action catalog id"):
        launcher._checkpoint_evaluator_kind(
            {**coset_metrics, launcher.ACTION_CATALOG_ID_METRIC: 0.0},
            expected_kind="coset-two-block",
            label="stale coset checkpoint",
        )


def test_coset_preflight_binds_the_exact_evaluator_dependency_set(tmp_path):
    default_dependencies = launcher._evaluator_dependency_identities()
    coset_dependencies = launcher._evaluator_dependency_identities(
        "coset-two-block"
    )
    assert set(coset_dependencies) == {
        *default_dependencies,
        *launcher.COSET_EVALUATOR_DEPENDENCIES,
    }
    for name, relative_path in launcher.COSET_EVALUATOR_DEPENDENCIES.items():
        assert Path(coset_dependencies[name]["path"]) == (
            PROJECT / relative_path
        ).resolve()
    contract_id = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR_COSET_TWO_BLOCK,
        coset_dependencies,
        candidate_log_path=(tmp_path / "coset/all_codes.jsonl").resolve(),
        evaluator_kind="coset-two-block",
    )
    assert 0 <= contract_id < 2**53
    with pytest.raises(RuntimeError, match="dependency set"):
        launcher._winner_preflight_contract_id(
            launcher.EVALUATOR_COSET_TWO_BLOCK,
            default_dependencies,
            candidate_log_path=(tmp_path / "coset/all_codes.jsonl").resolve(),
            evaluator_kind="coset-two-block",
        )


def test_launcher_coset_route_and_invocation_are_closed_and_source_bound():
    assert launcher._validated_evaluator_kind(
        "coset-two-block", noncss=False, milp=False
    ) == "coset-two-block"
    with pytest.raises(RuntimeError, match="unsupported evaluator"):
        launcher._validated_evaluator_kind(
            "/tmp/arbitrary.py", noncss=False, milp=False
        )
    with pytest.raises(RuntimeError, match="cannot be combined"):
        launcher._validated_evaluator_kind(
            "coset-two-block", noncss=False, milp=True
        )

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
        launcher.EVALUATOR_KIND_BINDING_FIELD: "coset-two-block",
        launcher.ACTION_CATALOG_SHA256_BINDING_FIELD: action_catalog_sha256(),
    }
    assert launcher._validated_invocation_binding(invocation, None, None) == invocation
    with pytest.raises(RuntimeError, match="coset binding is incomplete"):
        launcher._validated_invocation_binding(
            {
                key: value for key, value in invocation.items()
                if key != launcher.ACTION_CATALOG_SHA256_BINDING_FIELD
            },
            None,
            None,
        )
    with pytest.raises(RuntimeError, match="action catalog changed"):
        launcher._validated_invocation_binding(
            {
                **invocation,
                launcher.ACTION_CATALOG_SHA256_BINDING_FIELD: "0" * 64,
            },
            None,
            None,
        )


def test_launcher_cli_rejects_arbitrary_evaluator_path():
    completed = subprocess.run(
        [
            sys.executable,
            str(PROJECT / "evolve/run_evolution.py"),
            "--evaluator",
            "/tmp/arbitrary.py",
            "--iterations",
            "1",
        ],
        cwd=PROJECT,
        env=dict(os.environ),
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert completed.returncode == 2
    assert "invalid choice" in completed.stderr
