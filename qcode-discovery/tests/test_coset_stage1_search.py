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

from evaluation.coset_action_catalog import V2_CATALOG_ID, action_catalog_sha256
from evolve import coset_openevolve_evaluator as evaluator
from evolve import coset_policy_dsl as policy_dsl
from evolve import run_evolution as launcher
from evolve.coset_search_contract import (
    ActionSearchView,
    COSET_FEATURE_BINS,
    COSET_FEATURE_DIMENSIONS,
    COSET_MAP_SCHEMA_VERSION,
    COSET_PROOF_LADDER_SCHEMA_VERSION,
    COSET_PROOF_LADDER_VERSION_METRIC,
    COSET_REPRESENTATION_ID,
    action_search_view,
    action_search_views,
    candidate_digest,
    normalize_candidate,
    quota_by_normality,
)
from humanize import flow as flow_module
from scripts import audit_candidate_pool as candidate_pool


PROJECT = Path(__file__).resolve().parents[1]
EVOLUTION_CONFIG = PROJECT / "evolve/coset_config_v2.yaml"
PIPELINE_CONFIG = (
    PROJECT / "configs/five_stage_campaign.coset_two_block_actions_v2.json"
)


def _v2_catalog_sha256() -> str:
    return action_catalog_sha256(V2_CATALOG_ID)


def _render_default_policy(candidate_limit: int):
    return policy_dsl.render_candidates(
        policy_dsl.default_policy(candidate_limit)
    )


def _known_oracle_policy_json() -> str:
    """Encode the legacy low-weight control as data-only catalog indices."""

    document = policy_dsl.policy_document(policy_dsl.default_policy())
    for action in document["actions"]:
        view = action_search_view(action["action_id"])
        if not action["include_published"]:
            left = [
                item for item in view.left_element_ids
                if item != view.left_identity_id
            ]
            right = [
                item for item in view.right_element_ids
                if item != view.right_identity_id
            ]
            action["supports"] = [{
                "left": [0, len(left) - 1],
                "right": [0, len(right) - 1],
            }]
    return policy_dsl.canonical_policy_json(
        policy_dsl.parse_policy(json.dumps(document))
    ) + "\n"


def _render_known_oracle_policy():
    return policy_dsl.render_candidates(
        policy_dsl.parse_policy(_known_oracle_policy_json())
    )


def _published_candidate():
    view = action_search_view("coset2bga-l224-m53-s1-degree112-v2")
    return normalize_candidate({
        "schema_version": 2,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": view.action_id,
        "left_support": list(view.published_left_support),
        "right_support": list(view.published_right_support),
    })


def test_catalog_drives_balanced_normal_and_nonnormal_seed_pool():
    views = action_search_views()
    assert len(views) == 46
    assert sum(not view.subgroup_normal for view in views) == 45
    assert sum(view.subgroup_normal for view in views) == 1
    published = action_search_view("coset2bga-l224-m53-s1-degree112-v2")
    assert len(published.left_element_ids) == 224
    assert len(published.right_element_ids) == 28
    assert published.published_left_support is not None
    assert published.published_right_support is not None

    quotas = quota_by_normality(views, 31)
    assert sum(quotas.values()) == 31
    assert sum(
        quota for view in views if not view.subgroup_normal
        for quota in (quotas[view.action_id],)
    ) == 30
    assert sum(
        quota for view in views if view.subgroup_normal
        for quota in (quotas[view.action_id],)
    ) == 1
    first = _render_default_policy(64)
    second = _render_default_policy(64)
    assert first == second
    assert len(first) == len({json.dumps(row, sort_keys=True) for row in first}) == 64
    counts = Counter(row["action_id"] for row in first)
    assert {
        by_normality: sum(
            counts[view.action_id]
            for view in views
            if view.subgroup_normal is by_normality
        )
        for by_normality in (False, True)
    } == {False: 63, True: 1}
    by_id = {view.action_id: view for view in views}
    for raw in first:
        candidate = normalize_candidate(raw)
        view = by_id[candidate["action_id"]]
        assert len(candidate["left_support"]) == 3
        assert len(candidate["right_support"]) == 3
        assert view.left_identity_id in candidate["left_support"]
        assert view.right_identity_id in candidate["right_support"]


def test_policy_pool_is_deterministic_but_changes_with_evolved_walk():
    baseline_policy = policy_dsl.default_policy(64)
    baseline = policy_dsl.render_candidates(baseline_policy)
    assert baseline == policy_dsl.render_candidates(baseline_policy)

    mutated_document = policy_dsl.policy_document(baseline_policy)
    for action in mutated_document["actions"]:
        action["walk"] = {"enabled": True, "offset": 0, "stride": 1}
    mutated_text = json.dumps(
        mutated_document,
        sort_keys=True,
        separators=(",", ":"),
    )
    mutated_policy = policy_dsl.normalize_policy(json.loads(mutated_text))
    mutated = policy_dsl.render_candidates(mutated_policy)
    assert mutated == policy_dsl.render_candidates(
        policy_dsl.normalize_policy(json.loads(mutated_text))
    )

    baseline_digests = {candidate_digest(row) for row in baseline}
    mutated_digests = {candidate_digest(row) for row in mutated}
    # A structural walk mutation redirects all traversals; the 24 immutable
    # published anchors remain intentional overlap.
    assert len(baseline_digests & mutated_digests) <= 24


def test_production_batch_and_lane_quotas_are_rechecked_by_evaluator():
    candidates = policy_dsl.render_candidates(policy_dsl.default_policy())
    evaluator._validate_production_candidate_batch(candidates)

    with pytest.raises(RuntimeError, match="exact production batch"):
        evaluator._validate_production_candidate_batch(candidates[:-1])

    wrong_lane = copy.deepcopy(candidates)
    wrong_lane[0]["action_id"] = next(
        view.action_id
        for view in action_search_views()
        if view.action_id != wrong_lane[0]["action_id"]
    )
    with pytest.raises(RuntimeError, match="immutable action quotas"):
        evaluator._validate_production_candidate_batch(wrong_lane)


def test_structural_diversity_uses_fixed_bins_and_viable_coverage():
    views = sorted(action_search_views(), key=lambda view: view.action_id)
    sparse = [
        {
            "action_id": views[0].action_id,
            "subgroup_normal": views[0].subgroup_normal,
            "support_orbit_bin": 0,
        },
        {
            "action_id": views[1].action_id,
            "subgroup_normal": views[1].subgroup_normal,
            "support_orbit_bin": 1,
        },
    ]
    dense = sparse * (384 // len(sparse))

    assert evaluator._fixed_categorical_entropy(
        [row["action_id"] for row in sparse], category_count=2
    ) == pytest.approx(evaluator._fixed_categorical_entropy(
        [row["action_id"] for row in dense], category_count=2
    ))
    assert evaluator._structural_diversity(sparse) < (
        evaluator._structural_diversity(dense) / 100
    )

    # Oracle outcome is deliberately absent from the structural calculation;
    # pruning winner-capable rows cannot manufacture a diversity increase.
    rejected = [dict(row, threshold_rejected=True) for row in dense]
    assert evaluator._structural_diversity(rejected) == pytest.approx(
        evaluator._structural_diversity(dense)
    )


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
        "kind": "coset-two-block-v2",
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": row["action_id"],
        "action_catalog_id": V2_CATALOG_ID,
        "action_catalog_sha256": _v2_catalog_sha256(),
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


def test_dynamic_cutoff_uses_official_gate_and_ladder_reaches_odd_end():
    # No physically possible distance at n=3 can pass the final gate, so the
    # official cutoff is capped at n rather than the scalar-only value 6.
    assert evaluator._dynamic_rejection_cutoff(3, 1) == 3
    assert evaluator._proof_ladder(3) == (3,)

    # This exact-equality cutoff is odd and must not be skipped by a +2 ladder.
    # The block is larger than every published Pareto reference, so equality
    # itself is not a smaller-n win.
    assert evaluator._dynamic_rejection_cutoff(375, 180) == 5
    assert 180 * 5 * 5 == 12 * 375
    assert evaluator._proof_ladder(5) == (4, 5)
    assert evaluator._proof_ladder(3) == (3,)


def test_scalar_cutoff_keeps_pareto_diagnostics_but_rejects_48_8_d6(
    monkeypatch,
):
    """A [[48,8,6]] Pareto win must not stop the strict-FOM ladder."""

    monkeypatch.delenv(evaluator.CANDIDATE_LOG_PATH_ENV, raising=False)
    assert evaluator._dynamic_rejection_cutoff(48, 8) == 5
    assert evaluator._proof_rejection_cutoff(48, 8) == 8
    metadata = evaluator._cutoff_metadata(48, 8)
    assert {
        name: metadata[name]
        for name in (
            "fom_rejection_cutoff",
            "challenge_rejection_cutoff",
            "minimum_winning_distance",
            "minimum_scalar_fom_distance",
            "proof_target_mode",
        )
    } == {
        "fom_rejection_cutoff": 8,
        "challenge_rejection_cutoff": 5,
        "minimum_winning_distance": 6,
        "minimum_scalar_fom_distance": 9,
        "proof_target_mode": "scalar-fom-strict-v1",
    }
    assert metadata["target"] == evaluator.target_binding(
        48,
        8,
        evaluator.TARGET_MODE_SCALAR,
    )

    calls: list[tuple[str, int]] = []
    exact_distances = {"5" * 64: 5, "6" * 64: 6}

    def fake_rung(row, *, threshold, timeout_s, terminal_sectors):
        del timeout_s, terminal_sectors
        exact_distance = exact_distances[row["candidate_sha256"]]
        calls.append((row["candidate_sha256"], threshold))
        outcome = "SAT" if threshold >= exact_distance else "UNSAT"
        return {
            "outcome": outcome,
            "max_weight": threshold,
            "distance_lower_bound": (
                threshold + 1 if outcome == "UNSAT" else None
            ),
            "witness": (
                {
                    "side": "X",
                    "index": 0,
                    "weight": exact_distance,
                    "bits": [1] * exact_distance
                    + [0] * (48 - exact_distance),
                }
                if outcome == "SAT" else None
            ),
            "evidence_sha256": f"{threshold:064x}",
        }, {
            "hard_wall_timeout": False,
            "worker_failed": False,
            "elapsed_s": 0.01,
            "resumed_sectors": [],
        }

    monkeypatch.setattr(evaluator, "_run_oracle_rung_hard_wall", fake_rung)

    def row(distance: int):
        return {
            "candidate_sha256": str(distance) * 64,
            "static_legal": True,
            "n": 48,
            "k": 8,
            "hx": np.zeros((1, 48), dtype=np.uint8),
            "hz": np.zeros((1, 48), dtype=np.uint8),
        }

    distance_five = row(5)
    evaluator._run_oracle(distance_five)
    assert distance_five["search_status"] == "terminal_negative"
    assert distance_five["threshold_rejected"] is True
    assert distance_five["threshold_proof_distance"] == 5

    distance_six = row(6)
    evaluator._run_oracle(distance_six)
    assert distance_six["search_status"] == "terminal_negative"
    assert distance_six["threshold_rejected"] is True
    assert distance_six["distance_upper_bound"] == 6
    assert distance_six["challenge_target_excluded_by_upper_bound"] is False
    assert distance_six[
        "gist_challenge_possible_despite_selected_target_exclusion"
    ] is True
    assert distance_six["fom_target_lower_bound_proven"] is False
    assert distance_six["minimum_winning_distance"] == 6
    assert distance_six["challenge_rejection_cutoff"] == 5
    assert distance_six["fom_rejection_cutoff"] == 8
    direct = row(6)
    evaluator._apply_oracle_sat(
        direct,
        {
            "max_weight": 8,
            "witness": {
                "side": "X",
                "index": 0,
                "weight": 6,
                "bits": [1] * 6 + [0] * 42,
            },
        },
        cutoff=8,
    )
    assert direct["fom_target_excluded_by_upper_bound"] is True
    assert direct["final_gate_excluded_by_upper_bound"] is False
    assert calls == [
        ("5" * 64, 4),
        ("5" * 64, 6),
        ("6" * 64, 4),
        ("6" * 64, 6),
    ]


def test_proof_ladder_commits_retries_unknown_and_hydrates_retry_state(
    tmp_path,
    monkeypatch,
):
    candidate_log = (tmp_path / "run/all_codes.jsonl").resolve()
    candidate_log.parent.mkdir()
    monkeypatch.setenv(evaluator.CANDIDATE_LOG_PATH_ENV, str(candidate_log))

    monkeypatch.setattr(evaluator, "_ORACLE_UNKNOWN_RETRY_BACKOFF_S", 0.0)
    monkeypatch.setattr(
        evaluator,
        "_light_oracle_evidence_valid",
        lambda evidence, *, threshold: (
            isinstance(evidence, dict)
            and evidence.get("max_weight") == threshold
            and evidence.get("outcome") in {"SAT", "UNSAT", "UNKNOWN"}
        ),
    )
    calls: list[tuple[int, float]] = []
    outcomes = iter(("UNSAT", "UNKNOWN", "UNSAT", "SAT"))

    def fake_rung(
        _row,
        *,
        threshold,
        timeout_s,
        terminal_sectors,
    ):
        assert 0 < timeout_s <= evaluator.COSET_PROOF_STEP_HARD_TIMEOUT_S
        calls.append((threshold, timeout_s))
        outcome = next(outcomes)
        evidence = {
            "outcome": outcome,
            "max_weight": threshold,
            "distance_lower_bound": threshold + 1 if outcome == "UNSAT" else None,
            "witness": (
                {
                    "side": "X",
                    "index": 0,
                    "weight": threshold,
                    "bits": [1] * threshold + [0] * (16 - threshold),
                    "logical_syndrome": [1, 0, 0],
                    "support": list(range(threshold)),
                }
                if outcome == "SAT" else None
            ),
            "evidence_sha256": f"{len(calls):064x}",
        }
        return evidence, {
            "hard_wall_timeout": False,
            "worker_failed": False,
            "elapsed_s": 0.01,
            "resumed_sectors": sorted(terminal_sectors),
        }

    monkeypatch.setattr(evaluator, "_run_oracle_rung_hard_wall", fake_rung)
    candidate = _published_candidate()
    view = action_search_view(candidate["action_id"])
    base = {
        "candidate": candidate,
        "construction": evaluator._stage2_construction(candidate),
        "candidate_sha256": "a" * 64,
        "action_id": candidate["action_id"],
        "subgroup_normal": view.subgroup_normal,
        "support_orbit_bin": 0,
        "static_legal": True,
        "n": 16,
        "k": 3,
        "rank_x": 1,
        "rank_z": 12,
        "css_commutation": True,
        "max_check_weight": 6,
        "max_qubit_degree": 6,
        "tanner_components": 1,
        "hx": np.zeros((1, 16), dtype=np.uint8),
        "hz": np.zeros((1, 16), dtype=np.uint8),
    }

    first = copy.deepcopy(base)
    evaluator._run_oracle(first)
    assert [threshold for threshold, _timeout in calls] == [4, 6]
    assert first["distance_lower_bound"] == 5
    assert first["oracle_ladder_next_threshold"] == 6
    assert first["low_weight_oracle"]["outcome"] == "UNSAT"
    assert first["distance_lower_bound_evidence"]["outcome"] == "UNSAT"
    assert first["oracle_last_attempt"]["evidence"]["outcome"] == "UNKNOWN"
    assert first["oracle_evidence_sha256"] == (
        first["distance_lower_bound_evidence_sha256"]
    )
    first["fitness"] = evaluator._fitness(first)
    assert evaluator._append_candidate_rows([first]) == 1

    no_budget = copy.deepcopy(base)
    evaluator._run_oracle(
        no_budget,
        budget=evaluator._OracleBatchBudget(
            remaining_new_steps=0,
            deadline=evaluator.time.monotonic() + 30,
        ),
        max_new_steps=0,
    )
    assert [threshold for threshold, _timeout in calls] == [4, 6]
    assert no_budget["oracle_outcome"] == "UNKNOWN"
    assert no_budget["oracle_retryable"] is True
    assert no_budget["distance_lower_bound"] == 5
    assert no_budget["oracle_ladder_next_threshold"] == 6
    assert no_budget["oracle_last_attempt"]["timeout_s"] == 7.5

    terminal = copy.deepcopy(base)
    evaluator._run_oracle(terminal)
    assert [threshold for threshold, _timeout in calls] == [4, 6, 6, 8]
    assert [timeout for _threshold, timeout in calls] == [7.5, 7.5, 15.0, 7.5]
    assert terminal["oracle_outcome"] == "SAT"
    assert terminal["threshold_rejected"] is True
    assert terminal["fom_upper_bound"] == pytest.approx(3 * 8 * 8 / 16)
    assert terminal["fitness_distance_credit"] == 0.0

    # A retry generation is deliberately invisible to recovery until its
    # candidate row is durably appended and the generation is committed.
    terminal["fitness"] = evaluator._fitness(terminal)
    assert evaluator._append_candidate_rows([terminal]) == 1

    cache_root = candidate_log.parent / evaluator.COSET_PROOF_CACHE_DIRECTORY
    rung_six_base = cache_root / ("a" * 2) / ("a" * 64 + "-w6.json")
    cached = evaluator._load_cached_evidence(
        "a" * 64,
        6,
        hx=base["hx"],
        hz=base["hz"],
    )
    assert cached is not None
    assert not rung_six_base.exists()
    assert len(evaluator._proof_cache_version_paths(rung_six_base)) == 2
    assert cached["attempts"] == 2
    assert cached["latest_outcome"] == "UNSAT"
    assert evaluator._strict_self_hashed_mapping(
        cached["last_attempt"],
        hash_field="attempt_sha256",
    )


def test_all_unsat_single_evaluation_reaches_360_8_cutoff_23(monkeypatch):
    monkeypatch.delenv(evaluator.CANDIDATE_LOG_PATH_ENV, raising=False)
    calls: list[int] = []

    def fake_rung(_row, *, threshold, timeout_s, terminal_sectors):
        calls.append(threshold)
        return {
            "outcome": "UNSAT",
            "max_weight": threshold,
            "distance_lower_bound": threshold + 1,
            "witness": None,
            "evidence_sha256": f"{threshold:064x}",
        }, {
            "hard_wall_timeout": False,
            "worker_failed": False,
            "elapsed_s": 0.01,
            "resumed_sectors": [],
        }

    monkeypatch.setattr(evaluator, "_run_oracle_rung_hard_wall", fake_rung)
    row = {
        "candidate_sha256": "b" * 64,
        "static_legal": True,
        "n": 360,
        "k": 8,
        "hx": np.zeros((1, 360), dtype=np.uint8),
        "hz": np.zeros((1, 360), dtype=np.uint8),
    }
    result = evaluator._run_oracle(row)
    assert calls == [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 23]
    assert result["new_steps"] == 11
    assert row["oracle_ladder_complete"] is True
    assert row["distance_lower_bound"] == 24
    assert row["fom_target_lower_bound_proven"] is True


def test_batch_budget_never_shortens_a_configured_retry():
    now = evaluator.time.monotonic()
    short = evaluator._OracleBatchBudget(
        remaining_new_steps=1,
        deadline=now + 10.0,
    )
    assert short.claim_timeout(requested_cap_s=120.0) is None
    assert short.remaining_new_steps == 1

    complete = evaluator._OracleBatchBudget(
        remaining_new_steps=1,
        deadline=evaluator.time.monotonic() + 121.0,
    )
    assert complete.claim_timeout(requested_cap_s=120.0) == 120.0
    assert complete.remaining_new_steps == 0


def test_proof_frontier_hydrates_every_row_before_local_selection(monkeypatch):
    rows = [
        {
            "candidate_sha256": f"{index + 1:064x}",
            "static_legal": True,
            "k": 1,
            "subgroup_normal": index == 0,
        }
        for index in range(3)
    ]
    hydrated: set[str] = set()

    def fake_oracle(row, *, budget, max_new_steps=None):
        if max_new_steps == 0:
            hydrated.add(row["candidate_sha256"])
        row.update({
            "oracle_retryable": False,
            "threshold_rejected": False,
            "oracle_ladder_complete": True,
            "oracle_ladder_history": [],
        })
        return {"new_steps": 0, "cache_hits": 0, "deferred": False}

    monkeypatch.setattr(evaluator, "_run_oracle", fake_oracle)
    monkeypatch.setattr(
        evaluator,
        "_archive_and_annotate_negative_rows",
        lambda _rows: {
            "event_count": 0,
            "events_added": 0,
            "penalized_candidates": 0,
            "maximum_penalty": 0.0,
        },
    )
    monkeypatch.setattr(evaluator, "_fitness", lambda _row: 0.1)
    monkeypatch.setattr(evaluator, "_append_candidate_rows", lambda value: len(value))

    persisted, _statistics, _archive = (
        evaluator._run_proof_frontier_and_persist(rows, [rows[0]])
    )
    assert hydrated == {row["candidate_sha256"] for row in rows}
    assert persisted == 3


def test_run_global_frontier_rebuilds_historical_candidate(
    tmp_path,
    monkeypatch,
):
    candidate_log = (tmp_path / "run/all_codes.jsonl").resolve()
    candidate_log.parent.mkdir()
    monkeypatch.setenv(evaluator.CANDIDATE_LOG_PATH_ENV, str(candidate_log))
    rebuilt = []
    for candidate in _render_default_policy(64):
        row = evaluator._static_candidate(candidate)
        if row["static_legal"] and row["k"] > 0:
            rebuilt.append(row)
        if len(rebuilt) == 2:
            break
    assert len(rebuilt) == 2

    assert evaluator._global_proof_frontier_rows([rebuilt[0]]) == []
    injected = evaluator._global_proof_frontier_rows([rebuilt[1]])
    assert injected
    assert injected[0]["candidate_sha256"] == rebuilt[0]["candidate_sha256"]
    assert injected[0]["global_proof_frontier_injected"] is True
    assert injected[0]["candidate_persistence_lane"] == (
        "global_scalar_fom_proof_frontier"
    )

    frontier_path = (
        candidate_log.parent
        / evaluator.COSET_PROOF_CACHE_DIRECTORY
        / evaluator._GLOBAL_PROOF_FRONTIER_FILENAME
    )
    payload = json.loads(frontier_path.read_text())
    payload["candidates"][0]["n"] += 1
    frontier_path.write_text(json.dumps(payload))
    with pytest.raises(RuntimeError, match="validation failed"):
        evaluator._global_proof_frontier_rows([rebuilt[1]])


def test_oracle_probe_rotation_covers_large_catalog_and_keeps_control_quota(
    monkeypatch,
):
    views = tuple(
        ActionSearchView(
            action_id=f"action-{index:02d}",
            block_size=32,
            subgroup_normal=index == 45,
            action_family_bin=1 if index == 45 else 0,
            left_element_ids=("L0", "L1", "L2"),
            right_element_ids=("R0", "R1", "R2"),
            left_identity_id="L0",
            right_identity_id="R0",
        )
        for index in range(46)
    )
    monkeypatch.setattr(evaluator, "action_search_views", lambda: views)
    progressed = views[0].action_id
    monkeypatch.setattr(
        evaluator,
        "_cache_progress_hint",
        lambda row: 6 if row["action_id"] == progressed else 0,
    )
    rows = [
        {
            "action_id": view.action_id,
            "subgroup_normal": view.subgroup_normal,
            "static_legal": True,
            "n": 64,
            "k": 4,
            "support_orbit_bin": index % 8,
            "candidate_sha256": f"{index + 1:064x}",
        }
        for index, view in enumerate(views)
    ]
    seen_nonnormal: set[str] = set()
    for salt in ("policy-a", "policy-b", "policy-c", "policy-d"):
        selected = evaluator._oracle_probe_rows(
            rows,
            limit=8,
            selection_salt=salt,
        )
        assert len(selected) == 8
        assert sum(row["subgroup_normal"] for row in selected) == 1
        assert progressed in {row["action_id"] for row in selected}
        seen_nonnormal.update(
            row["action_id"] for row in selected
            if not row["subgroup_normal"]
        )
    assert len(seen_nonnormal) > 7


def test_evaluator_emits_numeric_metrics_and_stage2_rebuildable_rows(
    tmp_path,
    monkeypatch,
):
    program = tmp_path / "program.json"
    program.write_text(_known_oracle_policy_json())
    candidate_log = (tmp_path / "all_codes.jsonl").resolve()
    monkeypatch.setenv(evaluator.CANDIDATE_LOG_PATH_ENV, str(candidate_log))
    monkeypatch.setenv(evaluator.PREFLIGHT_CONTRACT_ID_ENV, "12345")

    # The full production policy contains the known negative control among
    # 384 rows while the bounded oracle probes only eight. Pin that control
    # into this evidence-path test; probe scheduling has separate coverage.
    rendered = _render_known_oracle_policy()
    control = next(
        candidate for candidate in rendered
        if action_search_view(candidate["action_id"]).subgroup_normal
    )
    control_digest = candidate_digest(control)

    def probe_with_control(
        rows,
        limit=evaluator.MAX_ORACLE_CANDIDATES,
        *,
        selection_salt="",
    ):
        del selection_salt
        if not rows or limit <= 0:
            return []
        target = next(
            row for row in rows
            if row["candidate_sha256"] == control_digest
        )
        # Probe scheduling and quotas have dedicated tests.  Keep this
        # evidence-path integration test bounded to the known fast control.
        return [target]

    monkeypatch.setattr(evaluator, "_oracle_probe_rows", probe_with_control)

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
        int(_v2_catalog_sha256()[:13], 16)
    )
    assert "winner_preflight_lattices" not in metrics
    assert metrics[evaluator.PREFLIGHT_UNIT_KIND_ID_METRIC] == 1.0
    assert metrics[evaluator.PREFLIGHT_UNITS_METRIC] == 46.0
    assert metrics[evaluator.PREFLIGHT_ACTION_STRATA_METRIC] == 46.0
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
            "representation_id",
            "action_id",
            "action_catalog_id",
            "action_catalog_sha256",
            "left_support",
            "right_support",
        }
        assert construction["action_catalog_sha256"] == _v2_catalog_sha256()
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
    program = tmp_path / "program.json"
    program.write_text(_known_oracle_policy_json())
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


def test_oversize_mutation_is_a_managed_worker_error_not_evaluator_failure(
    tmp_path,
    monkeypatch,
):
    program = tmp_path / "oversize-policy.json"
    program.write_bytes(b" " * (policy_dsl.MAX_POLICY_BYTES + 1))
    monkeypatch.setenv(evaluator.PREFLIGHT_CONTRACT_ID_ENV, "12345")

    result = evaluator.evaluate_stage1(str(program))

    assert result.artifacts["failure_stage"] == "mutation_preflight"
    assert result.artifacts["invalid_mutation"] == {
        "reason": "source_too_large",
        "program_sha256": None,
        "program_bytes": policy_dsl.MAX_POLICY_BYTES + 1,
        "detail_sha256": result.artifacts["invalid_mutation"][
            "detail_sha256"
        ],
        "error_type": "CosetPolicyError",
    }
    incomplete = launcher._exact_incomplete_winner_preflight_markers(
        result.metrics,
        expected_contract_id=12345,
        evaluator_kind="coset-two-block",
    )
    assert incomplete is not None


def test_cached_stage2_replays_and_excludes_coset_search_oracle_witness(
    tmp_path,
):
    normal_control = next(
        candidate for candidate in _render_known_oracle_policy()
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
    assert ranked[0]["proof_score"]["status"] == "REJECTED"
    assert ranked[0]["proof_score"]["rejected"] is True


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
from evolve.coset_policy_dsl import parse_policy, render_candidates

row = _static_candidate(render_candidates(parse_policy(
    os.environ["QCODE_TEST_POLICY_JSON"]
))[0])
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
    environment["QCODE_TEST_POLICY_JSON"] = _known_oracle_policy_json()
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

    row = evaluator._static_candidate(_render_known_oracle_policy()[1])
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
    expected = _render_known_oracle_policy()[:2]
    assert {item["action_id"] for item in rows} == {
        candidate["action_id"] for candidate in expected
    }
    assert not wal_path.exists()


def test_coset_evaluator_has_no_decoder_import():
    source = Path(evaluator.__file__).read_text()
    tree = ast.parse(source)
    modules = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    }
    modules.update(
        node.module
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module is not None
    )
    forbidden_modules = {"bposd", "bp_osd", "decoder", "decoders"}
    assert not any(
        set(module.lower().replace("-", "_").split(".")) & forbidden_modules
        for module in modules
    )


def test_coset_config_selects_batch_lane_map_v2():
    config = Config.from_yaml(EVOLUTION_CONFIG)
    assert config.random_seed == 47
    assert config.evaluator.cascade_thresholds[0] > 1.0
    assert config.database.num_islands == 4
    assert config.database.feature_dimensions == list(COSET_FEATURE_DIMENSIONS)
    assert config.database.feature_bins == dict(COSET_FEATURE_BINS)
    assert launcher._coset_search_portfolio_schema_version(
        EVOLUTION_CONFIG
    ) == COSET_MAP_SCHEMA_VERSION
    assert launcher._validated_coset_search_portfolio_config(
        config,
        COSET_MAP_SCHEMA_VERSION,
    ) == 47
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
        COSET_PROOF_LADDER_VERSION_METRIC: float(
            COSET_PROOF_LADDER_SCHEMA_VERSION
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
    with pytest.raises(RuntimeError, match="proof-ladder contract"):
        launcher._checkpoint_evaluator_kind(
            {
                key: value for key, value in coset_metrics.items()
                if key != COSET_PROOF_LADDER_VERSION_METRIC
            },
            expected_kind="coset-two-block",
            label="pre-ladder coset checkpoint",
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
        launcher.ACTION_CATALOG_SHA256_BINDING_FIELD: _v2_catalog_sha256(),
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
