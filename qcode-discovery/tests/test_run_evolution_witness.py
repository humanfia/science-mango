from __future__ import annotations

import asyncio
import copy
import concurrent.futures
import fcntl
import hashlib
import json
import os
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

import evolve.run_evolution as launcher
import humanize.flow as flow_module


@dataclass
class FakeResult:
    child_program_dict: dict[str, Any] | None = None
    iteration: int = 0
    error: str | None = None
    artifacts: dict[str, Any] | None = None


def _write_descriptor_checkpoint(
    tmp_path: Path,
    *,
    extension: str,
) -> tuple[Path, Path]:
    output = tmp_path / "output"
    checkpoint = output / "checkpoints" / "checkpoint_7"
    programs = checkpoint / "programs"
    programs.mkdir(parents=True)
    program_id = "typed-root"
    code = '{"kind":"typed-policy"}\n'
    (checkpoint / "metadata.json").write_text(json.dumps({
        "last_iteration": 7,
        "archive": [program_id],
        "best_program_id": program_id,
        "islands": [[program_id]],
        "island_best_programs": [program_id],
        "island_feature_maps": [{"cell": program_id}],
    }))
    (checkpoint / "best_program_info.json").write_text(json.dumps({
        "id": program_id,
        "current_iteration": 7,
        "language": "json",
    }))
    (programs / f"{program_id}.json").write_text(json.dumps({
        "id": program_id,
        "code": code,
        "metrics": {},
    }))
    (checkpoint / f"best_program{extension}").write_text(code)
    return output, checkpoint


def test_checkpoint_descriptors_accept_json_best_program(tmp_path):
    output, checkpoint = _write_descriptor_checkpoint(
        tmp_path,
        extension=".json",
    )

    launcher_descriptor = launcher._strong_checkpoint_descriptor(
        output,
        checkpoint,
        expected_iteration=7,
    )
    humanize_descriptor = flow_module._checkpoint_descriptor(
        output,
        checkpoint,
        expected_iteration=7,
    )

    assert launcher_descriptor == humanize_descriptor
    assert launcher_descriptor["programs"] == 1


def test_checkpoint_descriptors_reject_ambiguous_best_program_extensions(
    tmp_path,
):
    output, checkpoint = _write_descriptor_checkpoint(
        tmp_path,
        extension=".json",
    )
    (checkpoint / "best_program.py").write_text(
        (checkpoint / "best_program.json").read_text()
    )

    with pytest.raises(RuntimeError, match="exactly one"):
        launcher._strong_checkpoint_descriptor(output, checkpoint)
    with pytest.raises(flow_module.RoundTransactionError, match="exactly one"):
        flow_module._checkpoint_descriptor(output, checkpoint)


def test_checkpoint_descriptors_reject_unknown_best_program_extension(tmp_path):
    output, checkpoint = _write_descriptor_checkpoint(
        tmp_path,
        extension=".txt",
    )

    with pytest.raises(RuntimeError, match="supported language-specific"):
        launcher._strong_checkpoint_descriptor(output, checkpoint)
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="supported language-specific",
    ):
        flow_module._checkpoint_descriptor(output, checkpoint)


def test_parent_and_child_share_managed_evaluator_dependency_contract():
    import evolve.openevolve_evaluator as evaluator

    assert (
        launcher.LOCAL_EVALUATOR_DEPENDENCIES
        == flow_module.LOCAL_EVOLUTION_DEPENDENCIES
    )
    assert "evaluation_final_gate" in launcher.LOCAL_EVALUATOR_DEPENDENCIES
    assert (
        "evaluation_search_contract"
        in launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert (
        "evaluation_structural_features"
        in launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert (
        "evaluation_algebraic_mechanisms"
        in launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert "evaluation_proof_runtime" in (
        launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert "evaluation_distance_sat" in (
        launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert "evaluation_low_weight_oracle" in (
        launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert "evaluation_css_logical_detector" in (
        launcher.LOCAL_EVALUATOR_DEPENDENCIES
    )
    assert (
        launcher.STAGE2_DEEP_LATTICE_COUNT
        == len(evaluator.STAGE2_DEEP_LATTICES)
    )


def test_preflight_contract_is_stable_per_run_and_rotates_with_sink_or_source(
    tmp_path,
):
    dependencies = launcher._evaluator_dependency_identities()
    run_a_log = (tmp_path / "run-a" / "all_codes.jsonl").resolve()
    run_b_log = (tmp_path / "run-b" / "all_codes.jsonl").resolve()

    run_a_first = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=run_a_log,
    )
    run_a_second = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=run_a_log,
    )
    run_b = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=run_b_log,
    )
    upgraded_evaluator = tmp_path / "upgraded-evaluator.py"
    upgraded_evaluator.write_bytes(
        Path(launcher.EVALUATOR).read_bytes()
        + b"\n# simulated evaluator source upgrade\n"
    )
    upgraded = launcher._winner_preflight_contract_id(
        upgraded_evaluator,
        dependencies,
        candidate_log_path=run_a_log,
    )

    assert run_a_first == run_a_second
    assert run_a_first != run_b
    assert run_a_first != upgraded


def test_preflight_contract_rotates_with_css_detector_source(tmp_path):
    dependencies = launcher._evaluator_dependency_identities()
    rotated = {
        name: dict(identity) for name, identity in dependencies.items()
    }
    rotated["evaluation_css_logical_detector"]["sha256"] = "0" * 64
    sink = (tmp_path / "run" / "all_codes.jsonl").resolve()

    original_id = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=sink,
    )
    rotated_id = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        rotated,
        candidate_log_path=sink,
    )

    assert original_id != rotated_id


def test_preflight_contract_rejects_relative_candidate_log_path():
    with pytest.raises(RuntimeError, match="must be absolute"):
        launcher._winner_preflight_contract_id(
            launcher.EVALUATOR,
            launcher._evaluator_dependency_identities(),
            candidate_log_path="relative/all_codes.jsonl",
        )


class FakeFuture:
    def __init__(self, value: Any):
        self.value = value
        self.was_cancelled = False

    def done(self) -> bool:
        return True

    def result(self, *_args: Any, **_kwargs: Any) -> Any:
        if isinstance(self.value, BaseException):
            raise self.value
        return self.value

    def cancel(self) -> bool:
        self.was_cancelled = True
        return True

    def cancelled(self) -> bool:
        return self.was_cancelled


def _child(iteration: int, program_id: str | None = None) -> FakeResult:
    return FakeResult(
        child_program_dict={
            "id": program_id or f"program-{iteration}",
            "code": f"code-{iteration}",
            "metrics": {
                "combined_score": float(iteration),
                **_map_descriptor_metrics(),
            },
            "iteration_found": iteration,
        },
        iteration=iteration,
    )


def _map_descriptor_metrics(
    *,
    pool_size: int = 1,
    dominant_share: float = 1.0,
    pattern_type: int = 0,
    support_split_type: int = 0,
    structural_entropy: float = 0.0,
    algebraic_relation_type: int = 0,
    orbit_span_bin: int = 0,
    difference_spectrum_bin: int = 0,
) -> dict[str, float]:
    return {
        launcher.MAP_DESCRIPTOR_VERSION_METRIC: float(
            launcher.MAP_DESCRIPTOR_VERSION
        ),
        launcher.MAP_DESCRIPTOR_POOL_SIZE_METRIC: float(pool_size),
        launcher.MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC: dominant_share,
        "pattern_type": float(pattern_type),
        launcher.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC:
            float(support_split_type),
        launcher.MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC:
            structural_entropy,
        launcher.MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC:
            float(algebraic_relation_type),
        launcher.MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: float(orbit_span_bin),
        launcher.MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC:
            float(difference_spectrum_bin),
    }


def _portfolio_config() -> SimpleNamespace:
    return SimpleNamespace(
        random_seed=1729,
        prompt=SimpleNamespace(num_top_programs=3),
        database=SimpleNamespace(
            num_islands=5,
            feature_dimensions=list(
                launcher.SEARCH_PORTFOLIO_FEATURE_DIMENSIONS
            ),
            feature_bins=dict(launcher.SEARCH_PORTFOLIO_FEATURE_BINS),
            archive_size=500,
        ),
    )


def test_search_portfolio_config_is_exact_and_rejects_old_shape():
    assert launcher._validated_search_portfolio_config(
        _portfolio_config()
    ) == 1729
    bad = _portfolio_config()
    bad.database.feature_dimensions = [
        "term_count",
        "pattern_type",
    ]
    with pytest.raises(RuntimeError, match="feature_dimensions"):
        launcher._validated_search_portfolio_config(bad)


def test_search_portfolio_requires_explicit_versioned_yaml_marker(tmp_path):
    disabled = tmp_path / "disabled.yaml"
    disabled.write_text("database:\n  num_islands: 5\n")
    assert launcher._search_portfolio_requested(disabled) is False

    enabled = tmp_path / "enabled.yaml"
    enabled.write_text(
        "qcode_search_portfolio:\n"
        "  enabled: true\n"
        "  schema_version: 2\n"
    )
    assert launcher._search_portfolio_requested(enabled) is True

    malformed = tmp_path / "malformed.yaml"
    malformed.write_text(
        "qcode_search_portfolio:\n"
        "  enabled: true\n"
        "  schema_version: 1\n"
    )
    with pytest.raises(RuntimeError, match="marker must be exactly"):
        launcher._search_portfolio_requested(malformed)

    for name, marker in {
        "explicit-null": "null\n",
        "integer-enabled": "enabled: 1\n  schema_version: 2\n",
        "boolean-schema": "enabled: true\n  schema_version: true\n",
    }.items():
        invalid = tmp_path / f"{name}.yaml"
        invalid.write_text("qcode_search_portfolio:\n  " + marker)
        with pytest.raises(RuntimeError, match="marker must be exactly"):
            launcher._search_portfolio_requested(invalid)


def test_adaptive_policy_parses_real_producer_mapping_and_is_deterministic():
    policy = {
        "novel_structure_exploration": 250,
        "repair_x_low_weight": 250,
        "repair_z_low_weight": 250,
        "repair_dual_balance": 250,
    }
    context = (
        "Reviewer diagnosis follows.\n"
        + launcher.ADAPTIVE_MUTATION_POLICY_PREFIX
        + json.dumps(policy, sort_keys=True, separators=(",", ":"))
        + "\nContinue the campaign.\n"
    )
    parsed = launcher._validated_adaptive_mutation_policy(context)
    assert parsed == policy
    first = launcher._adaptive_mutation_tactic(
        parsed, program_code="def generate_candidates(): pass", iteration=41
    )
    second = launcher._adaptive_mutation_tactic(
        parsed, program_code="def generate_candidates(): pass", iteration=41
    )
    assert first == second
    assert first in launcher.ADAPTIVE_MUTATION_TACTICS


@pytest.mark.parametrize(
    "context",
    (
        " QCODE_ADAPTIVE_MUTATION_POLICY_V1={}",
        "QCODE_ADAPTIVE_MUTATION_POLICY_V1={}",
        (
            "QCODE_ADAPTIVE_MUTATION_POLICY_V1={}\n"
            "QCODE_ADAPTIVE_MUTATION_POLICY_V1={}"
        ),
        (
            "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
            '{"novel_structure_exploration":249,'
            '"repair_dual_balance":251,'
            '"repair_x_low_weight":250,'
            '"repair_z_low_weight":250}'
        ),
        (
            "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
            '{"novel_structure_exploration": 250,'
            '"repair_dual_balance":250,'
            '"repair_x_low_weight":250,'
            '"repair_z_low_weight":250}'
        ),
        (
            "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
            '{"novel_structure_exploration":250,'
            '"novel_structure_exploration":250,'
            '"repair_dual_balance":250,'
            '"repair_x_low_weight":250,'
            '"repair_z_low_weight":250}'
        ),
    ),
)
def test_adaptive_policy_bad_block_fails_closed(context):
    with pytest.raises(RuntimeError, match="adaptive mutation policy"):
        launcher._validated_adaptive_mutation_policy(context)


def test_search_regime_marker_and_expand_schedule_are_deterministic():
    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": "expand_required",
        "reason": "trusted_exact_low_distance_with_duplicate_collapse",
        "evidence": {"rounds": [1, 2, 3]},
    }
    encoded = json.dumps(regime, sort_keys=True, separators=(",", ":"))
    assert launcher._validated_search_regime(
        launcher.SEARCH_REGIME_POLICY_PREFIX + encoded
    ) == regime
    schedule = launcher._search_island_schedule(25, "expand_required")
    assert [schedule.count(island) for island in range(5)] == [5, 4, 4, 4, 8]
    assert flow_module._search_island_schedule(25, "expand_required") == schedule
    assert launcher._search_island_schedule(25, "normal") == tuple(
        index % 5 for index in range(25)
    )
    representation_schedule = launcher._search_island_schedule(
        25,
        "representation_change_required",
    )
    assert [
        representation_schedule.count(island) for island in range(5)
    ] == [3, 3, 3, 3, 13]
    assert flow_module._search_island_schedule(
        25,
        "representation_change_required",
    ) == representation_schedule
    assert (
        flow_module.SEARCH_REGIME_DIRECTIVES
        == launcher.SEARCH_REGIME_DIRECTIVES
    )

    representation_regime = {
        "schema_version": 1,
        "status": "representation_change_required",
    }
    encoded = json.dumps(
        representation_regime,
        sort_keys=True,
        separators=(",", ":"),
    )
    with pytest.raises(RuntimeError, match="search regime"):
        launcher._validated_search_regime(
            launcher.SEARCH_REGIME_POLICY_PREFIX + encoded
        )
    assert launcher._validated_search_regime(
        launcher.SEARCH_REGIME_POLICY_V2_PREFIX + encoded
    ) == {**representation_regime, "policy_version": 2}


@pytest.mark.parametrize(
    "status",
    ("normal", "expand_required", "representation_change_required"),
)
def test_policy_v3_flow_marker_drives_identical_launcher_schedule(status):
    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": status,
        "reason": "policy-v3-integration-test",
        "evidence": {"rounds": []},
    }
    encoded = json.dumps(regime, sort_keys=True, separators=(",", ":"))

    assert (
        launcher.SEARCH_REGIME_POLICY_V3_PREFIX
        == flow_module.SEARCH_REGIME_V3_PREFIX
    )
    parsed = launcher._validated_search_regime(
        flow_module.SEARCH_REGIME_V3_PREFIX + encoded
    )

    assert parsed == {**regime, "policy_version": 3}
    assert launcher._search_island_schedule(25, status) == (
        flow_module._search_island_schedule(25, status)
    )


@pytest.mark.parametrize(
    "status",
    ("normal", "expand_required", "representation_change_required"),
)
def test_policy_v4_flow_marker_drives_identical_launcher_schedule(status):
    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": status,
        "reason": "policy-v4-integration-test",
        "evidence": {"rounds": []},
    }
    encoded = json.dumps(regime, sort_keys=True, separators=(",", ":"))

    assert (
        launcher.SEARCH_REGIME_POLICY_V4_PREFIX
        == flow_module.SEARCH_REGIME_V4_PREFIX
    )
    parsed = launcher._validated_search_regime(
        flow_module.SEARCH_REGIME_V4_PREFIX + encoded
    )

    assert parsed == {**regime, "policy_version": 4}
    assert launcher._search_island_schedule(25, status) == (
        flow_module._search_island_schedule(25, status)
    )


@pytest.mark.parametrize(
    "context",
    (
        'prefix QCODE_SEARCH_REGIME_V1={"schema_version":1,"status":"normal"}',
        'QCODE_SEARCH_REGIME_V1={"schema_version":1, "status":"normal"}',
        'QCODE_SEARCH_REGIME_V1={"schema_version":1,"status":"unknown"}',
        (
            'QCODE_SEARCH_REGIME_V1={"schema_version":1,"status":"normal"}\n'
            'QCODE_SEARCH_REGIME_V2={"schema_version":1,"status":"normal"}'
        ),
    ),
)
def test_search_regime_marker_fails_closed(context):
    with pytest.raises(RuntimeError, match="search regime"):
        launcher._validated_search_regime(context)


def test_fixed_portfolio_bins_are_stable_and_v3_is_rejected():
    program = SimpleNamespace(
        id="stable",
        metrics={
            **_map_descriptor_metrics(
                algebraic_relation_type=4,
                support_split_type=4,
                orbit_span_bin=2,
            ),
            "combined_score": 1.0,
        },
    )
    assert launcher._fixed_search_feature_coords(program) == [4, 4, 2]
    program.metrics[launcher.MAP_DESCRIPTOR_VERSION_METRIC] = 3.0
    with pytest.raises(RuntimeError, match="incompatible MAP descriptor"):
        launcher._fixed_search_feature_coords(program)


def test_mechanism_island_admission_categories_match_evaluator_order():
    import evolve.openevolve_evaluator as evaluator

    expected = tuple(
        (index,) for index, _name in enumerate(evaluator.RELATION_TYPES)
    )
    assert launcher.SEARCH_PORTFOLIO_RELATION_CATEGORIES == expected


def test_real_ansatz_seed_bootstraps_into_its_mechanism_island():
    import evolve.openevolve_evaluator as evaluator
    import evolve.seed_solution_ansatz as seed

    rows = []
    for ell, m in evaluator.STAGE2_FITNESS_LATTICES:
        rows.extend(
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
            }
            for a_terms, b_terms in seed.generate_candidates(ell, m)
        )
    metrics = evaluator._pool_map_descriptor(
        rows,
        lattices=set(evaluator.STAGE2_FITNESS_LATTICES),
    )
    assert metrics[launcher.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC] == 5.0
    root = SimpleNamespace(
        id="real-ansatz-seed",
        code=Path(seed.__file__).read_text(),
        parent_id=None,
        metrics={"combined_score": 0.0, **metrics},
        metadata={"island": 0},
    )
    database = SimpleNamespace(
        programs={root.id: root},
        islands=[{root.id}, set(), set(), set(), set()],
        island_feature_maps=[{} for _ in range(5)],
        archive=set(),
        feature_stats={},
        feature_bins_per_dim={},
        island_best_programs=[None] * 5,
        best_program_id=None,
        config=SimpleNamespace(archive_size=180),
    )

    launcher._rebuild_fixed_search_feature_maps(database)

    expected_island = int(
        metrics[launcher.MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC]
    )
    assert root.metadata["island"] == expected_island
    assert database.islands == [
        {root.id} if island == expected_island else set()
        for island in range(launcher.SEARCH_PORTFOLIO_ISLAND_COUNT)
    ]
    assert launcher._search_elite_ids(database, 0) == [root.id]


@pytest.mark.parametrize(
    ("metric", "value"),
    (
        (launcher.MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC, True),
        (launcher.MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC, 5),
        (launcher.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC, -1),
        (launcher.MAP_DESCRIPTOR_ORBIT_SPAN_METRIC, float("nan")),
        (launcher.MAP_DESCRIPTOR_ORBIT_SPAN_METRIC, 3),
    ),
)
def test_fixed_portfolio_bins_reject_invalid_coordinates(metric, value):
    program = SimpleNamespace(
        id="invalid-coordinate",
        metrics={
            "combined_score": 1.0,
            **_map_descriptor_metrics(),
        },
    )
    program.metrics[metric] = value
    with pytest.raises(RuntimeError, match="search portfolio"):
        launcher._fixed_search_feature_coords(program)


def test_rebuilt_map_keeps_lineage_children_and_prefers_relation_parents():
    def program(
        program_id: str,
        score: float,
        *,
        pattern: int,
        support_split_type: int = 0,
        algebraic_relation_type: int = 0,
        island: int = 0,
    ) -> SimpleNamespace:
        return SimpleNamespace(
            id=program_id,
            code=f"code-{program_id}",
            parent_id="existing-parent",
            metrics={
                "combined_score": score,
                **_map_descriptor_metrics(
                    pattern_type=pattern,
                    support_split_type=support_split_type,
                    structural_entropy=0.3,
                    algebraic_relation_type=algebraic_relation_type,
                    orbit_span_bin=0 if pattern < 3 else 2,
                ),
            },
            metadata={"island": island},
        )

    programs = {
        "a": program("a", 3.0, pattern=1),
        "b": program("b", 2.0, pattern=1),
        "c": program("c", 1.0, pattern=4),
        # A mechanism-changing child remains part of the lineage island.  It
        # is a MAP elite, but matching affine parents are preferred for the
        # next affine mutation.
        "off-role": program(
            "off-role",
            100.0,
            pattern=5,
            support_split_type=2,
            algebraic_relation_type=1,
        ),
        # Island 3 has no local history.  Its cold-start fallback should find
        # a matching relation-3 elite in another lineage before using the
        # unrestricted global archive.
        "global-role-3": program(
            "global-role-3",
            4.0,
            pattern=2,
            algebraic_relation_type=3,
            island=1,
        ),
        # ProgramDatabase stores a failed novelty insertion in ``programs``
        # before returning, but does not put it in an island.  Rebuild must
        # not promote that rejected row merely because its score is high.
        "rejected": program("rejected", 99.0, pattern=5),
    }
    database = SimpleNamespace(
        programs=programs,
        islands=[
            {"a", "b", "c", "off-role"},
            {"global-role-3"},
            set(),
            set(),
            set(),
        ],
        island_feature_maps=[{} for _ in range(5)],
        archive=set(),
        feature_stats={"moving": {"min": 0}},
        feature_bins_per_dim={},
        island_best_programs=[None] * 5,
        best_program_id=None,
    )
    program_payloads = {
        program_id: json.dumps(
            vars(program_value),
            sort_keys=True,
            separators=(",", ":"),
        )
        for program_id, program_value in programs.items()
    }
    launcher._rebuild_fixed_search_feature_maps(database)
    assert database.islands[0] == {"a", "c", "off-role"}
    assert database.islands[1] == {"global-role-3"}
    assert "b" not in database.archive
    assert "off-role" in database.archive
    assert "rejected" not in database.archive
    assert database.best_program_id == "off-role"
    assert launcher._search_elite_ids(database, 0) == ["a", "c"]
    assert launcher._search_elite_ids(database, 1) == ["global-role-3"]
    assert launcher._search_elite_ids(database, 3) == ["global-role-3"]
    assert database.feature_stats == {}
    first_maps = json.loads(json.dumps(database.island_feature_maps))
    launcher._rebuild_fixed_search_feature_maps(database)
    assert database.island_feature_maps == first_maps
    assert set(database.programs) == set(programs)
    assert {
        program_id: json.dumps(
            vars(program_value),
            sort_keys=True,
            separators=(",", ":"),
        )
        for program_id, program_value in database.programs.items()
    } == program_payloads


def test_cover_seed_descriptors_submit_and_rebuild_all_five_lineage_islands():
    import evolve.openevolve_evaluator as evaluator
    import evolve.seed_solution_cover_algebra as seed
    from evaluation.algebraic_mechanisms import classify_algebraic_mechanism

    ell, m = 12, 6
    grouped_rows: dict[int, list[dict[str, Any]]] = {
        island: []
        for island in range(launcher.SEARCH_PORTFOLIO_ISLAND_COUNT)
    }
    all_rows: list[dict[str, Any]] = []
    for a_terms, b_terms in seed.generate_candidates(ell, m):
        row = {
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
        }
        relation_name = classify_algebraic_mechanism(
            a_terms,
            b_terms,
            ell=ell,
            m=m,
        )["relation_type"]
        relation = evaluator.RELATION_TYPES.index(relation_name)
        grouped_rows[relation].append(row)
        all_rows.append(row)

    assert all(grouped_rows.values())
    root_metrics = evaluator._pool_map_descriptor(
        all_rows,
        lattices={(ell, m)},
    )
    root = SimpleNamespace(
        id="cover-seed-root",
        code=Path(seed.__file__).read_text(),
        parent_id=None,
        metrics={"combined_score": 0.0, **root_metrics},
        metadata={"island": 0},
    )
    programs = {root.id: root}
    islands = [{root.id}, set(), set(), set(), set()]
    for island, rows in grouped_rows.items():
        metrics = evaluator._pool_map_descriptor(
            rows,
            lattices={(ell, m)},
        )
        assert int(
            metrics[launcher.MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC]
        ) == island
        child_id = f"cover-child-{island}"
        programs[child_id] = SimpleNamespace(
            id=child_id,
            code=f"cover-generator-{island}",
            parent_id=root.id,
            metrics={"combined_score": float(island + 1), **metrics},
            # This is the effective scheduler target recorded by
            # ProgramDatabase.add after a submission.
            metadata={"island": island},
        )
        islands[island].add(child_id)

    database = SimpleNamespace(
        programs=programs,
        islands=islands,
        island_feature_maps=[{} for _ in range(5)],
        archive=set(),
        feature_stats={},
        feature_bins_per_dim={},
        island_best_programs=[None] * 5,
        best_program_id=None,
        config=SimpleNamespace(archive_size=500),
    )

    launcher._rebuild_fixed_search_feature_maps(database)

    for island in range(launcher.SEARCH_PORTFOLIO_ISLAND_COUNT):
        child_id = f"cover-child-{island}"
        assert child_id in database.islands[island]
        assert child_id in set(
            database.island_feature_maps[island].values()
        )
        assert launcher._search_elite_ids(database, island)


def test_portfolio_observer_records_out_of_range_iteration_without_indexing_role():
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.search_policy_sha256 = launcher._adaptive_mutation_policy_sha256(
        dict(launcher.DEFAULT_ADAPTIVE_MUTATION_POLICY)
    )
    observer.begin(1, 1, None)

    result = observer.record_submission(
        2,
        0,
        None,
        search_role=launcher.SEARCH_PORTFOLIO_ROLES[0],
        search_tactic=launcher.ADAPTIVE_MUTATION_TACTICS[0],
        search_parent_program_id="parent",
        search_parent_code_sha256="a" * 64,
    )

    assert result is None
    assert any(
        "outside the scheduled slice" in violation
        for violation in observer.violations
    )


def test_observer_enforces_twenty_five_submission_portfolio_quota():
    observer = launcher._SliceObserver(0, 25, FakeResult)
    policy = dict(launcher.DEFAULT_ADAPTIVE_MUTATION_POLICY)
    observer.search_policy_sha256 = (
        launcher._adaptive_mutation_policy_sha256(policy)
    )
    observer.begin(1, 25, None)
    programs = {}
    tactic = launcher.ADAPTIVE_MUTATION_TACTICS[0]
    for iteration in range(1, 26):
        island = (iteration - 1) % 5
        future = observer.record_submission(
            iteration,
            island,
            FakeFuture(_child(iteration)),
            search_role=launcher.SEARCH_PORTFOLIO_ROLES[island],
            search_tactic=tactic,
            search_parent_program_id=f"parent-{iteration}",
            search_parent_code_sha256=hashlib.sha256(
                f"parent-{iteration}".encode()
            ).hexdigest(),
        )
        result = future.result()
        program_id = result.child_program_dict["id"]
        programs[program_id] = SimpleNamespace(
            **result.child_program_dict
        )
        observer.record_program_add(iteration, programs[program_id])
    observer.verify(_observer_controller(programs))
    assert observer.search_role_submission_counts == {
        role: 5 for role in launcher.SEARCH_PORTFOLIO_ROLES
    }
    assert observer.submission_attempts[0][
        "search_role_submission_counts"
    ] == {role: 5 for role in launcher.SEARCH_PORTFOLIO_ROLES}


class FakePortfolioDatabase:
    def __init__(self):
        seed = SimpleNamespace(
            id="portfolio-seed",
            code="def generate_candidates(): return []",
            parent_id=None,
            generation=0,
            metrics={
                "combined_score": 0.0,
                **_map_descriptor_metrics(),
            },
            iteration_found=0,
            metadata={"island": 0, "origin": "seed"},
        )
        self.programs = {seed.id: seed}
        self.islands = [{seed.id}, set(), set(), set(), set()]
        self.island_feature_maps = [{} for _ in range(5)]
        self.archive: set[str] = set()
        self.feature_stats: dict[str, Any] = {}
        self.feature_bins_per_dim: dict[str, int] = {}
        self.island_best_programs: list[str | None] = [None] * 5
        self.best_program_id: str | None = None
        self.config = SimpleNamespace(archive_size=500)
        self.artifacts = {
            seed.id: {"seed_artifact": {"preserved": True}},
        }
        self.add_order: list[int] = []
        self.drop_seed_on_first_add = False

    def get_artifacts(self, program_id: str) -> dict[str, Any]:
        return self.artifacts.get(program_id, {})

    def add(
        self,
        program: Any,
        iteration: int | None = None,
        target_island: int | None = None,
    ) -> str:
        assert iteration is not None
        assert target_island is not None
        program.iteration_found = iteration
        # Pinned OpenEvolve records the effective target in metadata.  In the
        # success case this is an idempotent assignment; in the adversarial
        # case it exposes a worker/scheduler disagreement to the observer's
        # byte-for-byte check.
        program.metadata["island"] = target_island
        self.programs[program.id] = program
        self.islands[target_island].add(program.id)
        self.add_order.append(iteration)
        if self.drop_seed_on_first_add and len(self.add_order) == 1:
            self.programs.pop("portfolio-seed")
            for island in self.islands:
                island.discard("portfolio-seed")
            self.artifacts.pop("portfolio-seed", None)
        return program.id


class FakePortfolioExecutor:
    def __init__(self):
        self.calls: list[tuple[Any, tuple[Any, ...]]] = []

    def submit(self, function: Any, *args: Any) -> FakeFuture:
        self.calls.append((function, args))
        return FakeFuture(function(*args))


class FakePortfolioParallelController:
    sequential = False

    def __init__(self, database: FakePortfolioDatabase, config: Any):
        self.database = database
        self.config = config
        self.executor = FakePortfolioExecutor()
        self.num_islands = 5
        self.shutdown_event = threading.Event()
        self.early_stopping_triggered = False

    def request_shutdown(self) -> None:
        self.shutdown_event.set()

    def _create_database_snapshot(self) -> dict[str, Any]:
        # JSON round-tripping is intentional: a real process snapshot owns
        # its values.  If the adapter accidentally mutates the main seed while
        # rebinding an empty island, the assertion below will catch it.
        programs = {
            program_id: json.loads(json.dumps(vars(program)))
            for program_id, program in self.database.programs.items()
        }
        snapshot_ids = list(self.database.programs)[:100]
        artifacts = json.loads(json.dumps({
            program_id: self.database.artifacts[program_id]
            for program_id in snapshot_ids
            if program_id in self.database.artifacts
        }))
        return {
            "programs": programs,
            "artifacts": artifacts,
            "islands": [
                sorted(program_ids)
                for program_ids in self.database.islands
            ],
            "current_island": 0,
            "sampling_island": 0,
            "feature_dimensions": list(
                self.config.database.feature_dimensions
            ),
        }

    async def run_evolution(
        self,
        start_iteration: int,
        max_iterations: int,
        target_score: float | None = None,
        checkpoint_callback: Any = None,
    ) -> None:
        del target_score
        end_iteration = start_iteration + max_iterations - 1
        if self.sequential:
            for iteration in range(start_iteration, end_iteration + 1):
                future = self._submit_iteration(iteration, 0)
                result = future.result()
                child = SimpleNamespace(**result.child_program_dict)
                self.database.add(child, iteration=iteration)
            checkpoint_callback(end_iteration)
            return
        futures = [
            (iteration, self._submit_iteration(iteration, 0))
            for iteration in range(start_iteration, end_iteration + 1)
        ]
        checkpoint_callback(start_iteration)
        # Deliberately integrate in reverse completion order.  The portfolio
        # lane must remain a pure function of the iteration, not whichever
        # worker happens to finish first.
        for iteration, future in reversed(futures):
            result = future.result()
            child = SimpleNamespace(**result.child_program_dict)
            self.database.add(child, iteration=iteration)
        checkpoint_callback(end_iteration)


class FakePortfolioOpenEvolve:
    def __init__(self):
        self.output_dir = "/fake-portfolio-output"
        self.saved: list[int] = []

    def _save_checkpoint(self, iteration: int) -> None:
        self.saved.append(iteration)


def _install_fake_portfolio_sources(
    monkeypatch: pytest.MonkeyPatch,
    *,
    wrong_worker_island: bool,
) -> tuple[Any, dict[str, Any]]:
    worker_state: dict[str, Any] = {
        "rows": {},
        "snapshots": {},
        "wrong_worker_island": wrong_worker_island,
    }

    def run_worker(
        iteration: int,
        snapshot: dict[str, Any],
        parent_id: str,
        inspiration_ids: list[str],
    ) -> FakeResult:
        del inspiration_ids
        parent = snapshot["programs"][parent_id]
        target_island = parent["metadata"]["island"]
        artifact = snapshot["artifacts"][parent_id][
            launcher.SEARCH_PORTFOLIO_ARTIFACT_KEY
        ]
        child_island = target_island
        if worker_state["wrong_worker_island"]:
            child_island = (target_island + 1) % 5
        child = {
            "id": f"portfolio-child-{iteration}",
            "code": f"portfolio-code-{iteration}",
            "parent_id": parent_id,
            "generation": 1,
            "metrics": {
                "combined_score": float(iteration + 10),
                **_map_descriptor_metrics(
                    support_split_type=(0, 1, 5, 3, 0)[target_island],
                    algebraic_relation_type=target_island,
                ),
            },
            "iteration_found": iteration,
            "metadata": {
                "changes": "fake portfolio mutation",
                "island": child_island,
            },
        }
        worker_state["rows"][iteration] = json.loads(json.dumps(child))
        worker_state["snapshots"][iteration] = {
            "parent_id": parent_id,
            "parent_metadata": json.loads(json.dumps(parent["metadata"])),
            "parent_artifacts": json.loads(json.dumps(
                snapshot["artifacts"][parent_id]
            )),
            "portfolio_artifact": json.loads(json.dumps(artifact)),
        }
        return FakeResult(child_program_dict=child, iteration=iteration)

    controller_module = SimpleNamespace(
        ProcessParallelController=FakePortfolioParallelController,
        OpenEvolve=FakePortfolioOpenEvolve,
    )
    process_module = SimpleNamespace(
        SerializableResult=FakeResult,
        _run_iteration_worker=run_worker,
    )
    monkeypatch.setattr(
        launcher,
        "_openevolve_source_binding",
        lambda: (
            {
                "controller": {
                    "path": "/fake/portfolio-controller.py",
                    "sha256": "b" * 64,
                    "bytes": 1,
                },
            },
            controller_module,
            process_module,
        ),
    )
    monkeypatch.setattr(
        launcher,
        "_strong_checkpoint_descriptor",
        lambda _output, _checkpoint, expected_iteration=None: {
            "path": (
                "/fake-portfolio-output/checkpoints/"
                f"checkpoint_{expected_iteration}"
            ),
            "last_iteration": expected_iteration,
            "sha256": f"{expected_iteration:064x}",
            "programs": expected_iteration + 1,
        },
    )
    return controller_module, worker_state


def test_verified_controller_portfolio_rebinds_snapshot_and_integrates_five_islands(
    monkeypatch,
):
    controller_module, worker_state = _install_fake_portfolio_sources(
        monkeypatch,
        wrong_worker_island=False,
    )
    config = _portfolio_config()
    database = FakePortfolioDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(
        0,
        5,
        search_config=config,
    ) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(
            database,
            config,
        )
        asyncio.run(
            parallel.run_evolution(
                1,
                5,
                None,
                checkpoint_callback=open_evolve._save_checkpoint,
            )
        )

        assert database.add_order == [5, 4, 3, 2, 1]
        assert [
            attempt["island_id"]
            for attempt in observer.submission_attempts
        ] == [0, 1, 2, 3, 4]
        assert database.programs["portfolio-seed"].metadata == {
            "island": 0,
            "origin": "seed",
        }
        for iteration, island in enumerate(range(5), start=1):
            child_id = f"portfolio-child-{iteration}"
            assert child_id in database.islands[island]
            snapshot = worker_state["snapshots"][iteration]
            assert snapshot["parent_metadata"] == {
                "island": island,
                "origin": "seed",
            }
            artifact = snapshot["portfolio_artifact"]
            assert artifact["island_id"] == island
            assert (
                artifact["island_role"]
                == launcher.SEARCH_PORTFOLIO_ROLES[island]
            )
            assert (
                artifact["island_directive"]
                == launcher.SEARCH_PORTFOLIO_DIRECTIVES[island]
            )
            assert artifact["support_split_targets"] == [
                list(split)
                for split in launcher.SEARCH_PORTFOLIO_SUPPORT_TARGETS[
                    island
                ]
            ]
            assert artifact["search_regime"] == {
                "schema_version": 1,
                "status": "normal",
            }
            assert artifact["search_regime_directive"] == (
                launcher.SEARCH_REGIME_DIRECTIVES["normal"]
            )
            assert (
                artifact["adaptive_mutation_tactic"]
                in launcher.ADAPTIVE_MUTATION_TACTICS
            )
            assert artifact["adaptive_mutation_directive"] == (
                launcher.ADAPTIVE_MUTATION_DIRECTIVES[
                    artifact["adaptive_mutation_tactic"]
                ]
            )
            worker_bytes = json.dumps(
                worker_state["rows"][iteration],
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode()
            stored_bytes = json.dumps(
                vars(database.programs[child_id]),
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode()
            assert stored_bytes == worker_bytes
        assert observer.accounting_complete is True

    assert open_evolve.saved == [5]


def test_selectable_elite_artifacts_bypass_generic_snapshot_first_100_cap(
    monkeypatch,
):
    controller_module, worker_state = _install_fake_portfolio_sources(
        monkeypatch,
        wrong_worker_island=False,
    )
    config = _portfolio_config()
    database = FakePortfolioDatabase()
    seed = database.programs["portfolio-seed"]
    decoys = {
        f"decoy-{index:03d}": SimpleNamespace(
            id=f"decoy-{index:03d}",
            code=f"decoy-code-{index}",
            parent_id=None,
            generation=0,
            metrics={"combined_score": -1.0},
            iteration_found=0,
            metadata={"island": 0},
        )
        for index in range(100)
    }
    database.programs = {**decoys, seed.id: seed}
    database.artifacts = {
        **{
            program_id: {"decoy": True}
            for program_id in decoys
        },
        seed.id: {
            "low_weight_oracle_failures": (
                "X-logical w=2 support=[1, 40]"
            ),
        },
    }
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(
        0,
        5,
        search_config=config,
    ):
        parallel = controller_module.ProcessParallelController(database, config)
        asyncio.run(parallel.run_evolution(
            1,
            5,
            None,
            checkpoint_callback=open_evolve._save_checkpoint,
        ))

    for snapshot in worker_state["snapshots"].values():
        assert snapshot["parent_artifacts"][
            "low_weight_oracle_failures"
        ] == "X-logical w=2 support=[1, 40]"


def test_representation_regime_forces_directive_into_every_portfolio_artifact(
    monkeypatch,
):
    controller_module, worker_state = _install_fake_portfolio_sources(
        monkeypatch,
        wrong_worker_island=False,
    )
    config = _portfolio_config()
    database = FakePortfolioDatabase()
    open_evolve = controller_module.OpenEvolve()
    regime = {
        "schema_version": 1,
        "status": "representation_change_required",
        "policy_version": 2,
    }

    with launcher._verified_slice_controller(
        0,
        5,
        search_config=config,
        search_regime=regime,
    ):
        parallel = controller_module.ProcessParallelController(
            database,
            config,
        )
        asyncio.run(
            parallel.run_evolution(
                1,
                5,
                None,
                checkpoint_callback=open_evolve._save_checkpoint,
            )
        )

    assert len(worker_state["snapshots"]) == 5
    expected_directive = launcher.SEARCH_REGIME_DIRECTIVES[
        "representation_change_required"
    ]
    for snapshot in worker_state["snapshots"].values():
        artifact = snapshot["portfolio_artifact"]
        assert artifact["search_regime"] == regime
        assert artifact["search_regime_directive"] == expected_directive
        assert (
            artifact["search_regime_directive"]
            == flow_module.SEARCH_REGIME_DIRECTIVES[
                "representation_change_required"
            ]
        )


def test_verified_controller_freezes_parent_archive_for_completion_order(
    monkeypatch,
):
    controller_module, worker_state = _install_fake_portfolio_sources(
        monkeypatch,
        wrong_worker_island=False,
    )
    config = _portfolio_config()
    database = FakePortfolioDatabase()
    database.drop_seed_on_first_add = True
    open_evolve = controller_module.OpenEvolve()
    FakePortfolioParallelController.sequential = True
    try:
        with launcher._verified_slice_controller(
            0,
            5,
            search_config=config,
        ):
            parallel = controller_module.ProcessParallelController(
                database,
                config,
            )
            asyncio.run(
                parallel.run_evolution(
                    1,
                    5,
                    None,
                    checkpoint_callback=open_evolve._save_checkpoint,
                )
            )
    finally:
        FakePortfolioParallelController.sequential = False

    assert {
        snapshot["parent_id"]
        for snapshot in worker_state["snapshots"].values()
    } == {"portfolio-seed"}
    assert "portfolio-seed" not in database.programs
    assert open_evolve.saved == [5]


def test_verified_controller_portfolio_rejects_wrong_worker_island(
    monkeypatch,
):
    controller_module, _worker_state = _install_fake_portfolio_sources(
        monkeypatch,
        wrong_worker_island=True,
    )
    config = _portfolio_config()
    database = FakePortfolioDatabase()
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(
        RuntimeError,
        match="changed worker island content",
    ):
        with launcher._verified_slice_controller(
            0,
            1,
            search_config=config,
        ):
            parallel = controller_module.ProcessParallelController(
                database,
                config,
            )
            asyncio.run(
                parallel.run_evolution(
                    1,
                    1,
                    None,
                    checkpoint_callback=open_evolve._save_checkpoint,
                )
            )
    assert open_evolve.saved == []


def _preflight_markers(
    contract_id: int,
    *,
    evaluated: int = 3,
    eligible: int = 2,
) -> dict[str, float]:
    return {
        launcher.WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            launcher.WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        launcher.WINNER_PREFLIGHT_CONTRACT_ID_METRIC: float(contract_id),
        launcher.WINNER_PREFLIGHT_COMPLETE_METRIC: 1.0,
        launcher.WINNER_PREFLIGHT_INCOMPLETE_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_LATTICES_METRIC: float(
            len(launcher.EVOLUTION_LATTICES)
        ),
        launcher.WINNER_PREFLIGHT_EVALUATED_METRIC: float(evaluated),
        launcher.WINNER_PREFLIGHT_ELIGIBLE_METRIC: float(eligible),
        launcher.WINNER_PREFLIGHT_PERSISTED_METRIC: float(eligible),
        launcher.WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 0.0,
    }


def _incomplete_preflight_metrics(
    contract_id: int,
    *,
    hard_timeout: int = 0,
) -> dict[str, Any]:
    return {
        "combined_score": 0.0,
        "error": "winner preflight failed",
        "lattices_with_high_k": 0.0,
        "num_high_k": 0.0,
        "term_count": 0.0,
        "pattern_type": 0.0,
        **_map_descriptor_metrics(pool_size=0, dominant_share=0.0),
        **{
            launcher.WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
                launcher.WINNER_PREFLIGHT_CONTRACT_VERSION
            ),
            launcher.WINNER_PREFLIGHT_CONTRACT_ID_METRIC:
                float(contract_id),
            launcher.WINNER_PREFLIGHT_COMPLETE_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_INCOMPLETE_METRIC: 1.0,
            launcher.WINNER_PREFLIGHT_LATTICES_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_EVALUATED_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_ELIGIBLE_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_PERSISTED_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
            launcher.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC:
                float(hard_timeout),
            launcher.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 1.0,
        },
    }


def _coset_preflight_markers(
    contract_id: int,
    *,
    evaluated: int = 3,
    eligible: int = 2,
) -> dict[str, float]:
    action_strata = launcher._coset_action_strata_count()
    return {
        launcher.WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            launcher.WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        launcher.WINNER_PREFLIGHT_CONTRACT_ID_METRIC: float(contract_id),
        launcher.WINNER_PREFLIGHT_COMPLETE_METRIC: 1.0,
        launcher.WINNER_PREFLIGHT_INCOMPLETE_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC: float(
            launcher.WINNER_PREFLIGHT_UNIT_KIND_ACTION_STRATA
        ),
        launcher.WINNER_PREFLIGHT_UNITS_METRIC: float(action_strata),
        launcher.WINNER_PREFLIGHT_ACTION_STRATA_METRIC: float(action_strata),
        launcher.WINNER_PREFLIGHT_EVALUATED_METRIC: float(evaluated),
        launcher.WINNER_PREFLIGHT_ELIGIBLE_METRIC: float(eligible),
        launcher.WINNER_PREFLIGHT_PERSISTED_METRIC: float(eligible),
        launcher.WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 0.0,
    }


def _outer_stage1_exception_artifacts(
    *,
    error_type: str = "NameError",
    message: str = "name 'seeded_anchors' is not defined",
    provenance_frames: list[dict[str, str]] | None = None,
) -> dict[str, Any]:
    program_path = Path(launcher.tempfile.gettempdir()) / "tmpqcode-mutant.py"
    final_error = error_type if not message else f"{error_type}: {message}"
    if provenance_frames is None:
        provenance_frames = [
            {
                "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                "function": "evaluate_stage1",
            },
            {
                "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                "function": "_evaluate",
            },
            {
                "path": str(program_path),
                "function": "generate_candidates",
            },
        ]
    return {
        "failure_stage": "stage1",
        "error_type": error_type,
        "error_message": message,
        "stderr": message,
        "traceback": (
            "Traceback (most recent call last):\n"
            f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
            "in _evaluate\n"
            "    raw = generator()\n"
            f'  File "{program_path}", line 2, in generate_candidates\n'
            "    return seeded_anchors\n"
            f"{final_error}"
        ),
        "timestamp": time.time(),
        "cascade_config": True,
        "cascade_thresholds": [2.0, 2.0],
        "timeout_config": 7200.0,
        "evaluation_file": launcher.EVALUATOR_COSET_TWO_BLOCK,
        launcher.STAGE1_EXCEPTION_PROVENANCE_FIELD: {
            "schema_version": (
                launcher.STAGE1_EXCEPTION_PROVENANCE_SCHEMA_VERSION
            ),
            "stage": "stage1",
            "frames": provenance_frames,
        },
    }


def _stage2_failure_metrics(
    contract_id: int,
    *,
    completed_lattices: int = 4,
    hard_timeout: int = 1,
) -> dict[str, Any]:
    return {
        "combined_score": 0.25,
        **_map_descriptor_metrics(
            pattern_type=2,
            support_split_type=3,
            structural_entropy=0.5,
        ),
        **_preflight_markers(contract_id),
        launcher.STAGE2_CONTRACT_VERSION_METRIC: float(
            launcher.STAGE2_DEEP_CONTRACT_VERSION
        ),
        launcher.STAGE2_CONTRACT_ID_METRIC: float(contract_id),
        launcher.STAGE2_COMPLETE_METRIC: 0.0,
        launcher.STAGE2_INCOMPLETE_METRIC: 1.0,
        launcher.STAGE2_LATTICES_METRIC: float(completed_lattices),
        launcher.STAGE2_HARD_TIMEOUT_METRIC: float(hard_timeout),
        launcher.STAGE2_SUBPROCESS_FAILED_METRIC: 1.0,
    }


def _observer_controller(
    programs: dict[str, Any],
    *,
    shutdown: bool = False,
    early_stop: bool = False,
) -> Any:
    event = threading.Event()
    if shutdown:
        event.set()
    return SimpleNamespace(
        shutdown_event=event,
        early_stopping_triggered=early_stop,
        database=SimpleNamespace(programs=programs),
    )


def test_observer_accepts_out_of_order_results_and_worker_error():
    observer = launcher._SliceObserver(10, 3, FakeResult)
    observer.begin(11, 3, None)
    futures = {
        iteration: observer.record_submission(
            iteration,
            iteration % 2,
            FakeFuture(
                FakeResult(iteration=iteration, error="worker failed")
                if iteration == 12
                else _child(iteration)
            ),
        )
        for iteration in (11, 12, 13)
    }
    programs: dict[str, Any] = {}
    for iteration in (13, 11, 12):
        result = futures[iteration].result()
        if result.child_program_dict is not None:
            program_id = result.child_program_dict["id"]
            programs[program_id] = SimpleNamespace(**result.child_program_dict)
            observer.record_program_add(iteration, programs[program_id])
    programs.clear()

    observer.verify(_observer_controller(programs))

    assert observer.accounting_complete is True
    assert sorted(observer.outcomes) == [11, 12, 13]
    assert observer.outcomes[12]["status"] == "worker_error"


def test_incomplete_child_preflight_cannot_complete_slice_or_witness():
    contract_id = 12345
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(1, 1, None)
    child = _child(1)
    child.child_program_dict["metrics"] = {
        **_preflight_markers(contract_id),
        launcher.WINNER_PREFLIGHT_COMPLETE_METRIC: 0.0,
        launcher.WINNER_PREFLIGHT_INCOMPLETE_METRIC: 1.0,
        launcher.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: 1.0,
        launcher.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 1.0,
    }
    future = observer.record_submission(1, 0, FakeFuture(child))
    result = future.result()
    program = SimpleNamespace(**result.child_program_dict)
    observer.record_program_add(1, program)

    with pytest.raises(
        RuntimeError,
        match="incomplete winner preflight",
    ):
        observer.verify(
            _observer_controller({program.id: program})
        )
    assert observer.accounting_complete is False


@pytest.mark.parametrize("hard_timeout", (0, 1))
def test_exact_incomplete_child_becomes_canonical_worker_error(
    hard_timeout: int,
):
    contract_id = 12345
    observer = launcher._SliceObserver(
        10,
        3,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(11, 3, None)
    raw_results = {
        iteration: _child(iteration)
        for iteration in (11, 12, 13)
    }
    for iteration in (11, 13):
        raw_results[iteration].child_program_dict["metrics"].update(
            _preflight_markers(contract_id)
        )
    raw_results[12].child_program_dict["metrics"] = (
        _incomplete_preflight_metrics(
            contract_id,
            hard_timeout=hard_timeout,
        )
    )
    futures = {
        iteration: observer.record_submission(
            iteration,
            iteration % 2,
            FakeFuture(raw_results[iteration]),
        )
        for iteration in (11, 12, 13)
    }
    programs: dict[str, Any] = {}
    for iteration in (13, 12, 11):
        result = futures[iteration].result()
        if result.error is not None:
            assert iteration == 12
            assert result.child_program_dict is None
            failure = json.loads(result.error)
            assert failure["kind"] == "winner_preflight_incomplete"
            assert failure["hard_timeout"] == hard_timeout
            assert failure["program_id"] == "program-12"
            continue
        program = SimpleNamespace(**result.child_program_dict)
        programs[program.id] = program
        observer.record_program_add(iteration, program)

    observer.verify(_observer_controller(programs))

    assert observer.accounting_complete is True
    assert observer.outcomes[12]["status"] == "worker_error"
    assert 12 not in observer.expected_programs
    assert set(programs) == {"program-11", "program-13"}


def test_all_authenticated_bad_dsl_mutations_complete_the_slice(monkeypatch):
    from evolve import coset_openevolve_evaluator as coset_evaluator
    from evolve.coset_mutation_preflight import InvalidCosetMutation

    contract_id = 12345
    monkeypatch.setenv(
        coset_evaluator.PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    evaluated = coset_evaluator._invalid_mutation_result(
        InvalidCosetMutation(
            "dsl_invalid",
            program_sha256="a" * 64,
            program_bytes=17,
            detail_sha256="b" * 64,
        )
    )
    observer = launcher._SliceObserver(
        0,
        3,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        evaluator_kind=launcher.EVALUATOR_KIND_COSET_TWO_BLOCK,
    )
    observer.begin(1, 3, None)
    for iteration in observer.expected_iterations:
        child = _child(iteration)
        child.child_program_dict["metrics"] = dict(evaluated.metrics)
        child.artifacts = dict(evaluated.artifacts)
        result = observer.record_submission(
            iteration,
            0,
            FakeFuture(child),
        ).result()
        assert result.child_program_dict is None

    observer.verify(_observer_controller({}))

    assert observer.accounting_complete is True
    assert all(
        outcome == {
            "iteration": iteration,
            "status": "worker_error",
            "error_sha256": outcome["error_sha256"],
            "error_bytes": outcome["error_bytes"],
            "error_kind": "invalid_mutation",
        }
        for iteration, outcome in observer.outcomes.items()
    )


def test_all_unclassified_worker_errors_still_fail_the_slice():
    observer = launcher._SliceObserver(0, 2, FakeResult)
    observer.begin(1, 2, None)
    for iteration in observer.expected_iterations:
        observer.record_submission(
            iteration,
            0,
            FakeFuture(FakeResult(iteration=iteration, error="worker failed")),
        ).result()

    with pytest.raises(RuntimeError, match="no successful evaluations"):
        observer.verify(_observer_controller({}))


def test_real_evaluator_failure_envelope_is_recognized(monkeypatch):
    import evolve.openevolve_evaluator as evaluator

    contract_id = 12345
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    metrics = evaluator._winner_preflight_failure_result(
        "candidate persistence failed",
        timed_out=False,
    )

    assert launcher._exact_incomplete_winner_preflight_markers(
        metrics,
        expected_contract_id=contract_id,
    ) is not None


def test_pinned_outer_stage1_mutation_exception_is_recognized():
    exception_metrics = {"stage1_passed": 0.0, "error": 0.0}
    assert launcher._pre_marker_stage1_failure_evidence(
        exception_metrics,
        _outer_stage1_exception_artifacts(),
    ) == {"error_type": "NameError", "timeout": False}


def test_empty_mutation_exception_message_is_recognized():
    assert launcher._pre_marker_stage1_failure_evidence(
        {"stage1_passed": 0.0, "error": 0.0},
        _outer_stage1_exception_artifacts(
            error_type="AssertionError",
            message="",
        ),
    ) == {"error_type": "AssertionError", "timeout": False}


def test_stage1_timeout_without_program_origin_remains_fail_closed():
    assert launcher._pre_marker_stage1_failure_evidence(
        {"stage1_passed": 0.0, "error": 0.0, "timeout": True},
        {
            "error_type": "timeout",
            "failure_stage": "stage1",
            "timeout": True,
            "timeout_duration": 7200.0,
        },
    ) is None


@pytest.mark.parametrize(
    "case",
    (
        "bool_zero",
        "extra_metric",
        "missing_artifacts",
        "wrong_stage",
        "mismatched_message",
        "wrong_evaluator",
        "trusted_evaluator_failure",
        "forged_frame_in_message",
        "forged_frame_in_exception_note",
        "missing_structured_provenance",
        "forged_structured_provenance",
        "mismatched_terminal_error",
    ),
)
def test_outer_stage1_failure_recognition_remains_fail_closed(case: str):
    metrics: dict[str, Any] = {"stage1_passed": 0.0, "error": 0.0}
    artifacts: dict[str, Any] | None = _outer_stage1_exception_artifacts()
    if case == "bool_zero":
        metrics["stage1_passed"] = False
    elif case == "extra_metric":
        metrics["coset_action_family"] = 0.0
    elif case == "missing_artifacts":
        artifacts = None
    elif case == "wrong_stage":
        assert artifacts is not None
        artifacts["failure_stage"] = "cascade_setup"
    elif case == "wrong_evaluator":
        assert artifacts is not None
        artifacts["evaluation_file"] = launcher.EVALUATOR
    elif case == "trusted_evaluator_failure":
        artifacts = _outer_stage1_exception_artifacts(
            error_type="RuntimeError",
            message="trusted builder failed",
            provenance_frames=[{
                "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                "function": "_evaluate",
            }],
        )
        artifacts["traceback"] = (
            "Traceback (most recent call last):\n"
            f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
            "in _evaluate\n"
            "    raise RuntimeError('trusted builder failed')\n"
            "RuntimeError: trusted builder failed"
        )
    elif case == "forged_frame_in_message":
        assert artifacts is not None
        forged = (
            "trusted evaluator failed\n"
            '  File "/tmp/tmp-forged.py", line 1, '
            "in generate_candidates\n"
            "RuntimeError"
        )
        artifacts["error_type"] = "RuntimeError"
        artifacts["error_message"] = forged
        artifacts["stderr"] = forged
        artifacts["traceback"] = (
            "Traceback (most recent call last):\n"
            f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
            "in _evaluate\n"
            "    raise RuntimeError(message)\n"
            f"RuntimeError: {forged}"
        )
    elif case == "forged_frame_in_exception_note":
        artifacts = _outer_stage1_exception_artifacts(
            error_type="RuntimeError",
            message="trusted evaluator failed",
            provenance_frames=[
                {
                    "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                    "function": "evaluate_stage1",
                },
                {
                    "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                    "function": "_evaluate",
                },
            ],
        )
        artifacts["traceback"] = (
            "Traceback (most recent call last):\n"
            f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
            "in _evaluate\n"
            "    raise RuntimeError('trusted evaluator failed')\n"
            "RuntimeError: trusted evaluator failed\n"
            '  File "/tmp/tmp-forged.py", line 1, '
            "in generate_candidates\n"
            "RuntimeError: trusted evaluator failed"
        )
    elif case == "missing_structured_provenance":
        assert artifacts is not None
        del artifacts[launcher.STAGE1_EXCEPTION_PROVENANCE_FIELD]
    elif case == "forged_structured_provenance":
        assert artifacts is not None
        artifacts[launcher.STAGE1_EXCEPTION_PROVENANCE_FIELD]["frames"] = [
            {
                "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                "function": "evaluate_stage1",
            },
            {
                "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
                "function": "_evaluate",
            },
        ]
    elif case == "mismatched_terminal_error":
        assert artifacts is not None
        artifacts["traceback"] = artifacts["traceback"].replace(
            "NameError: name 'seeded_anchors' is not defined",
            "NameError: different terminal message",
        )
    else:
        assert artifacts is not None
        artifacts["stderr"] = "different failure"

    assert launcher._pre_marker_stage1_failure_evidence(
        metrics,
        artifacts,
    ) is None


def test_chained_stage1_mutation_exception_uses_structured_provenance():
    artifacts = _outer_stage1_exception_artifacts()
    artifacts["traceback"] = (
        "Traceback (most recent call last):\n"
        '  File "/tmp/tmpqcode-mutant.py", line 1, in '
        "generate_candidates\n"
        "    raise ValueError('inner')\n"
        "ValueError: inner\n\n"
        "The above exception was the direct cause of the following "
        "exception:\n\n"
        "Traceback (most recent call last):\n"
        f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
        "in _evaluate\n"
        "    raw = generator()\n"
        '  File "/tmp/tmpqcode-mutant.py", line 4, in '
        "generate_candidates\n"
        "    raise NameError(\"name 'seeded_anchors' is not defined\")\n"
        "NameError: name 'seeded_anchors' is not defined"
    )

    assert launcher._pre_marker_stage1_failure_evidence(
        {"stage1_passed": 0.0, "error": 0.0},
        artifacts,
    ) == {"error_type": "NameError", "timeout": False}


def test_default_evaluator_cannot_use_coset_mutation_failure_lane():
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=24680,
    )
    observer.begin(1, 1, None)
    raw = _child(1)
    raw.child_program_dict["metrics"] = {
        "stage1_passed": 0.0,
        "error": 0.0,
    }
    raw.artifacts = _outer_stage1_exception_artifacts()

    observed = observer.record_future_result(1, raw)

    assert observed is raw
    assert 1 in observer.expected_programs
    assert 1 not in observer.outcomes


def test_coset_name_error_is_accounted_between_successful_iterations():
    contract_id = 24680
    observer = launcher._SliceObserver(
        129,
        3,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        evaluator_kind=launcher.EVALUATOR_KIND_COSET_TWO_BLOCK,
    )
    observer.begin(130, 3, None)
    raw_results = {
        iteration: _child(iteration)
        for iteration in (130, 131, 132)
    }
    for iteration in (130, 132):
        raw_results[iteration].child_program_dict["metrics"].update(
            _coset_preflight_markers(contract_id)
        )
    raw_results[131].child_program_dict["metrics"] = {
        "stage1_passed": 0.0,
        "error": 0.0,
    }
    raw_results[131].artifacts = _outer_stage1_exception_artifacts()

    futures = {
        iteration: observer.record_submission(
            iteration,
            iteration % 2,
            FakeFuture(raw_results[iteration]),
        )
        for iteration in (130, 131, 132)
    }
    programs: dict[str, Any] = {}
    for iteration in (132, 131, 130):
        result = futures[iteration].result()
        if iteration == 131:
            assert result.child_program_dict is None
            failure = json.loads(result.error)
            assert failure["kind"] == "stage1_outer_cascade_incomplete"
            assert failure["iteration"] == 131
            assert failure["evidence"] == {
                "error_type": "NameError",
                "timeout": False,
            }
            continue
        program = SimpleNamespace(**result.child_program_dict)
        programs[program.id] = program
        observer.record_program_add(iteration, program)

    observer.verify(_observer_controller(programs))
    assert observer.accounting_complete is True
    assert observer.outcomes[131]["status"] == "worker_error"
    assert 131 not in observer.expected_programs
    assert set(programs) == {"program-130", "program-132"}


def test_trusted_stage1_exception_is_fatal_but_not_a_genome_marker_error():
    contract_id = 24680
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        evaluator_kind=launcher.EVALUATOR_KIND_COSET_TWO_BLOCK,
        coset_map_schema_version=4,
    )
    observer.begin(1, 1, None)
    raw = _child(1)
    raw.child_program_dict["metrics"] = {
        "stage1_passed": 0.0,
        "error": 0.0,
    }
    raw.artifacts = _outer_stage1_exception_artifacts(
        error_type="RuntimeError",
        message="proof cache changed before candidate-log commit",
        provenance_frames=[{
            "path": launcher.EVALUATOR_COSET_TWO_BLOCK,
            "function": "_evaluate",
        }],
    )
    raw.artifacts["traceback"] = (
        "Traceback (most recent call last):\n"
        f'  File "{launcher.EVALUATOR_COSET_TWO_BLOCK}", line 653, '
        "in _evaluate\n"
        "    raise RuntimeError(message)\n"
        "RuntimeError: proof cache changed before candidate-log commit"
    )

    observed = observer.record_future_result(1, raw)

    assert observed.child_program_dict is None
    failure = json.loads(observed.error)
    assert failure["kind"] == "coset_stage1_evaluation_failed"
    assert failure["reason"] == "stage1_evaluation_failed_before_markers"
    assert failure["error_type"] == "RuntimeError"
    assert failure["evaluator_error_bytes"] == len(
        b"proof cache changed before candidate-log commit"
    )
    assert observer.outcomes[1]["error_kind"] == "stage1_evaluation_failed"
    assert any(
        "failed trusted Stage 1 evaluation before markers" in violation
        for violation in observer.violations
    )
    with pytest.raises(RuntimeError):
        observer.verify(_observer_controller({}))


@pytest.mark.parametrize("hard_timeout", (0, 1))
def test_exact_stage2_failure_is_quarantined_before_database_add(
    hard_timeout: int,
):
    contract_id = 54321
    observer = launcher._SliceObserver(
        20,
        3,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(21, 3, None)
    raw_results = {
        iteration: _child(iteration)
        for iteration in (21, 22, 23)
    }
    for iteration in (21, 23):
        raw_results[iteration].child_program_dict["metrics"].update(
            _preflight_markers(contract_id)
        )
    raw_results[22].child_program_dict["metrics"] = (
        _stage2_failure_metrics(
            contract_id,
            completed_lattices=7,
            hard_timeout=hard_timeout,
        )
    )
    raw_results[22].artifacts = {
        "failure_stage": "stage2",
        "stage2_subprocess_error": "deep lattice made no progress",
        "stage2_stderr": "",
    }
    futures = {
        iteration: observer.record_submission(
            iteration,
            iteration % 2,
            FakeFuture(raw_results[iteration]),
        )
        for iteration in (21, 22, 23)
    }
    programs: dict[str, Any] = {}
    for iteration in (23, 22, 21):
        result = futures[iteration].result()
        if iteration == 22:
            assert result.child_program_dict is None
            failure = json.loads(result.error)
            assert failure["kind"] == "stage2_evaluation_incomplete"
            assert failure["completed_lattices"] == 7
            assert failure["hard_timeout"] == hard_timeout
            continue
        program = SimpleNamespace(**result.child_program_dict)
        programs[program.id] = program
        observer.record_program_add(iteration, program)

    observer.verify(_observer_controller(programs))

    assert observer.outcomes[22]["status"] == "worker_error"
    assert 22 not in observer.expected_programs
    assert set(programs) == {"program-21", "program-23"}


def test_real_stage2_failure_envelope_preserves_stage1_map_metrics(
    monkeypatch,
):
    import evolve.openevolve_evaluator as evaluator

    contract_id = 54321
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    failure = evaluator._stage2_failure_result(
        "deep timeout",
        timed_out=True,
        contract_id=contract_id,
        completed_lattices=6,
    )
    failure_metrics = getattr(failure, "metrics", failure)
    failure_artifacts = getattr(failure, "artifacts", {})
    stage1 = {
        "combined_score": 0.75,
        **_map_descriptor_metrics(
            pattern_type=4,
            support_split_type=5,
            structural_entropy=0.4,
        ),
        **_preflight_markers(contract_id),
    }
    merged = dict(stage1)
    merged.update({
        name: float(value)
        for name, value in failure_metrics.items()
        if isinstance(value, (int, float)) and name != "error"
    })

    assert merged["combined_score"] == 0.75
    assert merged["pattern_type"] == 4.0
    assert (
        merged[launcher.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC]
        == 5.0
    )
    assert launcher._exact_incomplete_stage2_markers(
        merged,
        failure_artifacts,
        expected_contract_id=contract_id,
    ) is not None


@pytest.mark.parametrize(
    ("metrics_update", "artifacts"),
    (
        (
            {"stage2_passed": 0.0, "timeout": True},
            {"failure_stage": "stage2", "stage2_timeout": True},
        ),
        (
            {"stage2_passed": 0.0},
            {
                "failure_stage": "stage2",
                "stage2_stderr": "outer cascade exception",
            },
        ),
        (
            {},
            {
                "failure_stage": "stage2",
                "stage2_stderr": "outer cascade exception",
            },
        ),
    ),
)
def test_outer_cascade_stage2_failure_is_quarantined_before_database_add(
    metrics_update: dict[str, Any],
    artifacts: dict[str, Any],
):
    contract_id = 54321
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(1, 1, None)
    child = _child(1)
    child.child_program_dict["metrics"].update(
        _preflight_markers(contract_id)
    )
    child.child_program_dict["metrics"].update(metrics_update)
    child.artifacts = artifacts

    result = observer.record_submission(
        1, 0, FakeFuture(child)
    ).result()

    assert result.child_program_dict is None
    failure = json.loads(result.error)
    assert failure["kind"] == "stage2_outer_cascade_incomplete"
    assert failure["evidence"] == {
        "artifact_stage2": artifacts.get("failure_stage") == "stage2",
        "stage2_passed_zero": metrics_update.get("stage2_passed") == 0.0,
        "timeout": metrics_update.get("timeout") is True,
    }
    with pytest.raises(RuntimeError, match="no successful evaluations"):
        observer.verify(_observer_controller({}))


def test_stage2_markers_are_required_exactly_when_cascade_selects_stage2():
    contract_id = 54321
    low_score = {
        "combined_score": 0.009,
        **_map_descriptor_metrics(),
        **_preflight_markers(contract_id),
    }
    assert launcher._validated_managed_stage2_state(
        low_score,
        expected_contract_id=contract_id,
        cascade_threshold=0.01,
    ) == "not_observed"

    high_score = {**low_score, "combined_score": 0.01}
    with pytest.raises(
        RuntimeError,
        match="selected by the cascade.*no managed",
    ):
        launcher._validated_managed_stage2_state(
            high_score,
            expected_contract_id=contract_id,
            cascade_threshold=0.01,
        )

    complete = {
        **high_score,
        launcher.STAGE2_CONTRACT_VERSION_METRIC: float(
            launcher.STAGE2_DEEP_CONTRACT_VERSION
        ),
        launcher.STAGE2_CONTRACT_ID_METRIC: float(contract_id),
        launcher.STAGE2_COMPLETE_METRIC: 1.0,
        launcher.STAGE2_INCOMPLETE_METRIC: 0.0,
        launcher.STAGE2_LATTICES_METRIC: float(
            launcher.STAGE2_DEEP_LATTICE_COUNT
        ),
        launcher.STAGE2_HARD_TIMEOUT_METRIC: 0.0,
        launcher.STAGE2_SUBPROCESS_FAILED_METRIC: 0.0,
    }
    assert launcher._validated_managed_stage2_state(
        complete,
        expected_contract_id=contract_id,
        cascade_threshold=0.01,
    ) == "completed"


@pytest.mark.parametrize(
    "mutation",
    (
        "wrong_contract",
        "too_many_lattices",
        "false_complete",
        "missing_artifact",
    ),
)
def test_noncanonical_stage2_failure_is_fatal_and_not_added(
    mutation: str,
):
    contract_id = 54321
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(1, 1, None)
    child = _child(1)
    child.child_program_dict["metrics"] = _stage2_failure_metrics(
        contract_id
    )
    child.artifacts = {
        "failure_stage": "stage2",
        "stage2_subprocess_error": "deep timeout",
    }
    if mutation == "wrong_contract":
        child.child_program_dict["metrics"][
            launcher.STAGE2_CONTRACT_ID_METRIC
        ] = float(contract_id + 1)
    elif mutation == "too_many_lattices":
        child.child_program_dict["metrics"][
            launcher.STAGE2_LATTICES_METRIC
        ] = float(launcher.STAGE2_DEEP_LATTICE_COUNT + 1)
    elif mutation == "false_complete":
        child.child_program_dict["metrics"][
            launcher.STAGE2_COMPLETE_METRIC
        ] = 1.0
    else:
        child.artifacts.pop("stage2_subprocess_error")

    result = observer.record_submission(
        1, 0, FakeFuture(child)
    ).result()

    assert result.child_program_dict is None
    assert json.loads(result.error)["kind"] == "stage2_evaluation_invalid"
    with pytest.raises(
        RuntimeError,
        match="invalid Stage 2 state",
    ):
        observer.verify(_observer_controller({}))


@pytest.mark.parametrize(
    "case",
    ("wrong_contract", "false_complete", "extra_failure_field"),
)
def test_noncanonical_incomplete_claim_remains_fatal(case: str):
    contract_id = 12345
    observer = launcher._SliceObserver(
        0,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
    )
    observer.begin(1, 1, None)
    child = _child(1)
    if case == "wrong_contract":
        child.child_program_dict["metrics"] = (
            _incomplete_preflight_metrics(contract_id + 1)
        )
    elif case == "false_complete":
        child.child_program_dict["metrics"].update(
            _preflight_markers(contract_id)
        )
        child.child_program_dict["metrics"][
            launcher.WINNER_PREFLIGHT_OMITTED_METRIC
        ] = 1.0
    else:
        child.child_program_dict["metrics"] = (
            _incomplete_preflight_metrics(contract_id)
        )
        child.child_program_dict["metrics"]["unbound_failure_field"] = 1.0
    future = observer.record_submission(1, 0, FakeFuture(child))
    result = future.result()
    assert result.error is None
    program = SimpleNamespace(**result.child_program_dict)
    observer.record_program_add(1, program)

    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        observer.verify(_observer_controller({program.id: program}))
    assert observer.accounting_complete is False


def test_missing_resume_backfill_report_cannot_complete_slice():
    contract_id = 67890
    observer = launcher._SliceObserver(
        10,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        checkpoint_preflight_required=True,
    )
    observer.begin(11, 1, None)
    child = _child(11)
    child.child_program_dict["metrics"].update(
        _preflight_markers(contract_id)
    )
    future = observer.record_submission(11, 0, FakeFuture(child))
    result = future.result()
    program = SimpleNamespace(**result.child_program_dict)
    observer.record_program_add(11, program)

    with pytest.raises(
        RuntimeError,
        match="checkpoint winner preflight did not complete",
    ):
        observer.verify(
            _observer_controller({program.id: program})
        )
    assert observer.accounting_complete is False


def test_observer_accepts_only_well_formed_multisplit_bridge_report():
    contract_id = 67891
    report = {
        "schema_version": 4,
        "status": "completed",
        "contract_version": launcher.WINNER_PREFLIGHT_CONTRACT_VERSION,
        "contract_id": contract_id,
        "mode": "typed-json-dsl-activation-bridge-root",
        "source_checkpoint": {
            "path": "/tmp/checkpoint_125",
            "sha256": "a" * 64,
            "last_iteration": 125,
            "programs": 26,
        },
        "source_programs": 26,
        "source_program_set_sha256": "b" * 64,
        "target_programs": 1,
        "root_program_id": "coset-activation-root-" + "c" * 32,
        "root_policy_sha256": "d" * 64,
        "root_code_sha256": "e" * 64,
        "activation_sha256": "f" * 64,
        "approved_support_splits": [
            [2, 4],
            [2, 3],
            [3, 2],
            [3, 3],
        ],
        "root_support_split": [2, 4],
        "bridge_candidate_range": {},
    }
    accepted = launcher._SliceObserver(
        125,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        checkpoint_preflight_required=True,
    )
    accepted.record_checkpoint_preflight(report)

    assert accepted.violations == []
    assert accepted.checkpoint_preflight_report == report

    tampered = copy.deepcopy(report)
    tampered["root_support_split"] = [3, 2]
    rejected = launcher._SliceObserver(
        125,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        checkpoint_preflight_required=True,
    )
    rejected.record_checkpoint_preflight(tampered)
    assert rejected.checkpoint_preflight_report is None
    assert rejected.violations == [
        "checkpoint activation bridge report is invalid"
    ]

    singleton = copy.deepcopy(report)
    singleton["approved_support_splits"] = [[2, 4]]
    singleton["root_support_split"] = [2, 4]
    rejected_singleton = launcher._SliceObserver(
        125,
        1,
        FakeResult,
        expected_preflight_contract_id=contract_id,
        checkpoint_preflight_required=True,
    )
    rejected_singleton.record_checkpoint_preflight(singleton)
    assert rejected_singleton.checkpoint_preflight_report is None
    assert rejected_singleton.violations == [
        "checkpoint activation bridge report is invalid"
    ]


@pytest.mark.parametrize(
    "case",
    (
        "submit_none",
        "future_exception",
        "future_cancelled",
        "result_iteration_mismatch",
        "child_iteration_mismatch",
        "program_id_reused",
        "add_missing",
        "early_stop",
        "shutdown",
    ),
)
def test_observer_rejects_incomplete_or_ambiguous_accounting(case: str):
    observer = launcher._SliceObserver(0, 2, FakeResult)
    observer.begin(1, 2, None)
    first = _child(1, "same-id" if case == "program_id_reused" else None)
    second: Any = _child(
        2, "same-id" if case == "program_id_reused" else None
    )
    if case == "future_exception":
        second = RuntimeError("future exploded")
    elif case == "future_cancelled":
        second = concurrent.futures.CancelledError()
    elif case == "result_iteration_mismatch":
        second = _child(1, "wrong-result-iteration")
    elif case == "child_iteration_mismatch":
        second = FakeResult(
            child_program_dict={"id": "wrong-child-iteration", "iteration_found": 1},
            iteration=2,
        )

    observed = {
        1: observer.record_submission(1, 0, FakeFuture(first)),
        2: observer.record_submission(
            2, 0, None if case == "submit_none" else FakeFuture(second)
        ),
    }
    programs: dict[str, Any] = {}
    for iteration in (1, 2):
        future = observed[iteration]
        if future is None:
            continue
        try:
            result = future.result()
        except BaseException:
            continue
        if result.child_program_dict is None:
            continue
        program_id = result.child_program_dict["id"]
        programs[program_id] = SimpleNamespace(**result.child_program_dict)
        if not (case == "add_missing" and iteration == 2):
            observer.record_program_add(iteration, programs[program_id])

    controller = _observer_controller(
        programs,
        shutdown=case == "shutdown",
        early_stop=case == "early_stop",
    )
    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        observer.verify(controller)
    assert observer.accounting_complete is False


def test_observer_rejects_non_integer_submission_and_island():
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.begin(1, 1, None)
    future = observer.record_submission(True, False, FakeFuture(_child(1)))
    result = future.result()
    program_id = result.child_program_dict["id"]
    programs = {program_id: SimpleNamespace(**result.child_program_dict)}
    observer.record_program_add(1, programs[program_id])
    with pytest.raises(RuntimeError, match="submission iteration"):
        observer.verify(_observer_controller(programs))


class FakeDatabase:
    def __init__(
        self,
        *,
        fail_add_at: int | None = None,
        mutate_at: int | None = None,
    ):
        self.programs: dict[str, Any] = {}
        self.fail_add_at = fail_add_at
        self.mutate_at = mutate_at

    def add(
        self,
        program: Any,
        iteration: int | None = None,
        target_island: int | None = None,
    ) -> str:
        del target_island
        if self.fail_add_at is not None and iteration == self.fail_add_at:
            raise RuntimeError("database add failed")
        if iteration is not None:
            program.iteration_found = iteration
        if self.mutate_at is not None and iteration == self.mutate_at:
            program.code = "content-replaced-after-future"
        self.programs[program.id] = program
        return program.id


class FakeOpenEvolve:
    def __init__(self):
        self.output_dir = "/fake-output"
        self.saved: list[int] = []

    def _save_checkpoint(self, iteration: int) -> None:
        self.saved.append(iteration)


class FakeParallelController:
    scenario = "normal"

    def __init__(self, database: FakeDatabase):
        self.database = database
        self.shutdown_event = threading.Event()
        self.early_stopping_triggered = False
        self.num_islands = 2

    def request_shutdown(self) -> None:
        self.shutdown_event.set()

    def _submit_iteration(
        self, iteration: int, island_id: int | None = None
    ) -> FakeFuture | None:
        del island_id
        if self.scenario == "submit_none" and iteration == 2:
            return None
        if self.scenario == "future_exception" and iteration == 2:
            return FakeFuture(RuntimeError("future failed"))
        if self.scenario == "future_cancelled" and iteration == 2:
            return FakeFuture(concurrent.futures.CancelledError())
        if self.scenario == "all_worker_error":
            return FakeFuture(
                FakeResult(iteration=iteration, error="worker failed")
            )
        if self.scenario == "id_wrong" and iteration == 2:
            return FakeFuture(
                FakeResult(
                    child_program_dict={
                        "id": "bad-iteration",
                        "iteration_found": 1,
                    },
                    iteration=2,
                )
            )
        child = _child(iteration)
        if self.scenario in {
            "incomplete_preflight",
            "wrong_preflight_contract",
            "false_complete_preflight",
        }:
            if iteration == 2:
                if self.scenario == "incomplete_preflight":
                    child.child_program_dict["metrics"] = (
                        _incomplete_preflight_metrics(24680, hard_timeout=1)
                    )
                elif self.scenario == "wrong_preflight_contract":
                    child.child_program_dict["metrics"] = (
                        _incomplete_preflight_metrics(24681)
                    )
                else:
                    child.child_program_dict["metrics"].update(
                        _preflight_markers(24680)
                    )
                    child.child_program_dict["metrics"][
                        launcher.WINNER_PREFLIGHT_OMITTED_METRIC
                    ] = 1.0
            else:
                child.child_program_dict["metrics"].update(
                    _preflight_markers(24680)
                )
        return FakeFuture(child)

    async def run_evolution(
        self,
        start_iteration: int,
        max_iterations: int,
        target_score: float | None = None,
        checkpoint_callback: Any = None,
    ) -> Any:
        del target_score
        end = start_iteration + max_iterations - 1
        iterations = list(range(start_iteration, end + 1))
        if self.scenario == "early_return":
            iterations = iterations[:1]
        futures = [
            (iteration, self._submit_iteration(iteration, iteration % 2))
            for iteration in iterations
        ]
        checkpoint_callback(start_iteration)
        for iteration, future in reversed(futures):
            if future is None:
                continue
            try:
                result = future.result()
                if result.error:
                    continue
                child = SimpleNamespace(**result.child_program_dict)
                self.database.add(child, iteration=iteration)
                if self.scenario == "migration" and iteration == end:
                    self.database.add(
                        SimpleNamespace(
                            id=f"migrant-{iteration}",
                            code=child.code,
                            metrics=dict(child.metrics),
                            iteration_found=0,
                            parent_id=child.id,
                            metadata={"migrant": True, "island": 1},
                        ),
                        target_island=1,
                    )
            except Exception:
                continue
        if self.scenario == "request_shutdown":
            self.request_shutdown()
        if self.scenario == "early_stop":
            self.early_stopping_triggered = True
        if self.scenario == "system_exit_zero":
            raise SystemExit(0)
        checkpoint_callback(end)
        return None


def _fake_source_modules(monkeypatch: pytest.MonkeyPatch):
    controller_module = SimpleNamespace(
        ProcessParallelController=FakeParallelController,
        OpenEvolve=FakeOpenEvolve,
    )
    process_module = SimpleNamespace(SerializableResult=FakeResult)
    binding = {"controller": {"path": "/fake", "sha256": "a" * 64, "bytes": 1}}
    monkeypatch.setattr(
        launcher,
        "_openevolve_source_binding",
        lambda: (binding, controller_module, process_module),
    )
    monkeypatch.setattr(
        launcher,
        "_strong_checkpoint_descriptor",
        lambda _output, _checkpoint, expected_iteration=None: {
            "path": f"/fake-output/checkpoints/checkpoint_{expected_iteration}",
            "last_iteration": expected_iteration,
            "sha256": f"{expected_iteration:064x}",
            "programs": expected_iteration + 1,
        },
    )
    return binding, controller_module


def test_verified_controller_suppresses_early_end_save_and_saves_after_accounting(
    monkeypatch,
):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "normal"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(0, 2) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(database)
        asyncio.run(
            parallel.run_evolution(
                1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
            )
        )
        assert open_evolve.saved == []
        assert observer.accounting_complete is True

    assert open_evolve.saved == [2]
    assert [
        (save["iteration"], save["accounting_complete"])
        for save in observer.checkpoint_saves
    ] == [(1, False), (2, False), (2, True)]
    assert all(
        save["suppressed"] is True
        for save in observer.checkpoint_saves[:2]
    )
    assert observer.checkpoint_saves[-1]["accounting_complete"] is True


def test_verified_controller_accounts_for_database_migration_adds(monkeypatch):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "migration"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(0, 2) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(database)
        asyncio.run(
            parallel.run_evolution(
                1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
            )
        )
        assert observer.accounting_complete is True
        assert observer.auxiliary_programs == [
            {
                "program_id": "migrant-2",
                "parent_id": "program-2",
                "target_island": 1,
                "program_sha256": observer.auxiliary_programs[0][
                    "program_sha256"
                ],
                "program_bytes": observer.auxiliary_programs[0][
                    "program_bytes"
                ],
            }
        ]

    assert open_evolve.saved == [2]


def test_verified_controller_checkpoints_other_successful_children_around_incomplete(
    monkeypatch,
):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "incomplete_preflight"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(
        0,
        3,
        expected_preflight_contract_id=24680,
    ) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(database)
        asyncio.run(
            parallel.run_evolution(
                1, 3, None, checkpoint_callback=open_evolve._save_checkpoint
            )
        )
        assert observer.accounting_complete is True
        assert observer.outcomes[2]["status"] == "worker_error"
        assert set(database.programs) == {"program-1", "program-3"}

    assert open_evolve.saved == [3]
    assert observer.checkpoint_saves[-1]["accounting_complete"] is True


@pytest.mark.parametrize(
    "scenario",
    ("wrong_preflight_contract", "false_complete_preflight"),
)
def test_verified_controller_does_not_checkpoint_noncanonical_failure_claim(
    monkeypatch,
    scenario: str,
):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = scenario
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        with launcher._verified_slice_controller(
            0,
            2,
            expected_preflight_contract_id=24680,
        ):
            parallel = controller_module.ProcessParallelController(database)
            asyncio.run(
                parallel.run_evolution(
                    1,
                    2,
                    None,
                    checkpoint_callback=open_evolve._save_checkpoint,
                )
            )
    assert open_evolve.saved == []


def test_observer_rejects_unclassified_iterationless_database_add():
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.begin(1, 1, None)
    observer.record_auxiliary_program_add(
        program=SimpleNamespace(
            id="not-a-migrant",
            parent_id="parent",
            code="code",
            metrics={},
            metadata={},
            iteration_found=0,
        ),
        stored=SimpleNamespace(id="not-a-migrant", iteration_found=0),
        parent=SimpleNamespace(id="parent", code="code", metrics={}),
        target_island=0,
        num_islands=2,
    )

    with pytest.raises(RuntimeError, match="valid migration"):
        observer.verify(_observer_controller({}))


@pytest.mark.parametrize(
    "scenario",
    (
        "submit_none",
        "future_exception",
        "future_cancelled",
        "id_wrong",
        "add_fail",
        "content_replaced",
        "all_worker_error",
        "early_return",
        "early_stop",
        "request_shutdown",
    ),
)
def test_verified_controller_refuses_incomplete_scenarios(monkeypatch, scenario):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = scenario
    database = FakeDatabase(
        fail_add_at=2 if scenario == "add_fail" else None,
        mutate_at=2 if scenario == "content_replaced" else None,
    )
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        with launcher._verified_slice_controller(0, 2):
            parallel = controller_module.ProcessParallelController(database)
            asyncio.run(
                parallel.run_evolution(
                    1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
                )
            )
    assert open_evolve.saved == []


def test_verified_controller_system_exit_zero_never_completes(monkeypatch):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "system_exit_zero"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(SystemExit) as raised:
        with launcher._verified_slice_controller(0, 2) as (observer, _sources):
            parallel = controller_module.ProcessParallelController(database)
            asyncio.run(
                parallel.run_evolution(
                    1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
                )
            )
    assert raised.value.code == 0
    assert observer.accounting_complete is False
    assert open_evolve.saved == []


def test_resume_hook_runs_backfill_after_load_before_new_iterations(
    tmp_path, monkeypatch
):
    order = []

    class FakeOpenEvolve:
        def __init__(self, **_kwargs):
            self.database = SimpleNamespace(programs={})

        def _load_checkpoint(self, checkpoint_path):
            order.append(("load", checkpoint_path))
            self.database.programs["old"] = SimpleNamespace(
                id="old",
                code="def generate_candidates(ell, m): return []",
                metrics={},
            )

        async def run(self, *, iterations, checkpoint_path):
            self._load_checkpoint(checkpoint_path)
            order.append(("run", iterations))
            return None

    import openevolve.controller as controller_module

    monkeypatch.setattr(
        controller_module, "OpenEvolve", FakeOpenEvolve
    )

    def backfill(database):
        assert "old" in database.programs
        order.append(("backfill", len(database.programs)))

    checkpoint = tmp_path / "checkpoint_25"
    checkpoint.mkdir()
    launcher._run_resume(
        SimpleNamespace(),
        str(tmp_path / "output"),
        3,
        str(checkpoint),
        checkpoint_preflight=backfill,
    )

    assert order == [
        ("load", str(checkpoint)),
        ("backfill", 1),
        ("run", 3),
    ]


def test_fresh_initial_stage2_outer_failure_is_rejected_before_database_add(
    tmp_path,
    monkeypatch,
):
    import openevolve.api as api_module
    from openevolve.config import Config, LLMModelConfig

    contract_id = 54321
    seed = tmp_path / "seed.py"
    evaluator = tmp_path / "evaluator.py"
    seed.write_text("def generate_candidates(ell, m): return []\n")
    evaluator.write_text("def evaluate(_path): return {'combined_score': 0}\n")
    metrics = {
        "combined_score": 0.25,
        "stage2_passed": 0.0,
        "timeout": True,
        **_map_descriptor_metrics(),
        **_preflight_markers(contract_id),
    }
    instances = []

    class FakeDatabase:
        def __init__(self):
            self.programs = {}
            self.add_calls = 0

        def add(self, program, iteration=None, target_island=None):
            del iteration, target_island
            self.add_calls += 1
            self.programs[program.id] = program
            return program.id

    class FakeFreshOpenEvolve:
        def __init__(
            self,
            *,
            initial_program_path,
            evaluation_file,
            config,
            output_dir,
        ):
            del evaluation_file, config, output_dir
            self.initial_program_code = Path(initial_program_path).read_text()
            self.database = FakeDatabase()
            self.evaluator = SimpleNamespace(
                _pending_artifacts={
                    "initial-id": {
                        "failure_stage": "stage2",
                        "stage2_timeout": True,
                    }
                }
            )
            instances.append(self)

        async def run(self, *, iterations):
            del iterations
            program = SimpleNamespace(
                id="initial-id",
                code=self.initial_program_code,
                metrics=dict(metrics),
                iteration_found=0,
            )
            self.database.add(program)
            return program

    monkeypatch.setattr(api_module, "OpenEvolve", FakeFreshOpenEvolve)
    config = Config()
    config.llm.models = [LLMModelConfig(name="fake-model")]

    with pytest.raises(
        RuntimeError,
        match="Stage 2 failed.*before emitting",
    ):
        launcher._run_fresh(
            config,
            str(tmp_path / "output"),
            1,
            seed=str(seed),
            evaluator=str(evaluator),
            initial_program_preflight=lambda observed_metrics, artifacts: (
                launcher._validate_managed_initial_evaluation(
                    observed_metrics,
                    artifacts,
                    expected_contract_id=contract_id,
                    cascade_threshold=0.01,
                )
            ),
        )

    assert len(instances) == 1
    assert instances[0].database.add_calls == 0
    assert instances[0].database.programs == {}
    assert api_module.OpenEvolve is FakeFreshOpenEvolve


def test_loaded_checkpoint_cannot_silently_drop_old_program(tmp_path):
    checkpoint = tmp_path / "checkpoint_25"
    programs_dir = checkpoint / "programs"
    programs_dir.mkdir(parents=True)
    for program_id in ("a", "b"):
        (programs_dir / f"{program_id}.json").write_text(json.dumps({
            "id": program_id,
            "code": f"code-{program_id}",
            "metrics": {},
        }))
    database = SimpleNamespace(programs={
        "a": SimpleNamespace(id="a", code="code-a", metrics={}),
    })

    with pytest.raises(
        RuntimeError,
        match="exact checkpoint program set",
    ):
        launcher._validate_loaded_checkpoint_database(
            database, checkpoint
        )


@pytest.mark.parametrize(
    "legacy_state",
    ("selected_without_markers", "low_score_success", "timeout"),
)
def test_loaded_legacy_stage2_checkpoint_fails_before_stage1_backfill(
    legacy_state: str,
):
    metrics = {
        "combined_score": 0.25,
        **_map_descriptor_metrics(),
    }
    if legacy_state == "low_score_success":
        metrics.update({"combined_score": 0.0, "best_fom": 0.0})
    elif legacy_state == "timeout":
        metrics.update({"stage2_passed": 0.0, "timeout": True})
    database = SimpleNamespace(
        programs={
            "legacy": SimpleNamespace(
                id="legacy",
                code="def generate_candidates(ell, m): return []",
                metrics=metrics,
            )
        }
    )

    with pytest.raises(
        RuntimeError,
        match="managed Stage 2 contract.*fresh campaign",
    ):
        launcher._validate_loaded_checkpoint_stage2_contract(
            database,
            expected_contract_id=54321,
            cascade_threshold=0.01,
        )


def test_backfill_updates_every_same_code_program_without_touching_base(
    tmp_path, monkeypatch
):
    contract_id = 111222
    shared_code = "def generate_candidates(ell, m): return []\n"
    complete_code = "def generate_candidates(ell, m): return [('x','y')]\n"
    programs = {
        "a": SimpleNamespace(
            id="a",
            code=shared_code,
            metrics={"score": 1.0, **_map_descriptor_metrics()},
        ),
        "b": SimpleNamespace(
            id="b",
            code=shared_code,
            metrics={"score": 2.0, **_map_descriptor_metrics()},
        ),
        "c": SimpleNamespace(
            id="c",
            code=complete_code,
            metrics={
                "score": 3.0,
                **_map_descriptor_metrics(),
                **_preflight_markers(contract_id),
            },
        ),
    }
    database = SimpleNamespace(programs=programs)
    base = tmp_path / "checkpoint_25"
    (base / "programs").mkdir(parents=True)
    (base / "metadata.json").write_text('{"last_iteration":25}\n')
    for program_id, program in programs.items():
        (base / "programs" / f"{program_id}.json").write_text(
            json.dumps({
                "id": program_id,
                "code": program.code,
                "metrics": program.metrics,
            })
        )
    fixed_ns = 1_700_000_000_123_456_789
    for path in [base / "metadata.json", *sorted((base / "programs").iterdir())]:
        os.utime(path, ns=(fixed_ns, fixed_ns))

    def tree_identity():
        return {
            str(path.relative_to(base)): (
                hashlib.sha256(path.read_bytes()).hexdigest(),
                path.stat().st_mtime_ns,
            )
            for path in sorted(base.rglob("*"))
            if path.is_file()
        }

    before = tree_identity()
    calls = []

    def fake_execute(_evaluator, code, **kwargs):
        calls.append((code, kwargs["expected_contract_id"]))
        return _preflight_markers(contract_id)

    monkeypatch.setattr(
        launcher, "_execute_winner_preflight", fake_execute
    )
    report = launcher._backfill_checkpoint_programs(
        database,
        evaluator_path=launcher.EVALUATOR,
        expected_contract_id=contract_id,
        max_workers=4,
        wall_timeout=30,
    )

    assert calls == [(shared_code, contract_id)]
    assert report["unique_program_codes_evaluated"] == 1
    assert report["programs_updated"] == 2
    for program_id in ("a", "b", "c"):
        markers = launcher._validated_winner_preflight_markers(
            programs[program_id].metrics,
            expected_contract_id=contract_id,
        )
        assert markers[launcher.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0
    assert tree_identity() == before


def test_checkpoint_with_old_map_descriptor_fails_before_backfill_evaluation(
    monkeypatch,
):
    program = SimpleNamespace(
        id="legacy",
        code="def generate_candidates(ell, m): return []\n",
        metrics={"combined_score": 1.0},
    )
    monkeypatch.setattr(
        launcher,
        "_execute_winner_preflight",
        lambda *_args, **_kwargs: pytest.fail(
            "an incompatible MAP checkpoint must not be evaluated"
        ),
    )

    with pytest.raises(
        RuntimeError,
        match="incompatible MAP descriptor schema.*fresh campaign",
    ):
        launcher._backfill_checkpoint_programs(
            SimpleNamespace(programs={program.id: program}),
            evaluator_path=launcher.EVALUATOR,
            expected_contract_id=123456,
            max_workers=1,
            wall_timeout=30,
        )

    assert program.metrics == {"combined_score": 1.0}


def test_cross_output_checkpoint_marker_is_recomputed_and_rebound(
    tmp_path, monkeypatch
):
    dependencies = launcher._evaluator_dependency_identities()
    old_contract_id = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=(
            tmp_path / "old-output" / "all_codes.jsonl"
        ).resolve(),
    )
    new_contract_id = launcher._winner_preflight_contract_id(
        launcher.EVALUATOR,
        dependencies,
        candidate_log_path=(
            tmp_path / "new-output" / "all_codes.jsonl"
        ).resolve(),
    )
    program = SimpleNamespace(
        id="old-program",
        code="def generate_candidates(ell, m): return []\n",
        metrics={
            **_map_descriptor_metrics(),
            **_preflight_markers(old_contract_id),
        },
    )
    calls = []

    def fake_execute(_evaluator, code, **kwargs):
        calls.append((code, kwargs["expected_contract_id"]))
        return _preflight_markers(new_contract_id)

    monkeypatch.setattr(
        launcher, "_execute_winner_preflight", fake_execute
    )
    report = launcher._backfill_checkpoint_programs(
        SimpleNamespace(programs={program.id: program}),
        evaluator_path=launcher.EVALUATOR,
        expected_contract_id=new_contract_id,
        max_workers=1,
        wall_timeout=30,
    )

    assert old_contract_id != new_contract_id
    assert calls == [(program.code, new_contract_id)]
    assert report["unique_program_codes_evaluated"] == 1
    assert report["programs_updated"] == 1
    launcher._validated_winner_preflight_markers(
        program.metrics,
        expected_contract_id=new_contract_id,
    )


def test_same_run_checkpoint_marker_is_reused_without_recompute(
    monkeypatch,
):
    contract_id = 770077
    program = SimpleNamespace(
        id="current-program",
        code="def generate_candidates(ell, m): return []\n",
        metrics={
            **_map_descriptor_metrics(),
            **_preflight_markers(contract_id),
        },
    )
    monkeypatch.setattr(
        launcher,
        "_execute_winner_preflight",
        lambda *_args, **_kwargs: pytest.fail(
            "same-run marker must be reused"
        ),
    )

    report = launcher._backfill_checkpoint_programs(
        SimpleNamespace(programs={program.id: program}),
        evaluator_path=launcher.EVALUATOR,
        expected_contract_id=contract_id,
        max_workers=1,
        wall_timeout=30,
    )

    assert report["programs_already_complete"] == 1
    assert report["unique_program_codes_evaluated"] == 0
    assert report["programs_updated"] == 0


def test_checkpoint_backfill_respects_unified_worker_cap(monkeypatch):
    contract_id = 333444
    programs = {
        str(index): SimpleNamespace(
            id=str(index),
            code=(
                "def generate_candidates(ell, m):\n"
                f"    return []  # {index}\n"
            ),
            metrics=_map_descriptor_metrics(),
        )
        for index in range(9)
    }
    lock = threading.Lock()
    active = 0
    peak = 0

    def fake_execute(*_args, **_kwargs):
        nonlocal active, peak
        with lock:
            active += 1
            peak = max(peak, active)
        time.sleep(0.03)
        with lock:
            active -= 1
        return _preflight_markers(contract_id)

    monkeypatch.setattr(
        launcher, "_execute_winner_preflight", fake_execute
    )
    launcher._backfill_checkpoint_programs(
        SimpleNamespace(programs=programs),
        evaluator_path=launcher.EVALUATOR,
        expected_contract_id=contract_id,
        max_workers=3,
        wall_timeout=30,
    )

    assert 1 < peak <= 3


def test_backfill_worker_receives_expected_managed_contract_id(
    tmp_path, monkeypatch
):
    contract_id = 97531
    observed = {}

    class FakeProcess:
        pid = 4242

        def __init__(self, command, **kwargs):
            observed["environment"] = kwargs["env"]
            Path(command[4]).write_text(json.dumps({
                "schema_version": 1,
                "status": "completed",
                "metrics": _preflight_markers(contract_id),
            }))

        def wait(self, timeout=None):
            return 0

        def poll(self):
            return 0

    monkeypatch.setattr(launcher.subprocess, "Popen", FakeProcess)
    markers = launcher._execute_winner_preflight(
        launcher.EVALUATOR,
        "def generate_candidates(ell, m): return []\n",
        expected_contract_id=contract_id,
        wall_timeout=30,
        cancel_event=threading.Event(),
    )

    assert observed["environment"][
        launcher.WINNER_PREFLIGHT_CONTRACT_ID_ENV
    ] == str(contract_id)
    assert markers[launcher.WINNER_PREFLIGHT_CONTRACT_ID_METRIC] == float(
        contract_id
    )


def test_outer_timeout_covers_all_progress_bounded_lattice_attempts():
    configured = 1200.0
    inactivity = launcher._winner_preflight_wall_timeout(configured)

    assert inactivity == 1050.0
    assert launcher._winner_preflight_outer_timeout(configured) == (
        launcher._winner_preflight_attempt_timeout(inactivity)
        * launcher.STAGE1_PREFLIGHT_WORKER_ATTEMPTS
        + inactivity
        * launcher.STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS
        + launcher.STAGE1_PREFLIGHT_OUTER_MARGIN_S
    )


@pytest.mark.parametrize(
    "failure_type",
    (
        launcher._WinnerPreflightTimeout,
        launcher._WinnerPreflightChildFailure,
    ),
)
def test_backfill_child_failure_retries_same_owned_source(
    monkeypatch, failure_type
):
    contract_id = 987654
    code = "def generate_candidates(ell, m): return []\n"
    attempts = []

    def fake_owned(evaluator_path, source, **kwargs):
        attempts.append((evaluator_path, source, dict(kwargs)))
        if len(attempts) == 1:
            raise failure_type("transient child failure")
        return _preflight_markers(contract_id)

    monkeypatch.delenv(launcher.CANDIDATE_LOG_PATH_ENV, raising=False)
    monkeypatch.setattr(
        launcher,
        "_execute_winner_preflight_owned",
        fake_owned,
    )

    markers = launcher._execute_winner_preflight(
        launcher.EVALUATOR,
        code,
        expected_contract_id=contract_id,
        wall_timeout=30,
        cancel_event=threading.Event(),
    )

    assert len(attempts) == 2
    assert attempts[0][0:2] == attempts[1][0:2] == (
        launcher.EVALUATOR,
        code,
    )
    assert markers[launcher.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0


def test_backfill_fake_progress_cannot_extend_absolute_child_wall(
    tmp_path, monkeypatch
):
    terminated = []
    snapshots = 0

    class NeverFinishes:
        pid = 556677

        def __init__(self, _command, **_kwargs):
            self.terminated = False

        def wait(self, timeout=None):
            time.sleep(min(float(timeout), 0.01))
            raise launcher.subprocess.TimeoutExpired("preflight", timeout)

        def poll(self):
            return -9 if self.terminated else None

    def fake_snapshot(*_args, **_kwargs):
        nonlocal snapshots
        snapshots += 1
        return ("a" * 64, 0, snapshots, 0, "in_progress")

    monkeypatch.setattr(launcher.subprocess, "Popen", NeverFinishes)
    monkeypatch.setattr(
        launcher,
        "_winner_preflight_progress_snapshot",
        fake_snapshot,
    )
    monkeypatch.setattr(
        launcher,
        "_winner_preflight_attempt_timeout",
        lambda _timeout: 0.15,
    )
    def terminate(process):
        process.terminated = True
        terminated.append(process.pid)

    monkeypatch.setattr(
        launcher,
        "_terminate_private_worker_group",
        terminate,
    )

    started = time.monotonic()
    with pytest.raises(
        launcher._WinnerPreflightTimeout,
        match="absolute wall timeout",
    ):
        launcher._execute_winner_preflight_owned(
            launcher.EVALUATOR,
            "def generate_candidates(ell, m): return []\n",
            expected_contract_id=24680,
            wall_timeout=0.05,
            cancel_event=threading.Event(),
            progress_path=tmp_path / "progress.json",
        )

    assert time.monotonic() - started < 0.5
    assert snapshots > 2
    assert terminated == [556677]


def test_backfill_failure_mutates_no_program_and_cannot_record_completion(
    monkeypatch,
):
    contract_id = 555666
    programs = {
        "a": SimpleNamespace(
            id="a",
            code="code-a",
            metrics={"old": 1.0, **_map_descriptor_metrics()},
        ),
        "b": SimpleNamespace(
            id="b",
            code="code-b",
            metrics={"old": 2.0, **_map_descriptor_metrics()},
        ),
    }
    before = {
        program_id: dict(program.metrics)
        for program_id, program in programs.items()
    }

    def fail_one(_evaluator, code, **_kwargs):
        if code == "code-b":
            raise RuntimeError("simulated preflight failure")
        return _preflight_markers(contract_id)

    monkeypatch.setattr(
        launcher, "_execute_winner_preflight", fail_one
    )
    with pytest.raises(RuntimeError, match="simulated preflight failure"):
        launcher._backfill_checkpoint_programs(
            SimpleNamespace(programs=programs),
            evaluator_path=launcher.EVALUATOR,
            expected_contract_id=contract_id,
            max_workers=2,
            wall_timeout=30,
        )

    assert {
        program_id: program.metrics
        for program_id, program in programs.items()
    } == before


def test_openevolve_source_hashes_match_pinned_0_2_26():
    pytest.importorskip("openevolve")
    binding, _controller, _process = launcher._openevolve_source_binding()
    assert set(binding) == {
        "controller",
        "process_parallel",
        "database",
        "api",
        "evaluator",
    }
    assert {
        name: descriptor["sha256"] for name, descriptor in binding.items()
    } == launcher.SUPPORTED_OPENEVOLVE_SHA256


def test_real_cascade_merge_preserves_stage1_preflight_markers(tmp_path):
    pytest.importorskip("openevolve")
    from openevolve.config import EvaluatorConfig
    from openevolve.evaluator import Evaluator

    contract_id = 777888
    evaluator_path = tmp_path / "cascade_evaluator.py"
    evaluator_path.write_text(
        "def evaluate_stage1(_path):\n"
        f"    return {dict(combined_score=1.0, **_preflight_markers(contract_id))!r}\n"
        "def evaluate_stage2(_path):\n"
        "    return {'combined_score': 2.0, 'stage2_metric': 9.0}\n"
        "def evaluate(path):\n"
        "    return evaluate_stage2(path)\n"
    )
    program_path = tmp_path / "program.py"
    program_path.write_text(
        "def generate_candidates(ell, m): return []\n"
    )
    instance = Evaluator(
        EvaluatorConfig(
            timeout=30,
            max_retries=0,
            cascade_evaluation=True,
            cascade_thresholds=[0.5, 99.0],
        ),
        str(evaluator_path),
    )

    result = asyncio.run(instance._cascade_evaluate(str(program_path)))

    assert result.metrics["combined_score"] == 2.0
    assert result.metrics["stage2_metric"] == 9.0
    assert (
        result.metrics[launcher.WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        == float(contract_id)
    )
    assert (
        result.metrics[launcher.WINNER_PREFLIGHT_COMPLETE_METRIC]
        == 1.0
    )


@pytest.mark.parametrize("source_name", ["controller", "evaluator"])
def test_openevolve_source_hash_mismatch_fails_closed(
    monkeypatch,
    source_name,
):
    pytest.importorskip("openevolve")
    monkeypatch.setitem(
        launcher.SUPPORTED_OPENEVOLVE_SHA256, source_name, "0" * 64
    )
    with pytest.raises(RuntimeError, match=f"{source_name} source hash"):
        launcher._openevolve_source_binding()


def test_invocation_binding_requires_exact_fields_and_backend_consistency(
    tmp_path,
):
    invocation = {
        "model_names": ["fake-model"],
        "reasoning_effort": None,
        "codex_cli": True,
        "max_parallel_evaluations": 4,
        "api_base": "http://localhost:4000/v1",
        "temperature_disabled": True,
        "codex_version": "codex-cli 1.2.3",
        "codex_cwd": str(Path(launcher.PROJECT_ROOT).resolve()),
        "codex_executable_mode": 0o700,
    }
    backend = tmp_path / "codex_cli_llm.py"
    backend.write_text("backend\n")
    executable = tmp_path / "codex-native"
    executable.write_bytes(b"\x7fELFfake")
    executable.chmod(0o700)
    executable_identity = launcher._file_identity(
        executable, "test Codex executable"
    )
    executable_identity["mode"] = 0o700
    assert launcher._validated_invocation_binding(
        invocation, backend, executable_identity
    ) == invocation
    with pytest.raises(RuntimeError, match="backend binding"):
        launcher._validated_invocation_binding(invocation, None, None)
    with pytest.raises(RuntimeError, match="fields are incomplete"):
        launcher._validated_invocation_binding(
            {**invocation, "schema_version": 99}, backend, executable_identity
        )


def test_managed_codex_resolves_and_pins_native_binary(monkeypatch):
    if launcher.shutil.which("codex") is None:
        pytest.skip("Codex CLI is not installed")
    monkeypatch.delenv("QCODE_CODEX_BIN", raising=False)
    monkeypatch.delenv("QCODE_CODEX_CWD", raising=False)

    identity, version, cwd, view_binding = (
        launcher._resolve_codex_execution_binding()
    )

    native_path = Path(identity["path"])
    assert native_path.read_bytes()[:4] in (b"\x7fELF", b"MZ\x90\x00")
    assert identity["mode"] == native_path.stat().st_mode & 0o7777
    assert version
    assert cwd == str(Path(launcher.PROJECT_ROOT).resolve())
    assert view_binding is None
    assert os.environ["QCODE_CODEX_BIN"] == str(native_path)
    assert os.environ["QCODE_CODEX_CWD"] == cwd


def test_lifecycle_lease_requires_preheld_independent_lock(tmp_path):
    path = (tmp_path / "lifecycle.lock").resolve()
    fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        with pytest.raises(RuntimeError, match="not locked before inheritance"):
            launcher._validate_lifecycle_lease(fd, str(path))
        fcntl.flock(fd, fcntl.LOCK_EX)
        os.set_inheritable(fd, True)
        assert launcher._validate_lifecycle_lease(fd, str(path)) == path
        assert os.get_inheritable(fd) is False
    finally:
        os.close(fd)


def _managed_argv(tmp_path: Path, lease_fd: int, lease_path: Path) -> list[str]:
    context_path = tmp_path / "context.md"
    context_path.write_text("managed context\n")
    return [
        "run_evolution.py",
        "--iterations",
        "1",
        "--output",
        str(tmp_path / "output"),
        "--completion-marker",
        str(tmp_path / "completed.json"),
        "--slice-witness",
        str(tmp_path / "witness.json"),
        "--candidate-start-offset",
        "0",
        "--humanize-context",
        str(context_path),
        "--lifecycle-lease-fd",
        str(lease_fd),
        "--lifecycle-lease-path",
        str(lease_path),
    ]


def test_managed_milp_fails_before_launch(tmp_path, monkeypatch):
    lease_path = (tmp_path / "lease.lock").resolve()
    argv = _managed_argv(tmp_path, 123456, lease_path)
    argv.append("--milp")
    monkeypatch.setattr(launcher.sys, "argv", argv)

    with pytest.raises(SystemExit) as raised:
        launcher.main()

    assert raised.value.code == 2


def test_managed_build_config_system_exit_does_not_reference_unbound_observer(
    tmp_path, monkeypatch
):
    monkeypatch.delenv(launcher.CANDIDATE_LOG_PATH_ENV, raising=False)
    lease_path = (tmp_path / "lease.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    monkeypatch.setattr(
        launcher,
        "_build_config",
        lambda *_args: (_ for _ in ()).throw(SystemExit(1)),
    )
    monkeypatch.setattr(
        launcher.sys, "argv", _managed_argv(tmp_path, lease_fd, lease_path)
    )
    try:
        with pytest.raises(SystemExit) as raised:
            launcher.main()
    finally:
        os.close(lease_fd)
    assert raised.value.code == 1
    assert launcher.CANDIDATE_LOG_PATH_ENV not in os.environ


def test_managed_inner_system_exit_zero_becomes_nonzero(tmp_path, monkeypatch):
    monkeypatch.delenv(
        "QCODE_EVALUATOR_OUTER_TIMEOUT_S",
        raising=False,
    )
    lease_path = (tmp_path / "lease.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    config = SimpleNamespace(
        llm=SimpleNamespace(
            models=[SimpleNamespace(name="fake-model")],
            evaluator_models=[],
        ),
        evaluator=SimpleNamespace(
            parallel_evaluations=1,
            timeout=1200,
            cascade_thresholds=[0.01, 0.5],
        ),
    )

    @contextmanager
    def fake_scope(*_args, **_kwargs):
        yield SimpleNamespace(shutdown_requested=False), {}

    monkeypatch.setattr(launcher, "_build_config", lambda *_args: config)
    monkeypatch.setattr(launcher, "_verified_slice_controller", fake_scope)
    monkeypatch.setattr(
        launcher,
        "_run_fresh",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(SystemExit(0)),
    )
    monkeypatch.setattr(
        launcher.sys, "argv", _managed_argv(tmp_path, lease_fd, lease_path)
    )
    try:
        with pytest.raises(SystemExit) as raised:
            launcher.main()
    finally:
        os.close(lease_fd)
    assert raised.value.code == 130
    assert "QCODE_EVALUATOR_OUTER_TIMEOUT_S" not in os.environ
    assert config.evaluator.timeout == (
        launcher._winner_preflight_outer_timeout(1200.0)
    )
    assert not (tmp_path / "completed.json").exists()
    assert not (tmp_path / "witness.json").exists()


def test_witness_is_written_before_bound_marker(tmp_path, monkeypatch):
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.accounting_complete = True
    observer.submission_attempts = [{
        "iteration": 1,
        "island_id": 0,
        "result": "future",
    }]
    observer.outcomes = {
        1: {
            "iteration": 1,
            "status": "worker_error",
            "error_sha256": "a" * 64,
            "error_bytes": 1,
        }
    }
    observer.checkpoint_saves = [{
        "iteration": 1,
        "accounting_complete": True,
        "checkpoint_sha256": "b" * 64,
        "checkpoint_programs": 2,
    }]
    descriptor = {
        "path": str(tmp_path / "output" / "checkpoints" / "checkpoint_1"),
        "last_iteration": 1,
        "sha256": "b" * 64,
        "programs": 2,
    }
    source_binding = {
        name: {"path": f"/fake/{name}.py", "sha256": char * 64, "bytes": 1}
        for name, char in zip(
            (
                "controller",
                "process_parallel",
                "database",
                "api",
                "evaluator",
            ),
            "cdefg",
        )
    }
    monkeypatch.setattr(
        launcher,
        "_openevolve_source_binding",
        lambda: (source_binding, None, None),
    )
    monkeypatch.setattr(
        launcher, "_strong_checkpoint_descriptor", lambda *_args, **_kwargs: descriptor
    )
    config = tmp_path / "config.yaml"
    seed = tmp_path / "seed.py"
    evaluator = tmp_path / "evaluator.py"
    context = tmp_path / "context.md"
    for path in (config, seed, evaluator, context):
        path.write_text(path.name)
    invocation = {
        "model_names": ["fake-model"],
        "reasoning_effort": "high",
        "codex_cli": False,
        "max_parallel_evaluations": 2,
        "api_base": "http://localhost:4000/v1",
        "temperature_disabled": True,
        "codex_version": None,
        "codex_cwd": None,
        "codex_executable_mode": None,
    }
    context_identity = launcher._file_identity(context, "test context")
    dependency_identities = launcher._evaluator_dependency_identities()
    witness_path = tmp_path / "slice-witness.json"
    marker_path = tmp_path / "completed.json"
    candidate_log = (tmp_path / "output" / "all_codes.jsonl").resolve()

    result, witness = launcher._write_slice_witness(
        witness_path,
        observer=observer,
        source_binding=source_binding,
        output_dir=tmp_path / "output",
        resume_checkpoint=None,
        iterations=1,
        config_path=config,
        seed_path=seed,
        evaluator_path=evaluator,
        context_path=context,
        context_identity=context_identity,
        dependency_identities=dependency_identities,
        backend_path=None,
        codex_executable_identity=None,
        invocation=invocation,
        candidate_log_path=candidate_log,
        candidate_start_offset=0,
    )
    launcher._write_completion_marker(
        marker_path,
        output_dir=tmp_path / "output",
        resume_checkpoint=None,
        iterations=1,
        config_path=config,
        seed_path=seed,
        evaluator_path=evaluator,
        context_path=context,
        context_identity=context_identity,
        dependency_identities=dependency_identities,
        backend_path=None,
        codex_executable_identity=None,
        invocation=invocation,
        result_checkpoint=result,
        slice_witness=witness,
    )

    witness_payload = json.loads(witness_path.read_text())
    marker_payload = json.loads(marker_path.read_text())
    assert launcher.EVOLUTION_LEGACY_SLICE_WITNESS_SCHEMA_VERSION == 4
    assert launcher.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION == 7
    assert witness_payload["schema_version"] == (
        launcher.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
    )
    assert witness_payload["search_portfolio"] is None
    assert launcher.EVOLUTION_LEGACY_COMPLETION_SCHEMA_VERSION == 4
    assert launcher.EVOLUTION_COMPLETION_SCHEMA_VERSION == 7
    assert marker_payload["schema_version"] == (
        launcher.EVOLUTION_COMPLETION_SCHEMA_VERSION
    )
    assert marker_payload["slice_witness_sha256"] == witness["sha256"]
    assert marker_payload["result_checkpoint_sha256"] == "b" * 64
    assert marker_payload["context_sha256"] == witness_payload["context_sha256"]
    assert marker_payload["model_names"] == ["fake-model"]
    assert witness_payload["candidate_log_path"] == str(candidate_log)
    assert witness_payload["candidate_start_offset"] == 0
    assert witness_payload["candidate_end_offset"] == 0
    assert witness_payload["candidate_range_sha256"] == hashlib.sha256(
        b""
    ).hexdigest()
    assert witness_payload["candidate_wal_clean"] is True
    for field in (
        "candidate_log_path",
        "candidate_log_device",
        "candidate_log_inode",
        "candidate_start_offset",
        "candidate_end_offset",
        "candidate_range_sha256",
        "candidate_range_bytes",
        "candidate_wal_clean",
    ):
        assert marker_payload[field] == witness_payload[field]
    for name, identity in dependency_identities.items():
        for field in ("path", "sha256", "bytes"):
            key = f"{name}_{field}"
            assert witness_payload[key] == identity[field]
            assert marker_payload[key] == identity[field]
