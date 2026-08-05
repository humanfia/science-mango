from __future__ import annotations

import hashlib
from pathlib import Path
from types import SimpleNamespace

import pytest
from openevolve.database import Program

from evolve import run_evolution as launcher
from evolve import coset_policy_dsl as policy_dsl
from evolve.coset_policy_dsl import (
    canonical_policy_json,
    default_policy,
    parse_policy,
)
from humanize import flow as flow_module


def _legacy_database(code: str) -> SimpleNamespace:
    program = Program(
        id="legacy-program",
        code=code,
        metrics={
            "map_descriptor_version": 4.0,
            "qcode_evaluator_kind_id": 1.0,
            "qcode_action_catalog_id": float(
                launcher._coset_action_catalog_contract_id()
            ),
        },
        metadata={"island": 0},
    )
    return SimpleNamespace(
        config=SimpleNamespace(num_islands=4),
        programs={program.id: program},
        last_iteration=150,
        current_island=0,
        island_generations=[1, 2, 3, 4],
        last_migration_generation=99,
        islands=[{program.id}, set(), set(), set()],
        island_feature_maps=[{} for _ in range(4)],
        archive={program.id},
        best_program_id=program.id,
        island_best_programs=[program.id, None, None, None],
        feature_stats={"stale": {}},
        diversity_cache={1: {}},
        diversity_reference_set=[code],
        _calculate_feature_coords=lambda _program: [0, 0, 0],
    )


def _source_descriptor(database: SimpleNamespace) -> dict:
    return {
        "path": "/sealed/checkpoint_150",
        "last_iteration": 150,
        "sha256": "a" * 64,
        "programs": len(database.programs),
    }


def test_legacy_checkpoint_epoch_never_executes_old_python(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
):
    sentinel = tmp_path / "legacy-executed"
    legacy = (
        "from pathlib import Path\n"
        f"Path({str(sentinel)!r}).write_text('bad')\n"
        "import evolve.coset_openevolve_evaluator as target\n"
        "target._fitness = lambda row: 1.0\n"
        "raise RuntimeError('must never run')\n"
    )
    database = _legacy_database(legacy)
    source = _source_descriptor(database)

    def evaluated(_path, code, **_kwargs):
        parse_policy(code)
        return (
            {launcher.COSET_GENOME_FORMAT_ID_METRIC: 1.0},
            {"trusted": "artifact"},
            {
                "path": str(tmp_path / "all_codes.jsonl"),
                "start_offset": 10,
                "end_offset": 20,
                "sha256": "b" * 64,
                "bytes": 10,
                "wal_clean": True,
            },
        )

    monkeypatch.setattr(
        launcher,
        "_execute_coset_checkpoint_root_evaluation",
        evaluated,
    )
    monkeypatch.setattr(
        launcher,
        "_rebuild_fixed_search_feature_maps",
        lambda *_args, **_kwargs: None,
    )

    report = launcher._install_coset_checkpoint_dsl_epoch(
        database,
        source_checkpoint=source,
        evaluator_path=tmp_path / "evaluator.py",
        expected_contract_id=123,
        wall_timeout=5.0,
        search_portfolio_schema_version=None,
    )

    assert not sentinel.exists()
    assert database.last_iteration == 150
    assert len(database.programs) == 1
    root = next(iter(database.programs.values()))
    assert root.id == report["root_program_id"]
    assert root.parent_id is None
    assert root.iteration_found == 150
    assert root.language == "json"
    assert parse_policy(root.code) == default_policy()
    assert report["source_checkpoint"] == source
    assert report["source_programs"] == 1
    assert report["target_programs"] == 1
    assert report["root_code_sha256"] == hashlib.sha256(
        root.code.encode("utf-8")
    ).hexdigest()
    assert database.archive == {root.id}


def test_mixed_checkpoint_is_rejected_before_any_evaluation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
):
    database = _legacy_database("def generate_candidates(): return []\n")
    policy_code = canonical_policy_json(default_policy()) + "\n"
    database.programs["dsl"] = Program(
        id="dsl",
        code=policy_code,
        metrics={launcher.COSET_GENOME_FORMAT_ID_METRIC: 1.0},
    )
    called = False

    def evaluated(*_args, **_kwargs):
        nonlocal called
        called = True
        raise AssertionError("evaluation must not start")

    monkeypatch.setattr(
        launcher,
        "_execute_coset_checkpoint_root_evaluation",
        evaluated,
    )
    with pytest.raises(RuntimeError, match="mixes legacy Python"):
        launcher._install_coset_checkpoint_dsl_epoch(
            database,
            source_checkpoint={
                **_source_descriptor(database),
                "programs": 2,
            },
            evaluator_path=tmp_path / "evaluator.py",
            expected_contract_id=123,
            wall_timeout=5.0,
            search_portfolio_schema_version=None,
        )
    assert called is False


def test_typed_checkpoint_requires_every_genome_marker():
    code = canonical_policy_json(default_policy()) + "\n"
    database = SimpleNamespace(programs={
        "valid": Program(
            id="valid",
            code=code,
            metrics={launcher.COSET_GENOME_FORMAT_ID_METRIC: 1.0},
        )
    })
    assert launcher._strict_coset_checkpoint_genome_kind(database) == (
        "typed-json-dsl"
    )
    launcher._validate_typed_coset_checkpoint_programs(database)
    database.programs["valid"].metrics.clear()
    with pytest.raises(RuntimeError, match="lacks its genome marker"):
        launcher._validate_typed_coset_checkpoint_programs(database)


def test_typed_checkpoint_rejects_duplicate_policy_genomes():
    code = canonical_policy_json(default_policy()) + "\n"
    database = SimpleNamespace(programs={
        program_id: Program(
            id=program_id,
            code=code,
            metrics={launcher.COSET_GENOME_FORMAT_ID_METRIC: 1.0},
        )
        for program_id in ("duplicate-a", "duplicate-b")
    })

    with pytest.raises(RuntimeError, match="duplicate policy genomes"):
        launcher._validate_typed_coset_checkpoint_programs(database)


def test_historical_root_replay_does_not_depend_on_live_dsl_catalog(
    monkeypatch: pytest.MonkeyPatch,
):
    policy = default_policy()
    code = canonical_policy_json(policy) + "\n"
    catalog_sha256 = policy.action_catalog_sha256
    expected_policy_sha256 = policy_dsl.policy_digest(policy)

    monkeypatch.setattr(policy_dsl, "_catalog_sha256", lambda: "0" * 64)
    with pytest.raises(policy_dsl.CosetPolicyError, match="catalog binding"):
        policy_dsl.parse_policy(code)

    identity = flow_module._historical_coset_policy_v1_identity(
        code,
        expected_catalog_sha256=catalog_sha256,
    )

    assert identity["policy_sha256"] == expected_policy_sha256
    assert identity["code_sha256"] == hashlib.sha256(
        code.encode("utf-8")
    ).hexdigest()
