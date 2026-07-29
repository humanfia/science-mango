import json
from types import SimpleNamespace

import pytest

from evolve.run_evolution import _cap_parallel_evaluations
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    _milp_is_fully_exact,
    _stage1_milp_worker_count,
    evaluate_with_milp,
    run_openevolve,
)
from humanize.reviewer import validate_review


class Reviewer:
    def review(self, _prompt, _round_dir):
        return validate_review({
            "verdict": "continue",
            "summary": "No exact candidate yet.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def test_symplectic_d2_rule_is_exact_but_only_at_two():
    row = {"stage": "symplectic_low_d", "d_is_exact": True, "d": 2}
    assert _milp_is_fully_exact(row)
    row["d"] = 3
    assert not _milp_is_fully_exact(row)


def test_resume_rejects_configuration_drift(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    candidates = repo / "candidates.jsonl"
    candidates.write_text("")
    first = FlowConfig(
        repo_dir=repo,
        run_id="immutable",
        max_rounds=1,
        milp_top=0,
        candidate_file=candidates,
    )
    HumanizeFlow(first, reviewer=Reviewer()).run()

    changed = FlowConfig(
        repo_dir=repo,
        run_id="immutable",
        max_rounds=2,
        milp_top=0,
        candidate_file=candidates,
    )
    with pytest.raises(ValueError, match="different configuration"):
        HumanizeFlow(changed, reviewer=Reviewer()).run()


def test_openevolve_config_and_seed_are_forwarded(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    config_path = repo / "server.yaml"
    seed_path = repo / "seed.py"
    config_path.write_text("parallel_evaluations: 24\n")
    seed_path.write_text("def generate_candidates(*_args): return []\n")
    round_dir = repo / "round"
    round_dir.mkdir()
    captured = {}

    def fake_run(command, **kwargs):
        captured["command"] = command
        captured["kwargs"] = kwargs

    monkeypatch.setattr("humanize.flow.subprocess.run", fake_run)
    config = FlowConfig(
        repo_dir=repo,
        run_id="server-profile",
        max_rounds=1,
        iterations_per_round=25,
        evolution_config=config_path,
        evolution_seed=seed_path,
        max_total_workers=4,
    )
    run_openevolve(config, {"current_round": 0, "last_checkpoint": None}, round_dir)

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
    assert command[command.index("--max-parallel-evaluations") + 1] == "4"
    assert command[command.index("--config") + 1] == str(config_path)
    assert command[command.index("--seed") + 1] == str(seed_path)
    assert captured["kwargs"]["cwd"] == repo


def test_openevolve_resume_runs_one_increment_not_cumulative(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    round_dir = repo / "round-003"
    round_dir.mkdir()
    checkpoint = (
        repo
        / "results/evolution/humanize_incremental/checkpoints/checkpoint_50"
    )
    checkpoint.mkdir(parents=True)
    captured = {}

    def fake_run(command, **kwargs):
        captured["command"] = command
        captured["kwargs"] = kwargs

    monkeypatch.setattr("humanize.flow.subprocess.run", fake_run)
    config = FlowConfig(
        repo_dir=repo,
        run_id="incremental",
        max_rounds=3,
        iterations_per_round=25,
        max_total_workers=2,
    )
    run_openevolve(
        config,
        {"current_round": 2, "last_checkpoint": str(checkpoint)},
        round_dir,
    )

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
    assert command[command.index("--max-parallel-evaluations") + 1] == "2"
    assert command[command.index("--resume") + 1] == str(checkpoint)
    assert captured["kwargs"]["cwd"] == repo


def test_stage1_milp_uses_official_dynamic_fom_target(tmp_path, monkeypatch):
    from evaluation.final_gate import FOM_THRESHOLD

    captured = {}

    def fake_evaluator(*_args, **kwargs):
        captured.update(kwargs)
        return {"d": 16, "d_is_exact": False, "stage": "milp_low_d"}

    monkeypatch.setattr(
        "evaluation.evaluator.evaluate_candidate_milp", fake_evaluator
    )
    monkeypatch.setattr(
        "main.merge_bp_milp_result",
        lambda _candidate, milp_result: dict(milp_result),
    )
    candidate = {
        "ell": 18,
        "m": 10,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
    }
    config = FlowConfig(repo_dir=tmp_path, run_id="dynamic-cutoff")

    evaluate_with_milp(candidate, config)

    assert captured["milp_target_fom"] == FOM_THRESHOLD


@pytest.mark.parametrize(
    ("configured", "cap", "effective"),
    ((6, 4, 4), (1, 4, 1), (24, 4, 4), (6, None, 6)),
)
def test_openevolve_parallel_evaluations_are_capped_not_increased(
    configured, cap, effective,
):
    config = SimpleNamespace(
        evaluator=SimpleNamespace(parallel_evaluations=configured)
    )

    observed = _cap_parallel_evaluations(config, cap)

    assert observed == (configured, effective)
    assert config.evaluator.parallel_evaluations == effective


@pytest.mark.parametrize("invalid", (0, -1, True, 1.5, None))
def test_openevolve_rejects_invalid_configured_worker_count(invalid):
    config = SimpleNamespace(
        evaluator=SimpleNamespace(parallel_evaluations=invalid)
    )
    with pytest.raises(ValueError, match="positive integer"):
        _cap_parallel_evaluations(config, 4)


def test_stage1_milp_workers_obey_shared_budget(tmp_path):
    base = dict(repo_dir=tmp_path, run_id="worker-cap")
    assert _stage1_milp_worker_count(FlowConfig(**base), 9) == 3
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=2), 9
    ) == 2
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=8), 2
    ) == 2
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=1), 0
    ) == 0


def test_worker_budget_does_not_break_legacy_checkpoint_identity(tmp_path):
    base = FlowConfig(repo_dir=tmp_path, run_id="resume-compatible")
    capped = FlowConfig(
        repo_dir=tmp_path,
        run_id="resume-compatible",
        max_total_workers=4,
    )
    assert capped.serializable() == base.serializable()
