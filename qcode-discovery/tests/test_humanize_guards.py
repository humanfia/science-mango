import json

import pytest

from humanize.flow import (
    FlowConfig, HumanizeFlow, _milp_is_fully_exact, run_openevolve,
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
    )
    run_openevolve(config, {"current_round": 0, "last_checkpoint": None}, round_dir)

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
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
    )
    run_openevolve(
        config,
        {"current_round": 2, "last_checkpoint": str(checkpoint)},
        round_dir,
    )

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
    assert command[command.index("--resume") + 1] == str(checkpoint)
    assert captured["kwargs"]["cwd"] == repo
