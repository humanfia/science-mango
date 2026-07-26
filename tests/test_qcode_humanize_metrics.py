import json

from archon.commands.qcode_metrics import compute_metrics


def test_humanize_metrics_report_rounds_and_elite_cells(tmp_path):
    run_id = "humanized"
    run_dir = tmp_path / "results" / "runs" / run_id
    state_dir = tmp_path / "results" / "humanize" / run_id
    run_dir.mkdir(parents=True)
    state_dir.mkdir(parents=True)
    state_path = state_dir / "state.json"
    state_path.write_text(json.dumps({"no_improvement_rounds": 1}))
    (state_dir / "elite-archive.json").write_text(json.dumps({
        "cells": {"cell-a": {}, "cell-b": {}},
    }))
    (run_dir / "run_meta.json").write_text(json.dumps({
        "status": "search-complete",
        "humanize": True,
        "rounds_completed": 2,
        "state_path": str(state_path),
        "config": {
            "max_rounds": 5,
            "model": "gpt-5.5",
            "review_model": "gpt-5.5",
            "reasoning_effort": "xhigh",
            "review_effort": "xhigh",
        },
    }))

    metrics = compute_metrics(repo_dir=tmp_path, run_id=run_id)
    assert metrics["coverage"]["unit"] == "rlcr_rounds"
    assert metrics["coverage"]["completed_lattices"] == 2
    assert metrics["coverage"]["expected_lattices"] == 5
    assert metrics["humanize"] == {
        "enabled": True,
        "rounds_completed": 2,
        "unique_elite_cells": 2,
        "no_improvement_rounds": 1,
        "search_model": "gpt-5.5",
        "review_model": "gpt-5.5",
        "reasoning_effort": "xhigh",
        "review_effort": "xhigh",
    }
