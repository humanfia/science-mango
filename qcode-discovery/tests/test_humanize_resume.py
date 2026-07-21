import json

import pytest

from humanize.flow import FlowConfig, HumanizeFlow
from humanize.reviewer import ReviewError, validate_review


def candidate():
    return {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 12,
        "d": 6,
        "fom": 6.0,
        "score": 6.0,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }


class FlakyReviewer:
    def __init__(self):
        self.calls = 0

    def review(self, _prompt, _round_dir):
        self.calls += 1
        if self.calls == 1:
            raise ReviewError("simulated reviewer outage")
        return validate_review({
            "verdict": "promote",
            "summary": "Recovered review accepted the persisted audit.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def test_reviewer_failure_resumes_without_repeating_milp(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_text(json.dumps(candidate()) + "\n")
    config = FlowConfig(
        repo_dir=repo,
        run_id="resume-review",
        max_rounds=1,
        milp_top=1,
        candidate_file=source,
    )
    counter = {"milp": 0}

    def milp(row, _config):
        counter["milp"] += 1
        result = dict(row)
        result.update({
            "milp_attempted": True,
            "stage": "milp_incumbent",
            "d_is_exact": False,
            "milp_details": {
                "exact": False,
                "total_logicals": 24,
                "num_logicals_checked": 4,
                "logicals_optimal": 4,
            },
        })
        return result

    reviewer = FlakyReviewer()
    flow = HumanizeFlow(config, reviewer=reviewer, milp_evaluator=milp)
    with pytest.raises(ReviewError, match="outage"):
        flow.run()

    failed = json.loads(
        (repo / "results/humanize/resume-review/state.json").read_text()
    )
    assert failed["round_phase"] == "review"
    assert failed["pending_round"] == 1
    assert counter["milp"] == 1

    completed = HumanizeFlow(
        config, reviewer=reviewer, milp_evaluator=milp
    ).run()
    assert completed["status"] == "search-complete"
    assert counter["milp"] == 1
    evaluations = (
        repo / "results/runs/resume-review/evaluations.jsonl"
    ).read_text().splitlines()
    assert len(evaluations) == 1
