import json

import pytest

from humanize.flow import FlowConfig, HumanizeFlow, _milp_is_fully_exact
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
