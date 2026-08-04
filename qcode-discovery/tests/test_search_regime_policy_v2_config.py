"""Configuration compatibility for opt-in search-regime policy v2."""

from __future__ import annotations

import json
from pathlib import Path

from humanize.escalation import load_template_registry
from humanize.pipeline import PipelineConfig


PROJECT = Path(__file__).resolve().parents[1]
CONFIGS = PROJECT / "configs"


def test_auto_v2_campaign_explicitly_opts_into_terminal_handoff():
    path = CONFIGS / "five_stage_campaign.cover_algebra.auto_v2.json"
    raw = json.loads(path.read_text())
    config = PipelineConfig.from_json(path, repo_dir=PROJECT)

    assert raw["run_id"] == "qcode-cover-algebra-auto-v2"
    assert raw["resume"] is True
    assert config.flow_config is not None
    assert config.flow_config.search_representation_id == (
        "css-bb-cover-algebra-generator-v2"
    )
    assert config.flow_config.search_regime_policy_version == 2
    assert config.flow_config.stop_on_representation_change is True


def test_auto_v3_campaign_closes_budget_into_proof_compatible_ansatz():
    path = CONFIGS / "five_stage_campaign.cover_algebra.auto_v3.json"
    raw = json.loads(path.read_text())
    config = PipelineConfig.from_json(path, repo_dir=PROJECT)

    assert raw["run_id"] == "qcode-cover-algebra-auto-v3"
    assert raw["resume"] is True
    assert config.flow_config is not None
    config.flow_config.validate()
    assert config.flow_config.max_rounds == 12
    assert config.flow_config.search_representation_id == (
        "css-bb-cover-algebra-generator-v2"
    )
    assert config.flow_config.search_regime_policy_version == 3
    assert config.flow_config.stop_on_representation_change is True
    assert raw["auto_escalation"]["template_by_regime"] == {
        "representation_change_required": (
            "css-bb-novel-ansatz-generator-v2"
        )
    }

    template = load_template_registry(repo_dir=PROJECT).template(
        "css-bb-novel-ansatz-generator-v2"
    )
    assert template.transition_kind == "representation_change"
    assert template.proof_compatible is True
    assert template.launch_compatible is True
    assert template.auto_materialize is True


def test_ansatz_child_base_is_immutable_resume_template_without_parent_policy():
    path = CONFIGS / "five_stage_campaign.ansatz_child_v2.json"
    raw = json.loads(path.read_text())
    config = PipelineConfig.from_json(path, repo_dir=PROJECT)

    assert raw["resume"] is True
    assert "auto_escalation" not in raw
    assert "stop_on_representation_change" not in raw["stage1"]
    assert config.flow_config is not None
    assert config.flow_config.search_representation_id == (
        "css-bb-novel-ansatz-generator-v2"
    )
    assert config.flow_config.search_regime_policy_version == 2
    assert config.flow_config.stop_on_representation_change is False


def test_existing_cover_campaigns_remain_implicit_policy_v1():
    names = (
        "five_stage_campaign.cover_algebra.json",
        "five_stage_campaign.cover_algebra.proof_fix_v1.json",
        "five_stage_campaign.cover_algebra.twobga_v1.json",
    )
    for name in names:
        path = CONFIGS / name
        raw = json.loads(path.read_text())
        assert "search_regime_policy_version" not in raw.get("stage1", {})
        assert "stop_on_representation_change" not in raw.get("stage1", {})

        config = PipelineConfig.from_json(path, repo_dir=PROJECT)
        assert config.flow_config is not None
        assert config.flow_config.search_regime_policy_version == 1
        assert config.flow_config.stop_on_representation_change is False
        serialized = config.flow_config.serializable()
        assert "search_regime_policy_version" not in serialized
        assert "stop_on_representation_change" not in serialized
