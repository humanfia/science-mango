"""Contract tests for the IChO shared-chemistry module scaffolder."""

from __future__ import annotations

import json
from pathlib import Path

from archon.prompts import _subagent_catalog_block
from archon.commands.tooling.project_config import default_config
from archon.subagents.registry import build_registry


NAME = "chemistry-module-refactor"


def test_descriptor_is_opt_in_plan_scaffolder(tmp_path: Path) -> None:
    registry = build_registry(tmp_path, enabled=[NAME])

    assert registry.names() == [NAME]
    descriptor = registry[NAME]
    assert descriptor.write_domain == "IChO2026Chem/**"
    assert descriptor.is_mandatory_for("plan")
    assert not descriptor.is_mandatory_for("review")
    assert not descriptor.default_enabled
    assert not descriptor.read_only
    assert not descriptor.can_spawn


def test_descriptor_enforces_two_stage_consumer_migration_contract(
    tmp_path: Path,
) -> None:
    descriptor = build_registry(tmp_path, enabled=[NAME])[NAME]
    prompt = descriptor.prompt_body

    assert "project_local_shared_module" in prompt
    assert "minimal request schema" in prompt
    assert "IChO2026Chem/" in prompt
    assert "Do not touch consumers" in prompt
    assert "BLOCKED UNTIL SHARED MODULE VERIFIED" in prompt
    assert "mathlib-build" in prompt
    assert "lakefile.toml" in prompt
    assert "Do not invent chemical facts" in prompt
    assert ".archon/task_results/chemistry-module-refactor-<slug>.md" in prompt
    assert ".humanizephysics" not in prompt
    assert "humanizephysics-protected.yaml" not in prompt


def test_enabled_descriptor_is_visible_to_plan_catalog(tmp_path: Path) -> None:
    state_dir = tmp_path / ".archon"
    state_dir.mkdir()
    (state_dir / "config.json").write_text(
        json.dumps({"subagents": {"enabled": [NAME]}}),
        encoding="utf-8",
    )

    catalog = _subagent_catalog_block(tmp_path, role="plan")

    assert f"**{NAME}**" in catalog
    assert "HIGHLY RECOMMENDED" in catalog
    assert "IChO2026Chem/**" in catalog
    assert "project_local_shared_module" in catalog


def test_descriptor_remains_disabled_without_opt_in(tmp_path: Path) -> None:
    assert NAME not in build_registry(tmp_path)


def test_default_config_advertises_safe_opt_in() -> None:
    config = default_config()

    assert NAME in config["subagents"]["_available"]
    assert "chemistry-reviewer" in config["subagents"]["_available"]
    assert config["loop"]["shared_infrastructure"] == {
        "enabled": False,
        "module_roots": [],
        "scaffolder": "lean-scaffolder",
        "migration_refactor": "refactor",
    }
