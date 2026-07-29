from __future__ import annotations

import json
from pathlib import Path

import pytest

from humanize.pipeline import PipelineConfig


def _load_config(tmp_path: Path, values: dict) -> PipelineConfig:
    config_path = tmp_path / "pipeline.json"
    payload = {
        "run_id": "config-types",
        "candidate_inputs": ["candidates.jsonl"],
        **values,
    }
    config_path.write_text(json.dumps(payload) + "\n")
    return PipelineConfig.from_json(config_path, repo_dir=tmp_path)


@pytest.mark.parametrize(
    ("values", "field"),
    [
        ({"stage2": {"top": True}}, "stage2_top"),
        ({"stage2": {"timeout": False}}, "stage2_timeout"),
        ({"stage2": {"candidate_workers": True}}, "stage2_candidate_workers"),
        ({"stage2": {"solver_workers": False}}, "stage2_solver_workers"),
        ({"stage3": {"top": True}}, "stage3_top"),
        ({"stage3": {"top": False}}, "stage3_top"),
        ({"stage3": {"timeout": True}}, "stage3_timeout"),
        ({"stage3": {"candidate_workers": False}}, "stage3_candidate_workers"),
        ({"stage3": {"direction_workers": True}}, "stage3_direction_workers"),
        ({"certificate": {"workers": True}}, "certificate_workers"),
        (
            {"certificate": {"solver_workers": False}},
            "certificate_solver_workers",
        ),
        (
            {"certificate": {"timeout_per_logical": True}},
            "certificate_timeout_per_logical",
        ),
        (
            {"certificate": {"total_timeout": False}},
            "certificate_total_timeout",
        ),
        (
            {"certificate": {"verification_timeout_per_logical": True}},
            "verification_timeout_per_logical",
        ),
        (
            {"certificate": {"verification_total_timeout": False}},
            "verification_total_timeout",
        ),
        ({"max_total_workers": True}, "max_total_workers"),
        ({"proof_retry": {"max_attempts": True}}, "proof_retry_max_attempts"),
        (
            {"proof_retry": {"max_multiplier": False}},
            "proof_retry_max_multiplier",
        ),
        (
            {"proof_retry": {"campaign_total_timeout": True}},
            "proof_retry_campaign_total_timeout",
        ),
        (
            {"proof_retry": {"backoff_seconds": False}},
            "proof_retry_backoff_seconds",
        ),
        (
            {"strict": {"timeout_per_logical": True}},
            "known_answer_timeout_per_logical",
        ),
        (
            {"strict": {"total_timeout": False}},
            "known_answer_total_timeout",
        ),
    ],
)
def test_pipeline_json_rejects_bool_for_numeric_fields(
    tmp_path: Path,
    values: dict,
    field: str,
):
    with pytest.raises(ValueError, match=rf"^{field} must not be boolean$"):
        _load_config(tmp_path, values)


def test_pipeline_json_accepts_integral_numeric_budgets(tmp_path: Path):
    config = _load_config(
        tmp_path,
        {
            "stage2": {
                "top": 21,
                "timeout": 31,
                "candidate_workers": 2,
                "solver_workers": 3,
            },
            "stage3": {
                # Stage 3 is exhaustive within the bounded Stage 2 page.
                "top": 0,
                "timeout": 32,
                "candidate_workers": 1,
                "direction_workers": 6,
            },
            "certificate": {
                "workers": 1,
                "solver_workers": 6,
                "timeout_per_logical": 33,
                "total_timeout": 34,
                "verification_timeout_per_logical": 35,
                "verification_total_timeout": 36,
            },
            "max_total_workers": 6,
            "proof_retry": {
                "max_attempts": 7,
                "max_multiplier": 8,
                "campaign_total_timeout": 37,
                "backoff_seconds": 0,
            },
            "strict": {
                "timeout_per_logical": 38,
                "total_timeout": 39,
            },
        },
    )

    assert config.stage2_top == 21
    assert config.stage3_top == 0
    assert config.proof_retry_max_attempts == 7
    assert config.max_total_workers == 6
    assert config.certificate_timeout_per_logical == 33.0
    assert config.proof_retry_backoff_seconds == 0.0
    assert config.known_answer_total_timeout == 39


def test_pipeline_json_preserves_numeric_string_compatibility(tmp_path: Path):
    config = _load_config(
        tmp_path,
        {
            "stage2": {"top": "3", "timeout": "12.5"},
            "proof_retry": {"max_attempts": "4", "backoff_seconds": "0"},
        },
    )

    assert config.stage2_top == 3
    assert config.stage2_timeout == 12.5
    assert config.proof_retry_max_attempts == 4
    assert config.proof_retry_backoff_seconds == 0.0


@pytest.mark.parametrize("not_finite", [float("nan"), "NaN"])
def test_pipeline_json_still_rejects_nan_budget(
    tmp_path: Path,
    not_finite: float | str,
):
    with pytest.raises(ValueError, match="stage2_timeout must be positive and finite"):
        _load_config(tmp_path, {"stage2": {"timeout": not_finite}})


@pytest.mark.parametrize(
    ("field", "message"),
    [
        (
            "stage2_top",
            "stage2_top must be a positive integer so every proof page can advance",
        ),
        (
            "stage3_top",
            (
                "stage3_top must be 0: Stage 3 must audit every unresolved "
                "candidate in the bounded current Stage 2 page"
            ),
        ),
    ],
)
def test_direct_pipeline_config_rejects_bool_top(
    tmp_path: Path,
    field: str,
    message: str,
):
    values = {
        "repo_dir": tmp_path,
        "run_id": "direct-config-types",
        "candidate_inputs": (tmp_path / "candidates.jsonl",),
        field: True,
    }

    with pytest.raises(ValueError, match=rf"^{message}$"):
        PipelineConfig(**values)
