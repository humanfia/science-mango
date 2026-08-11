from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from evolve import coset_negative_archive as archive
from humanize.flow import FlowConfig
from humanize.pipeline import (
    FiveStagePipeline,
    PipelineConfig,
    PipelineError,
    _canonical_sha256,
)


def _write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def _pipeline(tmp_path: Path, run_id: str) -> tuple[FiveStagePipeline, FlowConfig]:
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidates = repo / "candidate-output.jsonl"
    candidates.write_text("{}\n", encoding="utf-8")
    flow = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidates,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    pipeline = FiveStagePipeline(PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow,
        stage_review=False,
    ))
    pipeline.config.root.mkdir(parents=True)
    pipeline._load_or_initialize_state()
    return pipeline, flow


def _record_attempt(
    pipeline: FiveStagePipeline,
    effective: FlowConfig,
    startup: dict,
) -> None:
    command = ["internal:HumanizeFlow.run", effective.run_id]
    stage_config = {
        "mode": "humanize-flow",
        "flow_config": effective.serializable(),
        "negative_feedback_startup": startup,
    }
    pipeline.state["stages"]["stage1_search"].update({
        "status": "FAILED",
        "machine_status": "FAILED",
        "command": command,
        "command_sha256": _canonical_sha256(command),
        "stage_config": stage_config,
        "stage_fingerprint": pipeline._stage_config_fingerprint(
            command,
            stage_config,
        ),
    })


def _complete_base_flow(flow: FlowConfig) -> Path:
    state_path = (
        flow.repo_dir
        / "results"
        / "humanize"
        / flow.run_id
        / "state.json"
    )
    _write_json(state_path, {
        "status": "search-complete",
        "config": flow.serializable(),
        "pending_round": None,
    })
    return state_path


@pytest.mark.parametrize("prepared_present", [True, False])
def test_stranded_epoch1_resumes_only_its_cross_bound_attempt(
    tmp_path: Path,
    prepared_present: bool,
) -> None:
    pipeline, base = _pipeline(tmp_path, f"stranded-e1-{prepared_present}")
    effective, startup = pipeline._prepare_stage1_feedback_epoch(base)
    assert effective.run_id == base.run_id
    assert startup["feedback_epoch"] == 1
    _record_attempt(pipeline, effective, startup)
    _complete_base_flow(base)
    if not prepared_present:
        pipeline.state.pop("negative_feedback_prepared")

    resumed, resumed_startup = pipeline._prepare_stage1_feedback_epoch(base)

    assert resumed.run_id == base.run_id
    assert resumed_startup == startup
    assert pipeline.state["negative_feedback_prepared"]["startup"] == startup


def test_stranded_epoch1_attempt_wins_over_shadow_cache_recovery(
    tmp_path: Path,
) -> None:
    pipeline, base = _pipeline(tmp_path, "stranded-e1-shadow-orphan")
    effective, startup = pipeline._prepare_stage1_feedback_epoch(base)
    _record_attempt(pipeline, effective, startup)
    _complete_base_flow(base)
    pipeline.state.pop("negative_feedback_prepared")

    live = Path(startup["live_archive_path"])
    current_archive = archive.load_archive(live)
    pipeline._materialize_pending_feedback_record(
        live_archive_path=live,
        archive=current_archive,
        pending_epoch=1,
        source_stage="stage1-cache-recovery",
        events_added=0,
    )
    shadow_run_id = pipeline._feedback_epoch_run_id(
        base.run_id,
        feedback_epoch=1,
        archive_sha256=current_archive["archive_sha256"],
        initial=False,
    )
    assert shadow_run_id != base.run_id
    shadow = replace(base, run_id=shadow_run_id)
    shadow_round = (
        base.repo_dir
        / "results"
        / "humanize"
        / shadow_run_id
        / "rounds"
        / "round-001"
    )
    archive.materialize_feedback_snapshot(
        live,
        shadow_round / "negative-feedback-snapshot.json",
        shadow_round / "negative-feedback-snapshot-manifest.json",
        run_id=shadow_run_id,
        round_number=1,
        feedback_epoch=1,
    )
    _write_json(
        shadow_round.parent.parent / "state.json",
        {
            "status": "search-complete",
            "config": shadow.serializable(),
            "pending_round": None,
        },
    )

    resumed, resumed_startup = pipeline._prepare_stage1_feedback_epoch(base)

    assert resumed.run_id == base.run_id
    assert resumed_startup == startup
    assert pipeline.state["negative_feedback_prepared"]["startup"] == startup


def test_preexisting_terminal_base_flow_keeps_normal_epoch2(
    tmp_path: Path,
) -> None:
    pipeline, base = _pipeline(tmp_path, "normal-derived-e2")
    _complete_base_flow(base)

    derived, startup = pipeline._prepare_stage1_feedback_epoch(base)
    resumed, resumed_startup = pipeline._prepare_stage1_feedback_epoch(base)

    assert startup["feedback_epoch"] == 2
    assert derived.run_id != base.run_id
    assert resumed.run_id == derived.run_id
    assert resumed_startup == startup


@pytest.mark.parametrize("tamper", ["base-config", "stage-fingerprint"])
def test_stranded_epoch1_cross_binding_tamper_fails_closed(
    tmp_path: Path,
    tamper: str,
) -> None:
    pipeline, base = _pipeline(tmp_path, f"stranded-e1-{tamper}")
    effective, startup = pipeline._prepare_stage1_feedback_epoch(base)
    _record_attempt(pipeline, effective, startup)
    base_state_path = _complete_base_flow(base)
    if tamper == "base-config":
        base_state = json.loads(base_state_path.read_text(encoding="utf-8"))
        base_state["config"]["max_rounds"] += 1
        _write_json(base_state_path, base_state)
    else:
        pipeline.state["stages"]["stage1_search"][
            "stage_fingerprint"
        ] = "0" * 64

    with pytest.raises(
        PipelineError,
        match="prepared Stage 1 feedback identity changed",
    ) as failure:
        pipeline._prepare_stage1_feedback_epoch(base)

    assert failure.value.classification == "STAGE1_FEEDBACK_INVALID"
