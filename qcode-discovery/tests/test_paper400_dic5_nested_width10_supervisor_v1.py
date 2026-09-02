from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts import run_paper400_dic5_nested_width10_supervisor_v1 as supervisor


def _config(tmp_path: Path, *, cpus: list[int] | None = None) -> dict:
    selected = [0, 1, 2, 3, 4, 5, 6, 7] if cpus is None else cpus
    return {
        "control_root": str(tmp_path / "control"),
        "run_parent": str(tmp_path),
        "tag": "test",
        "batch_first": 12,
        "batch_last": 15,
        "cpus": selected,
        "max_active_lanes": len(selected),
        "input_files": {},
        "resource_caps": dict(supervisor.RESOURCE_DEFAULTS),
        "disk_policy": {
            "stop_free_bytes": 100,
            "resume_free_bytes": 200,
        },
        "poll_seconds": 1,
        "action_workers": 2,
        "record_sha256": "a" * 64,
    }


def _batch(index: int, cpus: list[int], states: list[str]) -> dict:
    return {
        "batch_index": index,
        "root": f"/runs/batch-{index}",
        "state": "PRESENT",
        "cpus": cpus,
        "lanes": [
            {
                "lane_index": lane,
                "global_leaf_index": index * 4 + lane,
                "cpu": cpu,
                "state": state,
            }
            for lane, (cpu, state) in enumerate(zip(cpus, states, strict=True))
        ],
        "incomplete_action": None,
    }


def _missing(index: int) -> dict:
    return {
        "batch_index": index,
        "root": f"/runs/batch-{index}",
        "state": "MISSING",
        "cpus": [],
        "lanes": [],
        "incomplete_action": None,
    }


def test_plan_reuses_only_cpus_from_pruned_lanes(tmp_path: Path):
    config = _config(tmp_path)
    batches = [
        _batch(12, [0, 1, 2, 3], ["PRUNED"] * 4),
        _batch(13, [4, 5, 6, 7], ["RUNNING"] * 4),
        _missing(14),
        _missing(15),
    ]
    assert supervisor.plan_preparations(
        config, batches, paused=False,
    ) == [(14, [0, 1, 2, 3])]


def test_plan_can_reuse_pruned_lanes_from_different_batches(tmp_path: Path):
    config = _config(tmp_path)
    batches = [
        _batch(12, [0, 1, 2, 3], ["PRUNED", "RUNNING", "RUNNING", "RUNNING"]),
        _batch(13, [4, 5, 6, 7], ["PRUNED", "PRUNED", "PRUNED", "RUNNING"]),
        _missing(14),
        _missing(15),
    ]
    assert supervisor.plan_preparations(
        config, batches, paused=False,
    ) == [(14, [0, 4, 5, 6])]


def test_low_disk_plans_only_checkpoint_stop(tmp_path: Path):
    batches = [
        _batch(12, [0, 1, 2, 3], ["RUNNING", "FINAL", "INACTIVE", "PRUNED"]),
        _batch(13, [4, 5, 6, 7], ["CHECKPOINTED"] * 4),
        _missing(14),
    ]
    assert supervisor.plan_actions(batches, paused=True) == [
        (12, "checkpoint-stop"),
    ]
    assert supervisor.plan_preparations(
        _config(tmp_path), batches, paused=True,
    ) == []


def test_low_disk_running_only_batch_is_checkpointed():
    batches = [_batch(12, [0, 1, 2, 3], ["RUNNING"] * 4)]
    assert supervisor.plan_actions(batches, paused=True) == [
        (12, "checkpoint-stop"),
    ]


@pytest.mark.parametrize(
    ("states", "action"),
    [
        (["FINAL", "RUNNING", "RUNNING", "RUNNING"], "prune-transport"),
        (["PRUNE_INCOMPLETE", "RUNNING", "RUNNING", "RUNNING"], "prune-transport"),
        (["INACTIVE", "RUNNING", "RUNNING", "RUNNING"], "harvest-inactive"),
        (["CHECKPOINTED"] * 4, "resume"),
        (["PREPARED"] * 4, "start"),
    ],
)
def test_normal_action_priority(states: list[str], action: str):
    batch = _batch(12, [0, 1, 2, 3], states)
    assert supervisor.plan_actions([batch], paused=False) == [(12, action)]


def test_incomplete_action_has_priority():
    batch = _batch(12, [0, 1, 2, 3], ["RUNNING"] * 4)
    batch["incomplete_action"] = "checkpoint-stop"
    assert supervisor.plan_actions([batch], paused=False) == [
        (12, "checkpoint-stop"),
    ]


@pytest.mark.parametrize("state", ["POISONED", "START_INCOMPLETE", "TERMINAL_INCOMPLETE"])
def test_fail_closed_lane_state_blocks_scheduling(state: str):
    batch = _batch(12, [0, 1, 2, 3], [state, "RUNNING", "RUNNING", "RUNNING"])
    with pytest.raises(supervisor.SupervisorError, match="fail-closed"):
        supervisor.plan_actions([batch], paused=False)


def test_pid_identity_checks_start_ticks(monkeypatch, tmp_path: Path):
    stat_path = tmp_path / "stat"
    # fields after ')' start at process state (field 3); starttime is offset 19.
    stat_path.write_text("99 (solver name) S " + " ".join(["0"] * 18 + ["12345"]), encoding="ascii")
    original = Path.read_text

    def fake_read_text(path: Path, *args, **kwargs):
        if str(path) == "/proc/99/stat":
            return original(stat_path, *args, **kwargs)
        return original(path, *args, **kwargs)

    monkeypatch.setattr(Path, "read_text", fake_read_text)
    assert supervisor._pid_identity(99, 12345) is True
    assert supervisor._pid_identity(99, 12346) is False


def test_pause_hysteresis(monkeypatch, tmp_path: Path):
    control = tmp_path / "control"
    control.mkdir()
    config = _config(tmp_path)
    config["control_root"] = str(control)
    assert supervisor._pause_state(config, 99) is True
    pause = json.loads((control / supervisor.PAUSE_NAME).read_text())
    assert pause["reason"] == "LOW_DISK"
    assert supervisor._pause_state(config, 150) is True
    assert supervisor._pause_state(config, 200) is False
    assert not (control / supervisor.PAUSE_NAME).exists()


def test_toolchain_preflight_reports_missing_file(monkeypatch, tmp_path: Path):
    missing = tmp_path / "missing"
    monkeypatch.setattr(
        supervisor,
        "TOOL_FILES",
        {"missing": (missing, "0" * 64, True)},
    )
    result = supervisor.preflight_toolchain()
    assert result["valid"] is False
    assert result["failures"]
    assert result["record_sha256"]


def test_status_counts_pruned_as_completed(tmp_path: Path):
    config = _config(tmp_path)
    batches = [
        _batch(12, [0, 1, 2, 3], ["PRUNED"] * 4),
        _batch(13, [4, 5, 6, 7], ["RUNNING"] * 4),
        _missing(14),
        _missing(15),
    ]
    status = supervisor.campaign_status(
        config, batches, paused=False, free_bytes=1234,
    )
    assert status["expected_lane_count"] == 16
    assert status["locally_completed_pruned_lane_count"] == 4
    assert status["running_lane_count"] == 4
    assert status["free_cpu_slots"] == 4
    assert status["locally_complete"] is False
