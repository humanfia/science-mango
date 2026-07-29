"""Direction-level process hard-wall regression tests for Stage 3."""

from __future__ import annotations

import json
import os
import signal
from pathlib import Path

import pytest

import scripts.screen_frontier_candidate as frontier


pytestmark = pytest.mark.skipif(
    not hasattr(signal, "SIGKILL"),
    reason="proof hard-wall tests require POSIX process signals",
)


def _partial_or_hang(payload):
    position, _timeout, _max_weight = payload
    if position == 0:
        return {
            "position": 0,
            "logical_index": 0,
            "success": False,
            "status": 1,
            "objective": None,
            "operator": None,
        }
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    pid_dir = os.environ["QCODE_STAGE3_TEST_PID_DIR"]
    Path(pid_dir, f"{os.getpid()}.pid").write_text(str(os.getpid()))
    while True:
        signal.pause()


def _candidate() -> dict:
    return {
        "source": "hard-wall-test",
        "ell": 6,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
        "n": 72,
        "k": 12,
        "required_distance": 7,
        "canonical_digest": "hard-wall-candidate",
    }


def test_direction_hard_wall_retains_completed_direction_and_reaps(
    tmp_path, monkeypatch,
):
    pid_dir = tmp_path / "stage3-pids"
    pid_dir.mkdir()
    monkeypatch.setenv("QCODE_STAGE3_TEST_PID_DIR", str(pid_dir))
    monkeypatch.setattr(frontier, "solve_position", _partial_or_hang)
    monkeypatch.setattr(
        frontier,
        "order_direction_positions",
        lambda _candidate, _code: list(range(24)),
    )
    output = tmp_path / "stage3.json"

    artifact = frontier.screen_candidate(
        _candidate(),
        output=output,
        timeout=0.05,
        workers=2,
        threshold_only=True,
        resume=False,
        hard_timeout=0.2,
        candidate_timeout=1,
        termination_grace=0.05,
    )

    assert artifact["status"] == "UNRESOLVED"
    assert artifact["completed_directions"] == 1
    assert artifact["hard_wall"]["timed_out"] is True
    assert json.loads(output.read_text())["completed_directions"] == 1
    pids = [int(path.read_text()) for path in pid_dir.glob("*.pid")]
    assert pids
    for pid in pids:
        with pytest.raises(ProcessLookupError):
            os.kill(pid, 0)
