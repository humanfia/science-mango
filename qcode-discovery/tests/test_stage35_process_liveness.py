"""End-to-end process-liveness regressions for the Stage 3/5 proof lanes."""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

import humanize.pipeline as pipeline_module
from evaluation.process_hard_wall import (
    IsolatedCallOutcome,
    run_isolated_call,
)
from humanize.pipeline import default_command_runner
from scripts import finalize_challenge as finalizer
from scripts.audit_direction_pool import (
    direction_state_path,
    screen_selected_candidates,
    validate_worker_budget,
)
from tests._process_hang_helpers import (
    fork_child_then_exit,
    fork_child_then_return,
    hang_with_group_child,
    stage3_hang_or_complete,
    stage5_hang_or_accept,
    strict_integrity_hang,
)


pytestmark = pytest.mark.skipif(
    not hasattr(os, "killpg") or not hasattr(signal, "SIGKILL"),
    reason="proof hard-wall tests require POSIX process groups",
)


def _process_is_running(pid: int) -> bool:
    try:
        stat_line = Path(f"/proc/{pid}/stat").read_text()
    except FileNotFoundError:
        return False
    except OSError:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        return True
    state = stat_line[stat_line.rindex(")") + 2 :].split()[0]
    return state not in {"Z", "X"}


def _assert_process_stopped(pid: int) -> None:
    deadline = time.monotonic() + 2
    while _process_is_running(pid) and time.monotonic() < deadline:
        time.sleep(0.01)
    assert not _process_is_running(pid), f"process {pid} is still running"


def _candidate(digest: str) -> dict:
    return {
        "source": "process-liveness-test",
        "ell": 6,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
        "n": 72,
        "k": 12,
        "required_distance": 7,
        "canonical_digest": digest,
    }


def _certificate(index: int, *, digest: str | None = None) -> dict:
    return {
        "certificate_type": "qldpc-css-bb-exact",
        "certificate_sha256": digest or f"certificate-{index}",
        "claim": {"n": 72 + index, "k": 12, "d": 7},
    }


def _finalizer_args(tmp_path: Path, certificates: list[dict]) -> argparse.Namespace:
    claims = tmp_path / "claims.json"
    claims.write_text(json.dumps(certificates) + "\n")
    known_answer = tmp_path / "known-answer.json"
    known_answer.write_text('{"passed": true}\n')
    trust = tmp_path / "known-answer-trust.json"
    trust.write_text('{"schema_version": 1}\n')
    return argparse.Namespace(
        claims=claims,
        known_answer_artifact=known_answer,
        known_answer_trust=trust,
        known_answer_timeout_per_logical=1,
        known_answer_total_timeout=1,
        verification_timeout_per_logical=1.0,
        verification_total_timeout=6.0,
        verification_solver_workers=1,
        verification_state_dir=tmp_path / "verification-state",
        resume=True,
        output=tmp_path / "final-gate.json",
    )


def test_isolated_call_kills_exact_group_and_preserves_checkpoint(tmp_path):
    parent_pid = tmp_path / "parent.pid"
    child_pid = tmp_path / "child.pid"
    checkpoint = tmp_path / "checkpoint.json"
    sentinel = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(30)"],
        start_new_session=True,
    )
    try:
        outcome = run_isolated_call(
            hang_with_group_child,
            args=(str(parent_pid), str(child_pid), str(checkpoint)),
            timeout_s=2.5,
            termination_grace_s=0.05,
        )
        assert outcome.status == "timeout"
        assert outcome.hard_wall["timed_out"] is True
        assert outcome.hard_wall["forced"] is True
        assert checkpoint.read_text() == '{"completed": 1}\n'
        for path in (parent_pid, child_pid):
            _assert_process_stopped(int(path.read_text()))
        assert sentinel.poll() is None
    finally:
        sentinel.kill()
        sentinel.wait()


def test_isolated_call_cleans_descendant_after_valid_result(tmp_path):
    child_pid_path = tmp_path / "result-child.pid"

    outcome = run_isolated_call(
        fork_child_then_return,
        args=(str(child_pid_path),),
        timeout_s=3,
        termination_grace_s=0.05,
    )

    assert outcome.status == "completed"
    assert outcome.value == {"proof": "complete"}
    assert outcome.hard_wall["descendant_cleanup"] is True
    assert outcome.hard_wall["forced"] is True
    _assert_process_stopped(int(child_pid_path.read_text()))


def test_isolated_call_cleans_descendant_after_abrupt_leader_exit(tmp_path):
    child_pid_path = tmp_path / "error-child.pid"

    outcome = run_isolated_call(
        fork_child_then_exit,
        args=(str(child_pid_path),),
        timeout_s=3,
        termination_grace_s=0.05,
    )

    assert outcome.status == "error"
    assert "exitcode=17" in outcome.error
    assert outcome.hard_wall["descendant_cleanup"] is True
    assert outcome.hard_wall["forced"] is True
    _assert_process_stopped(int(child_pid_path.read_text()))


@pytest.mark.parametrize("candidate_workers", [1, 2])
def test_stage3_submit_wall_retains_progress_and_runs_peer(
    tmp_path,
    monkeypatch,
    candidate_workers,
):
    pid_dir = tmp_path / "pids"
    pid_dir.mkdir()
    monkeypatch.setenv("QCODE_STAGE35_PID_DIR", str(pid_dir))
    selected = [
        ("hang-candidate", _candidate("hang-candidate")),
        ("peer-candidate", _candidate("peer-candidate")),
    ]

    started = time.monotonic()
    results = screen_selected_candidates(
        selected,
        tmp_path / "state",
        timeout=30,
        candidate_workers=candidate_workers,
        direction_workers=1,
        threshold_only=True,
        resume=True,
        candidate_hard_timeout=5.0,
        termination_grace=0.05,
        screener=stage3_hang_or_complete,
    )

    assert time.monotonic() - started < 12
    assert [result["status"] for result in results] == [
        "UNRESOLVED",
        "THRESHOLD_PROVEN",
    ]
    assert results[0]["completed_directions"] == 3
    assert results[0]["hard_wall"]["timed_out"] is True
    artifact = json.loads(
        direction_state_path(
            tmp_path / "state",
            "hang-candidate",
        ).read_text()
    )
    assert artifact["completed_directions"] == 3
    _assert_process_stopped(
        int((pid_dir / "hang-candidate.pid").read_text())
    )


def test_stage3_startup_timeout_is_retryable_unresolved(tmp_path):
    results = screen_selected_candidates(
        [("startup-timeout", _candidate("peer-candidate"))],
        tmp_path / "state",
        timeout=30,
        candidate_workers=1,
        direction_workers=1,
        threshold_only=True,
        resume=True,
        candidate_hard_timeout=0.001,
        termination_grace=0.05,
        screener=stage3_hang_or_complete,
    )

    assert results[0]["status"] == "UNRESOLVED"
    assert results[0]["completed_directions"] == 0
    assert results[0]["hard_wall"]["startup_timed_out"] is True


def test_stage5_native_hang_is_incomplete_and_peer_can_win(
    tmp_path,
    monkeypatch,
):
    pid_dir = tmp_path / "pids"
    pid_dir.mkdir()
    monkeypatch.setenv("QCODE_STAGE35_PID_DIR", str(pid_dir))
    certificates = [
        _certificate(0, digest="hang"),
        _certificate(1),
    ]
    args = _finalizer_args(tmp_path, certificates)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    monkeypatch.setattr(
        finalizer,
        "_strict_integrity_with_hard_wall",
        lambda _args: {"mode": "strict", "passed": True, "failures": []},
    )
    monkeypatch.setattr(
        finalizer,
        "verify_certificate",
        stage5_hang_or_accept,
    )

    started = time.monotonic()
    assert finalizer.main() == 0
    assert time.monotonic() - started < 8

    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "WIN"
    assert [item["disposition"] for item in artifact["evaluations"]] == [
        "INCOMPLETE",
        "ACCEPTED",
    ]
    checkpoint = Path(artifact["evaluations"][0]["checkpoint_path"])
    assert json.loads(checkpoint.read_text())["completed_directions"] == 1
    scheduler = json.loads(
        (
            args.verification_state_dir / finalizer.SCHEDULER_FILENAME
        ).read_text()
    )
    assert scheduler["scheduled_attempts"] == 2
    _assert_process_stopped(int((pid_dir / "stage5-hang.pid").read_text()))


def test_strict_ibm_outer_wall_fails_closed_without_orphan(
    tmp_path,
    monkeypatch,
):
    pid_dir = tmp_path / "pids"
    pid_dir.mkdir()
    monkeypatch.setenv("QCODE_STAGE35_PID_DIR", str(pid_dir))
    args = _finalizer_args(tmp_path, [_certificate(0)])
    monkeypatch.setattr(
        finalizer,
        "check_known_answer_integrity",
        strict_integrity_hang,
    )
    monkeypatch.setattr(
        finalizer,
        "_known_answer_outer_timeout",
        lambda _total: 2.5,
    )

    result = finalizer._strict_integrity_with_hard_wall(args)

    assert result["passed"] is False
    assert "process hard wall" in result["failures"][0]
    _assert_process_stopped(int((pid_dir / "strict-hang.pid").read_text()))


def test_certificate_wall_reserves_cleanup_inside_fair_share(
    tmp_path,
    monkeypatch,
):
    captured = {}

    def fake_isolated(operation, **kwargs):
        captured["operation"] = operation
        captured.update(kwargs)
        return IsolatedCallOutcome(
            status="completed",
            value={"passed": True, "accepted": True, "failures": []},
        )

    monkeypatch.setattr(finalizer, "run_isolated_call", fake_isolated)
    result = finalizer._verify_certificate_with_hard_wall(
        _certificate(0),
        known_answer_artifact=tmp_path / "known.json",
        timeout_per_logical=10,
        checkpoint_path=tmp_path / "checkpoint.json",
        resume=True,
        total_timeout=10,
        solver_workers=3,
    )

    assert result["passed"] is True
    assert captured["operation"] is finalizer.verify_certificate
    assert captured["kwargs"]["rerun_milp"] is True
    assert captured["kwargs"]["total_timeout"] == pytest.approx(9.5)
    assert captured["timeout_s"] == pytest.approx(9.5)
    assert captured["termination_grace_s"] == pytest.approx(0.5)


def test_pipeline_outer_wall_kills_child_after_leader_exits(tmp_path):
    child_pid_path = tmp_path / "stage-child.pid"
    child_code = (
        "import ctypes,os,signal,sys;"
        "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
        "open(sys.argv[1],'w').write(str(os.getpid()));"
        "ctypes.CDLL(None).pause()"
    )
    leader_code = (
        "import subprocess,sys,time;"
        f"subprocess.Popen([sys.executable,'-c',{child_code!r},sys.argv[1]]);"
        "time.sleep(.1)"
    )

    with pytest.raises(subprocess.TimeoutExpired):
        default_command_runner(
            [sys.executable, "-c", leader_code, str(child_pid_path)],
            cwd=tmp_path,
            hard_timeout=0.4,
            termination_grace=0.05,
        )

    _assert_process_stopped(int(child_pid_path.read_text()))


def test_pipeline_normal_exit_cleans_child_that_closed_output_pipes(tmp_path):
    child_pid_path = tmp_path / "detached-output-child.pid"
    child_code = (
        "import ctypes,os,signal,sys;"
        "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
        "open(sys.argv[1],'w').write(str(os.getpid()));"
        "ctypes.CDLL(None).pause()"
    )
    leader_code = (
        "import os,subprocess,sys,time\n"
        "subprocess.Popen("
        f"[sys.executable,'-c',{child_code!r},sys.argv[1]],"
        "stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)\n"
        "deadline=time.monotonic()+2\n"
        "while not os.path.exists(sys.argv[1]) and time.monotonic()<deadline:\n"
        "    time.sleep(.01)\n"
    )

    completed = default_command_runner(
        [sys.executable, "-c", leader_code, str(child_pid_path)],
        cwd=tmp_path,
        hard_timeout=3,
        termination_grace=0.05,
    )

    assert completed.returncode == 70
    assert "descendants were terminated" in completed.stderr
    _assert_process_stopped(int(child_pid_path.read_text()))


def test_pipeline_outer_wall_accepts_timeout_above_poll_limit(tmp_path):
    completed = default_command_runner(
        [
            sys.executable,
            "-c",
            (
                "import time; print('started', flush=True); "
                "time.sleep(0.5); print('completed')"
            ),
        ],
        cwd=tmp_path,
        # Linux poll/epoll converts this to a millisecond C integer and raises
        # OverflowError if it is forwarded as one communicate timeout.
        hard_timeout=4_753_332,
        termination_grace=0.05,
    )

    assert completed.returncode == 0
    assert completed.stdout.splitlines() == ["started", "completed"]


def test_pipeline_outer_wall_wait_slices_preserve_total_deadline(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        pipeline_module,
        "SUBPROCESS_COMMUNICATE_MAX_SLICE_S",
        0.02,
    )

    completed = default_command_runner(
        [
            sys.executable,
            "-c",
            (
                "import time; print('before-slices', flush=True); "
                "time.sleep(0.08); print('after-slices')"
            ),
        ],
        cwd=tmp_path,
        hard_timeout=0.5,
        termination_grace=0.05,
    )

    assert completed.returncode == 0
    assert completed.stdout.splitlines() == [
        "before-slices",
        "after-slices",
    ]


def test_pipeline_outer_wall_slices_enforce_total_deadline_and_cleanup(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        pipeline_module,
        "SUBPROCESS_COMMUNICATE_MAX_SLICE_S",
        0.02,
    )
    pid_path = tmp_path / "sliced-timeout.pid"
    code = (
        "import os,signal,sys,time\n"
        "with open(sys.argv[1], 'w') as stream:\n"
        " stream.write(str(os.getpid()))\n"
        " stream.flush()\n"
        " os.fsync(stream.fileno())\n"
        "print('before-timeout', flush=True)\n"
        "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
        "time.sleep(30)\n"
    )

    with pytest.raises(subprocess.TimeoutExpired) as raised:
        default_command_runner(
            [sys.executable, "-c", code, str(pid_path)],
            cwd=tmp_path,
            hard_timeout=0.2,
            termination_grace=0.05,
        )

    assert raised.value.timeout == pytest.approx(0.2)
    output = raised.value.output
    if isinstance(output, bytes):
        output = output.decode()
    assert output == "before-timeout\n"
    _assert_process_stopped(int(pid_path.read_text()))


def test_unified_solver_worker_budget_is_capped_at_six():
    validate_worker_budget(2, 3, 6)
    with pytest.raises(ValueError, match="exceeds"):
        validate_worker_budget(2, 4, 6)
