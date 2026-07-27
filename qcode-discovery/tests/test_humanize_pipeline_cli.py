from __future__ import annotations

import json
import signal
import subprocess
from pathlib import Path
from types import SimpleNamespace

import humanize.pipeline_cli as pipeline_cli
import humanize.pipeline_process as process_control
import pytest


def _repo(tmp_path: Path) -> Path:
    repo = tmp_path / "qcode"
    (repo / "humanize").mkdir(parents=True)
    return repo


def _identity(pid: int = 4321) -> dict:
    return {
        "pid": pid,
        "command_name": "python",
        "state": "S",
        "pgid": pid,
        "session_id": pid,
        "proc_starttime": 123456,
        "uid": 1000,
        "cmdline_sha256": "a" * 64,
    }


def _metadata(
    run_id: str = "safe-run", pid: int = 4321, repo: Path | None = None
) -> dict:
    value = {
        "schema_version": process_control.PROCESS_SCHEMA_VERSION,
        "run_id": run_id,
        "status": "running",
        "isolated_session": True,
        **_identity(pid),
    }
    if repo is not None:
        value["repo_dir"] = str(repo.resolve())
    return value


def test_pipeline_run_id_rejects_path_traversal():
    for run_id in ("../escape", "/absolute", ".", "..", "space name", ""):
        with pytest.raises(ValueError):
            process_control.validate_run_id(run_id)
    assert process_control.validate_run_id("campaign-2026.07_27") == (
        "campaign-2026.07_27"
    )


def test_process_match_binds_pid_starttime_uid_command_and_session():
    metadata = _metadata()
    assert process_control.process_matches(
        metadata, identity_reader=lambda _pid: _identity()
    ).alive

    for field, replacement in (
        ("proc_starttime", 999),
        ("uid", 2000),
        ("cmdline_sha256", "b" * 64),
        ("pgid", 999),
        ("session_id", 999),
    ):
        live = _identity()
        live[field] = replacement
        match = process_control.process_matches(
            metadata, identity_reader=lambda _pid, value=live: value
        )
        assert not match.alive
        assert field in match.reason


def test_background_start_uses_isolated_session_and_inherited_lock(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text("{}\n")
    captured = {}

    class FakeProcess:
        pid = 4321

        def poll(self):
            return None

        def terminate(self):
            raise AssertionError("valid detached start must not be terminated")

    def fake_popen(command, **kwargs):
        captured["command"] = command
        captured["kwargs"] = kwargs
        return FakeProcess()

    # A fake Popen cannot really inherit the read side of the launch barrier.
    monkeypatch.setattr(process_control.os, "write", lambda _fd, data: len(data))
    record = process_control.start_background(
        repo_dir=repo,
        config_path=config,
        run_id="detached",
        python_executable="/usr/bin/python3",
        popen_factory=fake_popen,
        identity_reader=lambda _pid: _identity(),
    )

    kwargs = captured["kwargs"]
    assert kwargs["start_new_session"] is True
    assert kwargs["close_fds"] is True
    assert len(kwargs["pass_fds"]) == 2
    assert kwargs["stdin"] is subprocess.DEVNULL
    assert kwargs["stderr"] is subprocess.STDOUT
    assert isinstance(kwargs["stdout"], int)
    assert "shell" not in kwargs or kwargs["shell"] is False
    assert captured["command"][0] == "/usr/bin/python3"
    assert captured["command"][1:4] == [
        "-m",
        "humanize.pipeline_cli",
        "_worker",
    ]
    start_fd = int(captured["command"][captured["command"].index("--start-fd") + 1])
    lock_fd = int(captured["command"][captured["command"].index("--lock-fd") + 1])
    assert start_fd >= 0
    assert {start_fd, lock_fd} == set(kwargs["pass_fds"])
    assert record["isolated_session"] is True
    assert record["pgid"] == record["pid"] == record["session_id"]
    stored = json.loads(
        process_control.control_paths(repo, "detached").process.read_text()
    )
    assert stored["status"] == "starting"
    assert stored["proc_starttime"] == 123456


def test_per_run_lock_rejects_duplicate_owner(tmp_path):
    lock = tmp_path / "process.lock"
    first = process_control.acquire_run_lock(lock)
    try:
        with pytest.raises(process_control.AlreadyRunningError):
            process_control.acquire_run_lock(lock)
    finally:
        process_control.close_run_lock(first, unlock=True)


def test_status_marks_reused_pid_as_stale(tmp_path):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "status-run", create=True)
    process_control.atomic_write_json(paths.process, _metadata("status-run", repo=repo))
    process_control.atomic_write_json(paths.state, {"status": "running"})

    reused = _identity()
    reused["proc_starttime"] += 1
    status = process_control.status_for_run(
        repo_dir=repo,
        run_id="status-run",
        identity_reader=lambda _pid: reused,
    )
    assert status["status"] == "stale"
    assert status["alive"] is False
    assert "proc_starttime" in status["identity_reason"]


def test_status_preserves_core_failed_terminal_state(tmp_path):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "failed-run", create=True)
    process_control.atomic_write_json(paths.process, _metadata("failed-run", repo=repo))
    process_control.atomic_write_json(paths.state, {"status": "FAILED"})

    status = process_control.status_for_run(
        repo_dir=repo,
        run_id="failed-run",
        identity_reader=lambda _pid: None,
    )
    assert status["status"] == "FAILED"
    assert status["alive"] is False


def test_cancel_refuses_reused_pid_without_sending_any_signal(tmp_path):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "cancel-stale", create=True)
    process_control.atomic_write_json(
        paths.process, _metadata("cancel-stale", repo=repo)
    )
    reused = _identity()
    reused["cmdline_sha256"] = "b" * 64
    signals = []

    with pytest.raises(process_control.UnsafeProcessError, match="mismatch"):
        process_control.cancel_run(
            repo_dir=repo,
            run_id="cancel-stale",
            identity_reader=lambda _pid: reused,
            kill_process=lambda pid, sig: signals.append(("pid", pid, sig)),
            kill_group=lambda pgid, sig: signals.append(("pgid", pgid, sig)),
        )
    assert signals == []


def test_cancel_detached_run_signals_the_verified_process_group(tmp_path):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "cancel-group", create=True)
    process_control.atomic_write_json(
        paths.process, _metadata("cancel-group", repo=repo)
    )
    reads = iter((_identity(), None))
    groups = []
    processes = []

    result = process_control.cancel_run(
        repo_dir=repo,
        run_id="cancel-group",
        grace_seconds=0.1,
        poll_interval=0.001,
        identity_reader=lambda _pid: next(reads, None),
        group_members_reader=lambda **_kwargs: [],
        kill_process=lambda pid, sig: processes.append((pid, sig)),
        kill_group=lambda pgid, sig: groups.append((pgid, sig)),
    )

    assert result["status"] == "cancelled"
    assert result["forced"] is False
    assert groups == [(4321, signal.SIGTERM)]
    assert processes == []


def test_cancel_escalates_only_the_same_verified_group(tmp_path, monkeypatch):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "cancel-force", create=True)
    process_control.atomic_write_json(
        paths.process, _metadata("cancel-force", repo=repo)
    )
    waits = iter((False, True))
    monkeypatch.setattr(
        process_control,
        "_wait_until_group_stops",
        lambda **_kwargs: next(waits),
    )
    groups = []

    result = process_control.cancel_run(
        repo_dir=repo,
        run_id="cancel-force",
        grace_seconds=0,
        identity_reader=lambda _pid: _identity(),
        group_members_reader=lambda **_kwargs: [4321],
        kill_process=lambda _pid, _sig: pytest.fail(
            "detached cancellation must use killpg"
        ),
        kill_group=lambda pgid, sig: groups.append((pgid, sig)),
    )

    assert result["forced"] is True
    assert result["status"] == "cancelled"
    assert groups == [
        (4321, signal.SIGTERM),
        (4321, signal.SIGKILL),
    ]


@pytest.mark.parametrize(
    ("terminal_status", "expected_process_status", "expected_exit"),
    [
        ("FAILED", "failed", 1),
        ("COMPLETED_WIN", "completed", 0),
        ("COMPLETED_NO_WIN", "completed", 0),
    ],
)
def test_terminal_result_controls_process_status_and_cli_exit(
    tmp_path,
    monkeypatch,
    terminal_status,
    expected_process_status,
    expected_exit,
):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text('{"run_id": "terminal"}\n')
    paths = process_control.control_paths(repo, "terminal", create=True)
    process_control.atomic_write_json(paths.process, _metadata("terminal", repo=repo))
    result = {"status": terminal_status}

    succeeded = process_control.finalize_process_result(
        paths.process,
        pid=4321,
        proc_starttime=123456,
        result=result,
    )
    stored = json.loads(paths.process.read_text())
    assert stored["status"] == expected_process_status
    assert succeeded is (expected_exit == 0)

    monkeypatch.setattr(pipeline_cli, "resolve_repo_dir", lambda _path: repo)
    monkeypatch.setattr(pipeline_cli, "resolve_config_path", lambda _path: config)
    monkeypatch.setattr(pipeline_cli, "_load_run_id", lambda *_args: "terminal")
    monkeypatch.setattr(pipeline_cli, "_print_json", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(pipeline_cli, "run_foreground", lambda **_kwargs: result)
    args = SimpleNamespace(
        repo_dir=repo,
        config=config,
        run_id="terminal",
        stage_review=None,
        reviewer_model=None,
        reviewer_effort=None,
    )
    assert pipeline_cli._run_command(args) == expected_exit

    monkeypatch.setattr(pipeline_cli.signal, "signal", lambda *_args: None)
    monkeypatch.setattr(pipeline_cli, "control_paths", lambda *_args, **_kwargs: paths)
    monkeypatch.setattr(pipeline_cli, "execute_pipeline", lambda **_kwargs: result)
    worker_args = SimpleNamespace(
        **vars(args),
        lock_fd=10,
        start_fd=11,
    )
    assert pipeline_cli._worker_command(worker_args) == expected_exit


def test_status_and_cancel_reject_process_record_copied_from_another_run(
    tmp_path,
):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "requested-run", create=True)
    process_control.atomic_write_json(
        paths.process,
        _metadata("different-run", repo=repo),
    )
    signals = []

    status = process_control.status_for_run(
        repo_dir=repo,
        run_id="requested-run",
        identity_reader=lambda _pid: _identity(),
    )
    assert status["alive"] is False
    assert status["status"] == "stale"
    assert "run_id mismatch" in status["identity_reason"]

    with pytest.raises(process_control.UnsafeProcessError, match="run_id mismatch"):
        process_control.cancel_run(
            repo_dir=repo,
            run_id="requested-run",
            identity_reader=lambda _pid: _identity(),
            kill_process=lambda pid, sig: signals.append(("pid", pid, sig)),
            kill_group=lambda pgid, sig: signals.append(("pgid", pgid, sig)),
        )
    assert signals == []


def test_cancel_rejects_process_record_copied_from_another_repo(tmp_path):
    repo = _repo(tmp_path / "first")
    other_repo = _repo(tmp_path / "second")
    paths = process_control.control_paths(repo, "same-run", create=True)
    process_control.atomic_write_json(
        paths.process,
        _metadata("same-run", repo=other_repo),
    )
    signals = []

    with pytest.raises(process_control.UnsafeProcessError, match="repo_dir mismatch"):
        process_control.cancel_run(
            repo_dir=repo,
            run_id="same-run",
            identity_reader=lambda _pid: _identity(),
            kill_group=lambda pgid, sig: signals.append((pgid, sig)),
        )
    assert signals == []


def test_control_root_symlink_cannot_escape_repository(tmp_path):
    repo = _repo(tmp_path)
    outside = tmp_path / "outside"
    outside.mkdir()
    (repo / "results").symlink_to(outside, target_is_directory=True)

    with pytest.raises(ValueError, match="escapes repository"):
        process_control.control_paths(repo, "escape", create=True)
    assert not (outside / "humanize").exists()
