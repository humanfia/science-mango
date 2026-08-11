from __future__ import annotations

import hashlib
import json
import signal
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

import humanize.pipeline_process as process_control
from humanize import pipeline_cli


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
    assert stored["config_path"] == str(config.resolve())
    assert stored["config_sha256"] == hashlib.sha256(
        config.read_bytes()
    ).hexdigest()


def test_durable_policy_snapshot_allows_operational_config_changes_only(tmp_path):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text(
        '{"run_id":"snapshot","stage1":'
        '{"search_representation_id":"css-bb-v1"}}\n'
    )
    paths = process_control.control_paths(repo, "snapshot", create=True)
    first_sha = hashlib.sha256(config.read_bytes()).hexdigest()
    first = process_control._capture_durable_escalation_policy(
        repo_dir=repo,
        config_path=config,
        config_sha256=first_sha,
        run_id="snapshot",
        snapshot_path=paths.escalation_policy,
    )
    assert first["enabled"] is False

    config.write_text(
        '{"run_id":"snapshot","resume":true,"max_total_workers":24,'
        '"stage1":{"search_representation_id":"css-bb-v1",'
        '"max_rounds":20}}\n'
    )
    changed_sha = hashlib.sha256(config.read_bytes()).hexdigest()
    second = process_control._capture_durable_escalation_policy(
        repo_dir=repo,
        config_path=config,
        config_sha256=changed_sha,
        run_id="snapshot",
        snapshot_path=paths.escalation_policy,
    )
    assert second == first

    config.write_text(
        '{"run_id":"snapshot","stage1":'
        '{"search_representation_id":"css-bb-v2"}}\n'
    )
    changed_authority_sha = hashlib.sha256(config.read_bytes()).hexdigest()
    with pytest.raises(
        process_control.ProcessControlError,
        match="differs from the durable run snapshot",
    ):
        process_control._capture_durable_escalation_policy(
            repo_dir=repo,
            config_path=config,
            config_sha256=changed_authority_sha,
            run_id="snapshot",
            snapshot_path=paths.escalation_policy,
        )


def test_v2_durable_policy_snapshot_keeps_round_budget_operational(tmp_path):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    paths = process_control.control_paths(repo, "snapshot-v2", create=True)
    config.write_text(
        json.dumps({
            "run_id": "snapshot-v2",
            "stage1": {
                "search_representation_id": "css-bb-v2",
                "search_regime_policy_version": 2,
                "max_rounds": 12,
            },
        })
        + "\n"
    )
    first = process_control._capture_durable_escalation_policy(
        repo_dir=repo,
        config_path=config,
        config_sha256=hashlib.sha256(config.read_bytes()).hexdigest(),
        run_id="snapshot-v2",
        snapshot_path=paths.escalation_policy,
    )

    config.write_text(
        json.dumps({
            "run_id": "snapshot-v2",
            "stage1": {
                "search_representation_id": "css-bb-v2",
                "search_regime_policy_version": 2,
                "max_rounds": 20,
            },
        })
        + "\n"
    )
    second = process_control._capture_durable_escalation_policy(
        repo_dir=repo,
        config_path=config,
        config_sha256=hashlib.sha256(config.read_bytes()).hexdigest(),
        run_id="snapshot-v2",
        snapshot_path=paths.escalation_policy,
    )

    assert second == first
    assert "source_search_regime_policy_version" not in first
    assert "source_max_rounds" not in first


def test_v4_durable_policy_snapshot_binds_handoff_authority(tmp_path):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    paths = process_control.control_paths(repo, "snapshot-v4", create=True)

    def write_config(*, policy_version: int, max_rounds: int, stop: bool) -> str:
        config.write_text(
            json.dumps({
                "run_id": "snapshot-v4",
                "stage1": {
                    "search_representation_id": "css-coset-v3",
                    "search_regime_policy_version": policy_version,
                    "max_rounds": max_rounds,
                    "stop_on_representation_change": stop,
                },
            })
            + "\n"
        )
        return hashlib.sha256(config.read_bytes()).hexdigest()

    first = process_control._capture_durable_escalation_policy(
        repo_dir=repo,
        config_path=config,
        config_sha256=write_config(
            policy_version=4,
            max_rounds=12,
            stop=True,
        ),
        run_id="snapshot-v4",
        snapshot_path=paths.escalation_policy,
    )
    assert first["source_search_regime_policy_version"] == 4
    assert first["source_max_rounds"] == 12
    assert first["source_stop_on_representation_change"] is True

    for policy_version, max_rounds, stop in (
        (3, 12, True),
        (4, 13, True),
        (4, 12, False),
    ):
        with pytest.raises(
            process_control.ProcessControlError,
            match="differs from the durable run snapshot",
        ):
            process_control._capture_durable_escalation_policy(
                repo_dir=repo,
                config_path=config,
                config_sha256=write_config(
                    policy_version=policy_version,
                    max_rounds=max_rounds,
                    stop=stop,
                ),
                run_id="snapshot-v4",
                snapshot_path=paths.escalation_policy,
            )


def test_pending_escalation_retries_without_rerunning_science(tmp_path):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "retry-parent", create=True)
    process_control.atomic_write_json(
        paths.root / "campaign-escalation.json",
        {"disposition": "pending", "retryable": True},
    )
    process_control.atomic_write_json(
        paths.state,
        {"status": "COMPLETED_NO_WIN", "stage1": {"status": "COMPLETED"}},
    )

    recovered = process_control._pending_escalation_parent_result(paths)
    assert recovered is not None
    assert recovered["status"] == "COMPLETED_NO_WIN"
    assert recovered["escalation_retry_only"] is True


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


@pytest.mark.parametrize("core_status", ["FAILED", "INCOMPLETE"])
def test_status_preserves_core_non_success_state(tmp_path, core_status):
    repo = _repo(tmp_path)
    paths = process_control.control_paths(repo, "failed-run", create=True)
    process_control.atomic_write_json(paths.process, _metadata("failed-run", repo=repo))
    process_control.atomic_write_json(paths.state, {"status": core_status})

    status = process_control.status_for_run(
        repo_dir=repo,
        run_id="failed-run",
        identity_reader=lambda _pid: None,
    )
    assert status["status"] == core_status
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
        ("INCOMPLETE", "failed", 1),
        ("ESCALATION_PENDING", "failed", 1),
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


def test_detached_worker_sigterm_unwinds_pipeline_cleanup(
    tmp_path,
    monkeypatch,
):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text('{"run_id": "cancel-cascade"}\n')
    paths = process_control.control_paths(repo, "cancel-cascade", create=True)
    handlers = {}
    registrations = []

    def fake_signal(signum, handler):
        handlers[signum] = handler
        registrations.append((signum, handler))

    def interrupted_pipeline(**_kwargs):
        handlers[signal.SIGTERM](signal.SIGTERM, None)
        raise AssertionError("SIGTERM handler must interrupt execute_pipeline")

    monkeypatch.setattr(pipeline_cli.signal, "signal", fake_signal)
    monkeypatch.setattr(pipeline_cli, "resolve_repo_dir", lambda _path: repo)
    monkeypatch.setattr(pipeline_cli, "resolve_config_path", lambda _path: config)
    monkeypatch.setattr(
        pipeline_cli,
        "_load_run_id",
        lambda *_args: "cancel-cascade",
    )
    monkeypatch.setattr(pipeline_cli, "control_paths", lambda *_args, **_kwargs: paths)
    monkeypatch.setattr(pipeline_cli, "execute_pipeline", interrupted_pipeline)
    monkeypatch.setattr(pipeline_cli.traceback, "print_exc", lambda: None)
    args = SimpleNamespace(
        repo_dir=repo,
        config=config,
        run_id="cancel-cascade",
        stage_review=None,
        reviewer_model=None,
        reviewer_effort=None,
        lock_fd=10,
        start_fd=11,
    )

    assert pipeline_cli._worker_command(args) == 1
    assert registrations[:2] == [
        (signal.SIGHUP, signal.SIG_IGN),
        (signal.SIGTERM, pipeline_cli._interrupt_pipeline_on_sigterm),
    ]
    assert registrations[-1] == (signal.SIGTERM, signal.SIG_IGN)


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


def _fake_materialized_reconciliation(
    child_config: Path,
    *,
    child_run_id: str = "auto-child",
):
    payload = child_config.read_bytes()
    materialized = SimpleNamespace(
        path=child_config,
        child_run_id=child_run_id,
        pipeline_sha256=hashlib.sha256(payload).hexdigest(),
    )
    return SimpleNamespace(
        disposition="materialized",
        materialized=materialized,
        serializable=lambda: {
            "schema_version": 1,
            "kind": "qcode-campaign-escalation-reconciliation",
            "disposition": "materialized",
            "materialized": {
                "path": str(child_config),
                "child_run_id": child_run_id,
                "pipeline_sha256": hashlib.sha256(payload).hexdigest(),
            },
        },
    )


def test_completed_no_win_materializes_and_starts_exact_child_once(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path)
    parent_config = repo / "parent.json"
    parent_config.write_text('{"run_id":"parent"}\n')
    child_input = repo / "child-candidates.jsonl"
    child_input.write_text("{}\n")
    child_config = repo / "child.json"
    child_config.write_text(
        json.dumps({
            "run_id": "auto-child",
            "resume": False,
            "candidate_inputs": [str(child_input)],
        }) + "\n"
    )
    reconciliation = _fake_materialized_reconciliation(child_config)
    monkeypatch.setattr(
        "humanize.escalation.reconcile_campaign_escalation",
        lambda **_kwargs: reconciliation,
    )
    monkeypatch.setattr(
        "humanize.escalation.verify_materialized_child_pipeline",
        lambda **_kwargs: {},
    )
    launches = []

    def launch(**kwargs):
        launches.append(kwargs)
        intent = json.loads(
            process_control.control_paths(repo, "parent").root.joinpath(
                "campaign-escalation.json"
            ).read_text()
        )
        assert intent["disposition"] == "pending"
        assert intent["retryable"] is True
        assert intent["launch"] == {
            "status": "pending-launch-intent",
            "child_run_id": "auto-child",
            "config_path": str(child_config.resolve()),
            "config_sha256": hashlib.sha256(
                child_config.read_bytes()
            ).hexdigest(),
        }
        return {
            "run_id": kwargs["run_id"],
            "config_path": str(kwargs["config_path"]),
            "config_sha256": kwargs["expected_config_sha256"],
            "pid": 9001,
            "proc_starttime": 77,
        }

    outcome = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=launch,
        status_reader=lambda **_kwargs: {
            "status": "not-started",
            "alive": False,
            "process": None,
            "state": None,
        },
    )

    assert outcome is not None
    assert outcome["launch"] == {
        "status": "started",
        "pid": 9001,
        "proc_starttime": 77,
    }
    assert len(launches) == 1
    assert launches[0]["run_id"] == "auto-child"
    assert launches[0]["config_path"] == child_config.resolve()
    stored = json.loads(
        process_control.control_paths(repo, "parent").root.joinpath(
            "campaign-escalation.json"
        ).read_text()
    )
    assert stored["launch"]["status"] == "started"


def test_campaign_escalation_adopts_only_hash_bound_live_child(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path)
    parent_config = repo / "parent.json"
    parent_config.write_text('{"run_id":"parent"}\n')
    child_input = repo / "child-candidates.jsonl"
    child_input.write_text("{}\n")
    child_config = repo / "child.json"
    child_config.write_text(json.dumps({
        "run_id": "auto-child",
        "candidate_inputs": [str(child_input)],
    }) + "\n")
    reconciliation = _fake_materialized_reconciliation(child_config)
    monkeypatch.setattr(
        "humanize.escalation.reconcile_campaign_escalation",
        lambda **_kwargs: reconciliation,
    )
    monkeypatch.setattr(
        "humanize.escalation.verify_materialized_child_pipeline",
        lambda **_kwargs: {},
    )
    digest = hashlib.sha256(child_config.read_bytes()).hexdigest()
    live = {
        "status": "running",
        "alive": True,
        "process": {
            "run_id": "auto-child",
            "config_path": str(child_config.resolve()),
            "config_sha256": digest,
            "pid": 9002,
            "proc_starttime": 88,
        },
        "state": {"status": "RUNNING"},
    }

    outcome = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=lambda **_kwargs: pytest.fail("live child must be adopted"),
        status_reader=lambda **_kwargs: live,
    )
    assert outcome is not None
    assert outcome["launch"]["status"] == "adopted-running"
    assert outcome["launch"]["pid"] == 9002

    forged = dict(live)
    forged["process"] = dict(live["process"], config_sha256="0" * 64)
    blocked = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent-2",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=lambda **_kwargs: pytest.fail("mismatched child must not start"),
        status_reader=lambda **_kwargs: forged,
    )
    assert blocked is not None
    assert blocked["disposition"] == "pending"
    assert blocked["classification"] == "ProcessControlError"


def test_stale_or_failed_child_resumes_same_id_but_unknown_state_fails_closed(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path)
    parent_config = repo / "parent.json"
    parent_config.write_text('{"run_id":"parent"}\n')
    child_input = repo / "child-candidates.jsonl"
    child_input.write_text("{}\n")
    child_config = repo / "child.json"
    child_config.write_text(json.dumps({
        "run_id": "auto-child",
        "resume": True,
        "candidate_inputs": [str(child_input)],
    }) + "\n")
    reconciliation = _fake_materialized_reconciliation(child_config)
    monkeypatch.setattr(
        "humanize.escalation.reconcile_campaign_escalation",
        lambda **_kwargs: reconciliation,
    )
    monkeypatch.setattr(
        "humanize.escalation.verify_materialized_child_pipeline",
        lambda **_kwargs: {},
    )
    digest = hashlib.sha256(child_config.read_bytes()).hexdigest()
    stale = {
        "status": "stale",
        "alive": False,
        "process": {
            "run_id": "auto-child",
            "config_path": str(child_config.resolve()),
            "config_sha256": digest,
            "pid": 9003,
            "proc_starttime": 99,
        },
        "state": {"status": "RUNNING"},
    }
    launches = []

    resumed = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent",
        result={"status": "INCOMPLETE"},
        python_executable="/usr/bin/python3",
        launcher=lambda **kwargs: launches.append(kwargs) or {
            "run_id": kwargs["run_id"],
            "config_path": str(kwargs["config_path"]),
            "config_sha256": kwargs["expected_config_sha256"],
            "pid": 9004,
            "proc_starttime": 100,
        },
        status_reader=lambda **_kwargs: stale,
    )
    assert resumed is not None
    assert resumed["launch"]["status"] == "started"
    assert launches[0]["run_id"] == "auto-child"
    assert launches[0]["expected_config_sha256"] == digest

    failed = {
        "status": "FAILED",
        "alive": False,
        "process": stale["process"],
        "state": {"status": "FAILED"},
    }
    failed_launches = []
    resumed_failed = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent-failed",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=lambda **kwargs: failed_launches.append(kwargs) or {
            "run_id": kwargs["run_id"],
            "config_path": str(kwargs["config_path"]),
            "config_sha256": kwargs["expected_config_sha256"],
            "pid": 9005,
            "proc_starttime": 101,
        },
        status_reader=lambda **_kwargs: failed,
    )
    assert resumed_failed is not None
    assert resumed_failed["launch"]["status"] == "resumed-failed"
    assert failed_launches[0]["run_id"] == "auto-child"

    unknown = process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=parent_config,
        parent_run_id="parent-unknown",
        result={"status": "COMPLETED_NO_WIN"},
        python_executable="/usr/bin/python3",
        launcher=lambda **_kwargs: pytest.fail("unknown child must not start"),
        status_reader=lambda **_kwargs: {
            "status": "mystery",
            "alive": False,
            "process": None,
            "state": {"status": "mystery"},
        },
    )
    assert unknown is not None
    assert unknown["disposition"] == "pending"


def test_incomplete_result_enters_escalation_reconciliation(tmp_path, monkeypatch):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text("{}\n")
    calls = []
    disabled = SimpleNamespace(
        disposition="disabled",
        materialized=None,
        serializable=lambda: {"disposition": "disabled"},
    )
    monkeypatch.setattr(
        "humanize.escalation.reconcile_campaign_escalation",
        lambda **kwargs: calls.append(kwargs) or disabled,
    )

    outcome_path = process_control.control_paths(
        repo, "incomplete-parent", create=True
    ).root / "campaign-escalation.json"
    process_control.atomic_write_json(
        outcome_path,
        {"disposition": "pending", "retryable": True},
    )

    assert process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=config,
        parent_run_id="incomplete-parent",
        result={"status": "INCOMPLETE"},
        python_executable="/usr/bin/python3",
    ) is None
    assert len(calls) == 1
    assert json.loads(outcome_path.read_text())["disposition"] == "disabled"


def test_campaign_escalation_does_not_run_for_non_no_win_result(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path)
    config = repo / "pipeline.json"
    config.write_text("{}\n")
    monkeypatch.setattr(
        "humanize.escalation.reconcile_campaign_escalation",
        lambda **_kwargs: pytest.fail("non-no-WIN must not reconcile"),
    )
    assert process_control.reconcile_completed_campaign_escalation(
        repo_dir=repo,
        pipeline_config_path=config,
        parent_run_id="winner",
        result={"status": "COMPLETED_WIN"},
        python_executable="/usr/bin/python3",
    ) is None


def test_export_release_command_uses_resolved_repo_and_safe_run_id(
    tmp_path, monkeypatch
):
    repo = _repo(tmp_path).resolve()
    captured = {}
    output = {
        "status": "exported",
        "run_id": "release-run",
        "manifest": str(repo / "results/runs/release-run/challenge_manifest.json"),
    }

    monkeypatch.setattr(pipeline_cli, "resolve_repo_dir", lambda _path: repo)

    def fake_export_release(*, repo_dir, run_id, python_executable):
        captured.update(
            repo_dir=repo_dir,
            run_id=run_id,
            python_executable=python_executable,
        )
        return output

    printed = []
    monkeypatch.setattr(pipeline_cli, "export_release", fake_export_release)
    monkeypatch.setattr(
        pipeline_cli,
        "_print_json",
        lambda value, **_kwargs: printed.append(value),
    )

    assert (
        pipeline_cli._export_release_command(
            SimpleNamespace(
                repo_dir=repo,
                run_id="release-run",
                python_executable="/trusted/python",
            )
        )
        == 0
    )
    assert captured == {
        "repo_dir": repo,
        "run_id": "release-run",
        "python_executable": "/trusted/python",
    }
    assert printed == [output]


def test_export_release_cli_distinguishes_no_win_from_invalid_export(
    tmp_path, monkeypatch, capsys
):
    repo = _repo(tmp_path).resolve()
    monkeypatch.setattr(pipeline_cli, "resolve_repo_dir", lambda _path: repo)

    def no_win(**_kwargs):
        raise pipeline_cli.ReleaseNotExportableError(
            "NO_CERTIFIED_WIN", "no certified win"
        )

    monkeypatch.setattr(pipeline_cli, "export_release", no_win)
    assert (
        pipeline_cli.main(
            ["export-release", "--repo-dir", str(repo), "--run-id", "no-win"]
        )
        == 1
    )
    payload = json.loads(capsys.readouterr().err)
    assert payload["status"] == "not-exportable"
    assert payload["classification"] == "NO_CERTIFIED_WIN"

    def invalid(**_kwargs):
        raise pipeline_cli.ReleaseExportError("STATE_HASH_MISMATCH", "tampered")

    monkeypatch.setattr(pipeline_cli, "export_release", invalid)
    assert (
        pipeline_cli.main(
            ["export-release", "--repo-dir", str(repo), "--run-id", "invalid"]
        )
        == 2
    )
    payload = json.loads(capsys.readouterr().err)
    assert payload["status"] == "error"
    assert payload["classification"] == "STATE_HASH_MISMATCH"
