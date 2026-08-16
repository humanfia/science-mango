from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from types import SimpleNamespace

import pytest

from humanize import exactification_cli as cli


def _repo(tmp_path: Path) -> tuple[Path, Path]:
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    run = repo / "results" / "humanize" / "pipelines" / "run-a"
    run.mkdir(parents=True)
    return repo, run


def _config(tmp_path: Path) -> Path:
    path = tmp_path / "exact.json"
    path.write_text(
        json.dumps(
            {
                "queue": {
                    "top_k": 13,
                    "workers": 1,
                    "max_attempts": 3,
                    "termination_grace_s": 180,
                },
                "resources": {
                    "solver_slots": 1,
                    "reserve_foreground_cpus": 12,
                    "nice": 15,
                    "heartbeat_s": 60,
                    "capacity_poll_s": 1,
                    "termination_grace_s": 180,
                },
            }
        )
        + "\n"
    )
    return path


def _identity(pid: int = 4321) -> dict:
    return {
        "pid": pid,
        "proc_starttime": 99,
        "pgid": pid,
        "session_id": pid,
        "uid": os.getuid(),
        "cmdline_sha256": "a" * 64,
    }


def test_parser_exposes_sidecar_commands_and_run_is_once():
    parser = cli.build_parser()
    args = parser.parse_args(
        ["run", "--run-id", "r", "--config", "policy.json"]
    )
    assert args.command == "run"
    assert args.once is True
    for command in ("refresh", "start", "status", "cancel", "_worker"):
        assert command in parser._subparsers._group_actions[0].choices
    cancel = parser.parse_args(["cancel", "--run-id", "r"])
    assert cancel.grace_seconds == 180.0


def test_cpu_list_and_resource_policy_are_fail_closed():
    assert cli.parse_cpu_list("7,9-10") == (7, 9, 10)
    policy = cli.ResourcePolicy.from_mapping({"resources": {}})
    assert policy.solver_slots == 1
    assert policy.reserve_foreground_cpus == 12
    assert policy.nice == 15
    with pytest.raises(ValueError, match="at least 12"):
        cli.ResourcePolicy.from_mapping(
            {"resources": {"reserve_foreground_cpus": 11}}
        )
    with pytest.raises(ValueError, match="solver_slots=1"):
        cli.ResourcePolicy.from_mapping({"resources": {"solver_slots": 2}})


def test_process_record_is_self_hashed_and_tamper_detected(tmp_path):
    path = tmp_path / "process.json"
    record = {
        "schema_version": 1,
        "kind": cli.PROCESS_KIND,
        "status": "running",
    }
    written = cli.write_process_record(path, record)
    assert cli.read_process_record(path) == written
    tampered = json.loads(path.read_text())
    tampered["status"] = "completed"
    path.write_text(json.dumps(tampered))
    with pytest.raises(cli.ExactificationControlError, match="self-hash"):
        cli.read_process_record(path)


def test_start_uses_list_argv_shell_false_and_isolated_session(
    tmp_path, monkeypatch
):
    repo, _ = _repo(tmp_path)
    config = _config(tmp_path)
    paths = cli.control_paths(repo, "run-a", create=True)
    captured = {}

    class FakeProcess:
        pid = 4321

        def poll(self):
            return None

        def terminate(self):
            captured["terminated"] = True

    def fake_popen(command, **kwargs):
        captured["command"] = command
        captured["kwargs"] = kwargs
        return FakeProcess()

    monkeypatch.setattr(cli.subprocess, "Popen", fake_popen)
    # FakePopen has no child-side duplicate of the launch-barrier pipe.
    monkeypatch.setattr(cli.os, "write", lambda _fd, payload: len(payload))
    monkeypatch.setattr(cli, "_proc_identity", lambda pid: _identity(pid))
    args = cli.build_parser().parse_args(
        [
            "start",
            "--repo-dir",
            str(repo),
            "--run-id",
            "run-a",
            "--config",
            str(config),
        ]
    )

    record = cli.start_background(args, paths)

    assert isinstance(captured["command"], list)
    assert captured["kwargs"]["shell"] is False
    assert captured["kwargs"]["start_new_session"] is True
    assert record["status"] == "starting"
    assert cli.read_process_record(paths.process) == record


def test_cancel_refuses_reused_pid_and_signals_only_verified_group(
    tmp_path, monkeypatch
):
    repo, _ = _repo(tmp_path)
    paths = cli.control_paths(repo, "run-a", create=True)
    identity = _identity()
    cli.write_process_record(
        paths.process,
        {
            "schema_version": 1,
            "kind": cli.PROCESS_KIND,
            "run_id": "run-a",
            "repo_dir": str(repo.resolve()),
            "sidecar_root": str(paths.root),
            "status": "running",
            **identity,
            "isolated_session": True,
        },
    )
    args = SimpleNamespace(
        repo_dir=repo, run_id="run-a", grace_seconds=180.0
    )
    signals = []
    with pytest.raises(cli.UnsafeProcessError, match="mismatch"):
        cli.cancel_worker(
            args,
            paths,
            identity_reader=lambda _pid: {**identity, "proc_starttime": 100},
            kill_group=lambda pgid, signum: signals.append((pgid, signum)),
        )
    assert signals == []

    alive = {"value": True}

    def identity_reader(_pid):
        return identity if alive["value"] else None

    def kill_group(pgid, signum):
        signals.append((pgid, signum))
        alive["value"] = False

    result = cli.cancel_worker(
        args, paths, identity_reader=identity_reader, kill_group=kill_group
    )
    assert result["stopped"] is True
    assert signals[0][0] == identity["pgid"]


def test_foreground_once_applies_limits_before_scientific_work(
    tmp_path, monkeypatch
):
    repo, _ = _repo(tmp_path)
    config = _config(tmp_path)
    paths = cli.control_paths(repo, "run-a", create=True)
    args = cli.build_parser().parse_args(
        [
            "run",
            "--repo-dir",
            str(repo),
            "--run-id",
            "run-a",
            "--config",
            str(config),
        ]
    )
    events = []

    class Lease:
        def release(self):
            events.append("release")

    monkeypatch.setattr(cli, "_proc_identity", lambda _pid: _identity(os.getpid()))
    monkeypatch.setattr(cli, "_selected_cpus", lambda _policy: (7,))
    monkeypatch.setattr(
        cli,
        "_capacity_lease",
        lambda _policy, _affinity: events.append("capacity") or Lease(),
    )
    monkeypatch.setattr(
        cli, "_apply_resources", lambda _policy, _cpus: events.append("resources")
    )

    def scientific(**_kwargs):
        events.append("scientific")
        assert os.environ["OMP_NUM_THREADS"] == "1"
        return {"status": "IDLE", "processed": 0}

    monkeypatch.setattr(cli, "_run_scientific", scientific)
    lock_fd = cli._acquire_lock(paths.lock)
    try:
        result = cli._execute_worker(
            args=args,
            paths=paths,
            lock_fd=lock_fd,
            isolated=False,
        )
    finally:
        os.close(lock_fd)

    assert result["status"] == "IDLE"
    assert events == ["capacity", "resources", "scientific", "release"]
    record = cli.read_process_record(paths.process)
    assert record is not None
    assert record["status"] == "completed"
    assert record["result_status"] == "IDLE"


def test_stage2_sources_are_confined_to_the_same_run(tmp_path):
    repo, run = _repo(tmp_path)
    solver_state = run / "solver-state"
    stage2_state = solver_state / "xor"
    stage2_state.mkdir(parents=True)
    ledger = solver_state / "stage2-selection-ledger.json"
    ledger.write_text("{}\n")
    paths = cli.control_paths(repo, "run-a", create=True)
    args = SimpleNamespace(ledger_path=ledger, stage2_state_dir=stage2_state)
    resolved = cli._source_kwargs(args, paths)
    assert resolved["ledger_path"] == ledger.resolve()
    assert resolved["stage2_state_dir"] == stage2_state.resolve()

    outside = tmp_path / "outside"
    outside.mkdir()
    args.stage2_state_dir = outside
    with pytest.raises(ValueError, match="escapes"):
        cli._source_kwargs(args, paths)


def test_cancel_grace_must_cover_recorded_solver_cleanup(tmp_path):
    repo, _ = _repo(tmp_path)
    paths = cli.control_paths(repo, "run-a", create=True)
    identity = _identity()
    cli.write_process_record(
        paths.process,
        {
            "schema_version": 1,
            "kind": cli.PROCESS_KIND,
            "run_id": "run-a",
            "repo_dir": str(repo.resolve()),
            "sidecar_root": str(paths.root),
            "status": "running",
            **identity,
            "isolated_session": True,
            "resources": {"termination_grace_s": 180.0},
            "solver_termination_grace_s": 180.0,
        },
    )
    args = SimpleNamespace(repo_dir=repo, run_id="run-a", grace_seconds=179.0)
    signals = []
    with pytest.raises(ValueError, match="solver termination grace"):
        cli.cancel_worker(
            args,
            paths,
            identity_reader=lambda _pid: identity,
            kill_group=lambda pgid, signum: signals.append((pgid, signum)),
        )
    assert signals == []


def _audit_process(
    *,
    pid: int,
    ppid: int,
    pgid: int,
    state_dir: str,
    cwd: str = "/repo",
    state: str = "R",
):
    from evaluation.solver_budget import ProcessRecord

    return ProcessRecord(
        pid=pid,
        ppid=ppid,
        pgid=pgid,
        state=state,
        comm="python",
        argv=(
            "/venv/bin/python",
            "-I",
            "-B",
            "/repo/scripts/audit_candidate_pool.py",
            "candidates.jsonl",
            "--state-dir",
            state_dir,
            "--candidate-workers",
            "3",
            "--solver-workers",
            "4",
        ),
        cwd=cwd,
    )


def test_audit_pool_process_dedup_preserves_independent_campaigns_and_solvers():
    from evaluation.solver_budget import (
        ProcessRecord,
        estimate_unmanaged_qcode_usage,
    )

    root = _audit_process(
        pid=100,
        ppid=1,
        pgid=100,
        state_dir="/run-a/solver-state",
    )
    workers = [
        _audit_process(
            pid=pid,
            ppid=100,
            pgid=100,
            state_dir="/run-a/solver-state",
        )
        for pid in range(101, 113)
    ]
    other = _audit_process(
        pid=200,
        ppid=1,
        pgid=200,
        state_dir="/run-b/solver-state",
    )
    standalone = ProcessRecord(
        pid=300,
        ppid=1,
        pgid=300,
        state="R",
        comm="cadical",
        argv=("/usr/bin/cadical", "/root/qcode-discovery/proof.cnf"),
        cwd="/root/qcode-discovery",
    )

    masked = cli._deduplicate_audit_pool_processes(
        [root, *workers, other, standalone],
    )
    by_pid = {record.pid: record for record in masked}
    assert by_pid[100].argv == root.argv
    assert all(by_pid[pid].argv == () for pid in range(101, 113))
    assert by_pid[200].argv == other.argv
    assert by_pid[300].argv == standalone.argv

    usage = estimate_unmanaged_qcode_usage(masked)
    assert usage.workers == 25
    assert [item["pid"] for item in usage.campaigns] == [100, 200]
    assert [item["pid"] for item in usage.external_solvers] == [300]


def test_zombie_audit_ancestor_does_not_hide_a_live_pool_child():
    from evaluation.solver_budget import estimate_unmanaged_qcode_usage

    zombie = _audit_process(
        pid=100,
        ppid=1,
        pgid=100,
        state_dir="/run-a/solver-state",
        state="Z",
    )
    live_child = _audit_process(
        pid=101,
        ppid=100,
        pgid=100,
        state_dir="/run-a/solver-state",
    )

    masked = cli._deduplicate_audit_pool_processes([zombie, live_child])
    by_pid = {record.pid: record for record in masked}
    assert by_pid[101].argv == live_child.argv
    usage = estimate_unmanaged_qcode_usage(masked)
    assert usage.workers == 12
    assert [item["pid"] for item in usage.campaigns] == [101]


def test_capacity_lease_counts_one_multiprocessing_pool_once(monkeypatch):
    from evaluation import solver_budget

    root = _audit_process(
        pid=100,
        ppid=1,
        pgid=100,
        state_dir="/run-a/solver-state",
    )
    workers = [
        _audit_process(
            pid=pid,
            ppid=100,
            pgid=100,
            state_dir="/run-a/solver-state",
        )
        for pid in range(101, 113)
    ]
    budget = SimpleNamespace(capacity=64)
    captured = {}

    def acquire(requested, *, cpu_budget, processes, current_pid):
        usage = solver_budget.estimate_unmanaged_qcode_usage(
            processes,
            current_pid=current_pid,
        )
        captured.update(
            requested=requested,
            cpu_budget=cpu_budget,
            processes=processes,
            usage=usage,
        )
        return SimpleNamespace(
            cooperative_slots_before=12,
            unmanaged_usage=usage,
            release=lambda: None,
        )

    monkeypatch.setattr(solver_budget, "_read_processes", lambda: [root, *workers])
    monkeypatch.setattr(
        solver_budget,
        "detect_cpu_budget",
        lambda *, affinity: budget,
    )
    monkeypatch.setattr(solver_budget, "acquire_solver_budget", acquire)

    lease = cli._capacity_lease(
        cli.ResourcePolicy(
            solver_slots=1,
            reserve_foreground_cpus=12,
        ),
        tuple(range(64)),
    )
    assert lease is not None
    assert captured["requested"] == 1
    assert captured["usage"].workers == 12
    assert 64 - 12 - captured["usage"].workers - 1 >= 12


def test_cli_has_no_top_level_scientific_import():
    source = Path(cli.__file__).read_text()
    prefix = source.split("def _run_scientific", 1)[0]
    assert "exactification_queue" not in prefix
    assert "import numpy" not in prefix
