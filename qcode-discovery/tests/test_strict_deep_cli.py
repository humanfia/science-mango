from __future__ import annotations

import json
import os
import signal
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

from humanize import strict_deep_cli as cli


def _repo(tmp_path: Path) -> tuple[Path, Path]:
    repo = tmp_path / "repo"
    humanize = repo / "humanize"
    humanize.mkdir(parents=True)
    (humanize / "strict_deep_queue.py").write_text("# sealed queue source\n")
    run = repo / "results" / "humanize" / "pipelines" / "run-a"
    run.mkdir(parents=True)
    return repo, run


def _sources(run: Path) -> tuple[Path, Path]:
    batch = run / "sidecars" / "strict" / "batch-0000"
    batch.mkdir(parents=True)
    ranked, summary = batch / "ranked.jsonl", batch / "summary.json"
    ranked.write_text("{}\n")
    summary.write_text("{}\n")
    return ranked, summary


def _document(*, capacity_poll_s: float = 0.01) -> dict:
    return {
        "expected_digests": list(cli.EXPECTED_DIGESTS),
        "queue": {
            "lanes": [
                {
                    "name": "cadical-seq",
                    "solver": "cadical195",
                    "cardinality_encoding": "seqcounter",
                },
                {
                    "name": "kissat-total",
                    "solver": "kissat404",
                    "cardinality_encoding": "totalizer",
                },
                {
                    "name": "glucose-km",
                    "solver": "glucose42",
                    "cardinality_encoding": "kmtotalizer",
                },
                {
                    "name": "minicard-native",
                    "solver": "minicard",
                    "cardinality_encoding": "native-minicard",
                },
            ],
            "time_slices_s": [1800, 7200, 21600],
            "required_proof_lanes": 2,
            "max_workers": 4,
            "seed": 0,
            "poll_interval_s": 30,
            "stale_after_s": 28800,
            "termination_grace_s": 180,
        },
        "resources": {
            "solver_slots": 4,
            "reserve_foreground_cpus": 12,
            "nice": 15,
            "cpu_list": None,
            "heartbeat_s": 60,
            "capacity_poll_s": capacity_poll_s,
            "termination_grace_s": 180,
        },
    }


def _config(tmp_path: Path, **kwargs) -> Path:
    path = tmp_path / "strict-deep.json"
    path.write_text(json.dumps(_document(**kwargs)) + "\n")
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


def _args(repo, config, ranked, summary):
    return cli.build_parser().parse_args(
        [
            "run",
            "--repo-dir",
            str(repo),
            "--run-id",
            "run-a",
            "--config",
            str(config),
            "--ranked-input",
            str(ranked),
            "--summary-input",
            str(summary),
        ]
    )


def test_parser_has_full_surface_and_requires_explicit_inputs():
    parser = cli.build_parser()
    commands = parser._subparsers._group_actions[0].choices
    assert {"init", "run", "start", "_worker", "status", "cancel"} <= set(commands)
    with pytest.raises(SystemExit):
        parser.parse_args(["run", "--run-id", "r", "--config", "p.json"])
    assert parser.parse_args(["cancel", "--run-id", "r"]).grace_seconds == 180


def test_resource_policy_is_fail_closed():
    policy = cli.ResourcePolicy.from_mapping(_document())
    assert (policy.solver_slots, policy.reserve_foreground_cpus, policy.nice) == (
        4,
        12,
        15,
    )
    for replacement, message in (
        ({"solver_slots": 3}, "solver_slots=4"),
        ({"reserve_foreground_cpus": 11}, "reserve_foreground_cpus=12"),
        ({"nice": 14}, "nice=15"),
        ({"termination_grace_s": 179}, "at least 180"),
    ):
        document = _document()
        document["resources"].update(replacement)
        with pytest.raises(ValueError, match=message):
            cli.ResourcePolicy.from_mapping(document)


def test_config_binds_digest_order_and_rejects_symlink(tmp_path):
    config = _config(tmp_path)
    document, digest, resolved = cli._load_config(config)
    assert document["expected_digests"] == list(cli.EXPECTED_DIGESTS)
    assert len(digest) == 64 and resolved == config.resolve()
    document["expected_digests"].reverse()
    config.write_text(json.dumps(document))
    with pytest.raises(ValueError, match="fixed strict deep digests"):
        cli._load_config(config)
    target = _config(tmp_path)
    link = tmp_path / "link.json"
    link.symlink_to(target)
    with pytest.raises(ValueError, match="non-symlink"):
        cli._load_config(link)


def test_process_record_self_hash_detects_tampering(tmp_path):
    path = tmp_path / "process.json"
    record = cli.write_process_record(
        path,
        {
            "schema_version": 1,
            "kind": cli.PROCESS_KIND,
            "status": "running",
        },
    )
    assert cli.read_process_record(path) == record
    changed = json.loads(path.read_text())
    changed["status"] = "completed"
    path.write_text(json.dumps(changed))
    with pytest.raises(cli.StrictDeepControlError, match="self-hash"):
        cli.read_process_record(path)


def test_start_is_shell_free_isolated_and_source_sealed(tmp_path, monkeypatch):
    repo, run = _repo(tmp_path)
    ranked, summary = _sources(run)
    config = _config(tmp_path)
    paths = cli.control_paths(repo, "run-a", create=True)
    captured = {}

    class FakeProcess:
        pid = 4321

        def poll(self):
            return None

        def terminate(self):
            captured["terminated"] = True

    def popen(command, **kwargs):
        captured.update(command=command, kwargs=kwargs)
        return FakeProcess()

    monkeypatch.setattr(cli.subprocess, "Popen", popen)
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
            "--ranked-input",
            str(ranked),
            "--summary-input",
            str(summary),
            "--python-executable",
            sys.executable,
        ]
    )
    record = cli.start_background(args, paths)
    assert isinstance(captured["command"], list)
    assert captured["kwargs"]["shell"] is False
    assert captured["kwargs"]["start_new_session"] is True
    assert record["pid"] == record["pgid"] == record["session_id"]
    assert record["launcher_source_sha256"] == cli._SOURCE_SHA256
    assert len(record["queue_source_sha256"]) == 64
    assert record["inputs"]["expected_digests"] == list(cli.EXPECTED_DIGESTS)


def test_resource_wait_retries_then_runs_under_lease(tmp_path, monkeypatch):
    repo, run = _repo(tmp_path)
    ranked, summary = _sources(run)
    paths = cli.control_paths(repo, "run-a", create=True)
    args = _args(repo, _config(tmp_path, capacity_poll_s=0.001), ranked, summary)
    events = []

    class Lease:
        def release(self):
            events.append("release")

    def capacity(_policy, _affinity):
        events.append("capacity")
        if events.count("capacity") == 1:
            raise cli.ResourceWait("RESOURCE_WAIT: reserve")
        return Lease()

    monkeypatch.setattr(cli, "_proc_identity", lambda _pid: _identity(os.getpid()))
    monkeypatch.setattr(cli, "_selected_cpus", lambda _policy: (0, 1, 2, 3))
    monkeypatch.setattr(cli, "_capacity_lease", capacity)
    monkeypatch.setattr(
        cli, "_apply_resources", lambda *_args: events.append("resources")
    )
    monkeypatch.setattr(
        cli,
        "_run_scientific",
        lambda **_kwargs: events.append("science") or {"status": "INCOMPLETE"},
    )
    lock_fd = cli._acquire_lock(paths.lock)
    try:
        result = cli._execute_worker(
            args=args, paths=paths, lock_fd=lock_fd, isolated=False
        )
    finally:
        os.close(lock_fd)
    assert result["status"] == "INCOMPLETE"
    assert events == ["capacity", "capacity", "resources", "science", "release"]
    record = cli.read_process_record(paths.process)
    assert record and record["status"] == "completed"


def test_cancel_refuses_pid_reuse_then_signals_only_verified_group(tmp_path):
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
            "command": [sys.executable, "-m", "humanize.strict_deep_cli", "_worker"],
            "resources": {"termination_grace_s": 180},
            "solver_termination_grace_s": 180,
        },
    )
    args = SimpleNamespace(repo_dir=repo, run_id="run-a", grace_seconds=180)
    signals = []
    with pytest.raises(cli.UnsafeProcessError, match="mismatch"):
        cli.cancel_worker(
            args,
            paths,
            identity_reader=lambda _pid: {**identity, "proc_starttime": 100},
            kill_group=lambda pgid, sig: signals.append((pgid, sig)),
        )
    assert not signals
    alive = {"value": True}

    def reader(_pid):
        return identity if alive["value"] else None

    def kill(pgid, sig):
        signals.append((pgid, sig))
        alive["value"] = False

    result = cli.cancel_worker(
        args,
        paths,
        identity_reader=reader,
        kill_group=kill,
        group_members_reader=lambda **_kwargs: [],
    )
    assert result["stopped"] and signals == [(identity["pgid"], signal.SIGTERM)]


def test_cancel_grace_at_least_180(tmp_path):
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
            "command": ["/repo/humanize/strict_deep_cli.py", "_worker"],
            "resources": {"termination_grace_s": 180},
            "solver_termination_grace_s": 180,
        },
    )
    args = SimpleNamespace(repo_dir=repo, run_id="run-a", grace_seconds=179)
    with pytest.raises(ValueError, match="at least 180s"):
        cli.cancel_worker(args, paths, identity_reader=lambda _pid: identity)


def test_checked_in_policy_contract():
    path = (
        Path(cli.__file__).resolve().parent.parent
        / "configs"
        / "stage2_strict_deep_v1.json"
    )
    document, _, _ = cli._load_config(path)
    queue, resources = document["queue"], document["resources"]
    assert queue["time_slices_s"] == [1800, 7200, 21600]
    assert (queue["required_proof_lanes"], queue["max_workers"]) == (2, 4)
    assert len(queue["lanes"]) == len({lane["solver"] for lane in queue["lanes"]}) == 4
    assert (
        resources["solver_slots"],
        resources["reserve_foreground_cpus"],
        resources["nice"],
    ) == (4, 12, 15)


def test_no_top_level_scientific_import():
    prefix = Path(cli.__file__).read_text().split("def _run_scientific", 1)[0]
    assert "from . import strict_deep_queue" not in prefix
    assert "import numpy" not in prefix
