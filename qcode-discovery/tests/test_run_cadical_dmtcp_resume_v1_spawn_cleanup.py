from __future__ import annotations

import hashlib
import importlib.util
import signal
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_cadical_dmtcp_resume_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "cadical_dmtcp_resume_v1_cleanup", SOURCE
)
assert SPEC is not None and SPEC.loader is not None
resume_v1 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(resume_v1)


def _make_executable(path: Path, payload: bytes) -> None:
    path.write_bytes(payload)
    path.chmod(0o755)


def _initialized_fake_root(tmp_path: Path) -> Path:
    prefix = tmp_path / "dmtcp"
    (prefix / "bin").mkdir(parents=True)
    (prefix / "lib" / "dmtcp").mkdir(parents=True)
    for name in resume_v1.REQUIRED_DMTCP_BINS:
        rc = 1 if name == "dmtcp_command" else 0
        _make_executable(
            prefix / "bin" / name,
            (
                "#!/bin/sh\n"
                "if [ \"$1\" = \"--version\" ]; then\n"
                f"echo '{name} (DMTCP) 4.2.0'\n"
                f"exit {rc}\n"
                "fi\n"
                "exit 99\n"
            ).encode("ascii"),
        )
    (prefix / "lib" / "dmtcp" / "libdmtcp.so").write_bytes(b"library")
    solver = tmp_path / "solver"
    _make_executable(solver, b"#!/bin/sh\nexit 0\n")
    cnf = tmp_path / "x.cnf"
    cnf.write_bytes(b"p cnf 0 0\n")
    root = tmp_path / "root"
    resume_v1.initialize(
        root,
        cnf=cnf,
        solver=solver,
        dmtcp_prefix=prefix,
        solver_args=[],
        runtime_libs=[],
        runtime_libs_complete=False,
    )
    return root


def test_kill_spawned_group_sends_sigkill_and_waits_for_identity_loss(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    kills: list[tuple[int, signal.Signals]] = []
    monkeypatch.setattr(
        resume_v1,
        "_proc_start_ticks",
        lambda _pid, allow_zombie=False: 5678,
    )
    monkeypatch.setattr(
        resume_v1.os, "killpg", lambda pid, sig: kills.append((pid, sig))
    )
    waits = iter([(0, 0), (1234, 0)])
    monkeypatch.setattr(
        resume_v1.os, "waitpid", lambda _pid, _flags: next(waits)
    )
    monkeypatch.setattr(
        resume_v1, "_pid_identity", lambda _pid, _ticks: True
    )
    monkeypatch.setattr(resume_v1.time, "sleep", lambda _seconds: None)
    resume_v1._kill_spawned_group(1234, 5678)
    assert kills == [(1234, signal.SIGKILL)]


def test_start_readiness_failure_kills_spawned_group_and_keeps_poison_claim(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _initialized_fake_root(tmp_path)
    monkeypatch.setattr(
        resume_v1,
        "_spawn_detached",
        lambda *_args, **_kwargs: (1234, 5678),
    )
    monkeypatch.setattr(
        resume_v1,
        "_wait_ready",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            resume_v1.ResumeControllerError("injected readiness failure")
        ),
    )
    cleaned: list[tuple[int, int]] = []

    def fake_cleanup(pid: int, ticks: int) -> None:
        cleaned.append((pid, ticks))

    monkeypatch.setattr(resume_v1, "_kill_spawned_group", fake_cleanup)
    with pytest.raises(resume_v1.ResumeControllerError, match="readiness"):
        resume_v1.start(root)
    assert cleaned == [(1234, 5678)]
    generation = root / "generations" / "000000"
    assert (generation / "start.claim.json").is_file()
    assert not (generation / "start.commit.json").exists()
    assert resume_v1._claim_without_commit(generation) == "start.claim.json"


def test_client_list_binds_exactly_one_running_real_pid() -> None:
    payload = (
        b"Coordinator:\n"
        b"  Host: 127.0.0.1\n"
        b"  Port: 45678\n"
        b"Client List:\n"
        b"#, PROG[virtPID:realPID]@HOST, DMTCP-UNIQUEPID, STATE, BARRIER\n"
        b"1, cadical[40000:23456]@host, host-40000-abc, WorkerState::RUNNING, \n\n"
    )
    worker = resume_v1._parse_client_list(
        payload, expected_host="127.0.0.1", expected_port=45678
    )
    assert worker["virtual_pid"] == 40000
    assert worker["real_pid"] == 23456
    assert worker["state"] == "WorkerState::RUNNING"
    with pytest.raises(resume_v1.ResumeControllerError, match="exactly one"):
        resume_v1._parse_client_list(
            payload
            + b"2, cadical[40001:23457]@host, host-40001-def, WorkerState::RUNNING, \n",
            expected_host="127.0.0.1",
            expected_port=45678,
        )


def test_resume_readiness_accepts_bootstrap_exit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    port_file = tmp_path / "port"
    port_file.write_text("45678\n", encoding="ascii")
    monkeypatch.setattr(
        resume_v1, "_query_status", lambda _command, _port: (1, True)
    )
    worker = {
        "real_pid": 23456,
        "proc_start_ticks": 9876,
        "virtual_pid": 40000,
    }
    monkeypatch.setattr(
        resume_v1,
        "_query_client_identity",
        lambda _command, _port, expected_program, expected_executable: worker,
    )
    monkeypatch.setattr(
        resume_v1.os, "waitpid", lambda _pid, _flags: (1234, 0)
    )
    assert resume_v1._wait_resume_ready(
        Path("/dmtcp_command"),
        port_file,
        1234,
        expected_program="solver",
        expected_executable=Path("/mtcp_restart"),
    ) == (45678, worker, 0)


def test_live_prefix_hash_allows_only_append(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    proof = tmp_path / "proof.drat"
    proof.write_bytes(b"prefix")
    original = resume_v1._sha256_fd

    def hash_then_append(fd: int, *, limit: int | None = None) -> tuple[str, int]:
        result = original(fd, limit=limit)
        with proof.open("ab") as handle:
            handle.write(b"-new")
        return result

    monkeypatch.setattr(resume_v1, "_sha256_fd", hash_then_append)
    expected = hashlib.sha256(b"prefix").hexdigest()
    assert resume_v1._hash_prefix(proof, 6, allow_append=True) == expected
