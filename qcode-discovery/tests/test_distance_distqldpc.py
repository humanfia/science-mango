"""Focused soundness and lifecycle tests for the DistQLDPC adapter."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import numpy as np
import pytest

from evaluation import distance_distqldpc as dist


def _steane_matrices() -> tuple[np.ndarray, ...]:
    checks = np.asarray([
        [1, 1, 1, 1, 0, 0, 0],
        [1, 1, 0, 0, 1, 1, 0],
        [1, 0, 1, 0, 1, 0, 1],
    ], dtype=np.uint8)
    logical = np.ones((1, 7), dtype=np.uint8)
    return checks, checks.copy(), logical, logical.copy()


def _write_solver(tmp_path: Path, body: str) -> tuple[Path, str]:
    executable = tmp_path / "fake-distqldpc"
    executable.write_text(
        "#!/usr/bin/env python3\n" + body,
        encoding="utf-8",
    )
    executable.chmod(0o755)
    digest = hashlib.sha256(executable.read_bytes()).hexdigest()
    return executable, digest


def _exact_solver(tmp_path: Path, distance: int = 3) -> tuple[Path, str]:
    return _write_solver(
        tmp_path,
        "\n".join([
            f"print('c d_lb: {distance}')",
            f"print('c d_ub: {distance}')",
            f"print('c d : {distance}')",
            f"print('o {distance}')",
            "",
        ]),
    )


def _solve(
    executable: Path,
    digest: str,
    *,
    max_weight: int = 2,
    cardinality_mode: str = "default",
    checkpoint_path: Path | None = None,
) -> tuple[dict, tuple[np.ndarray, ...]]:
    matrices = _steane_matrices()
    evidence = dist.solve_css_distance_distqldpc_lower(
        *matrices,
        max_weight=max_weight,
        timeout=3,
        binary=executable,
        cardinality_mode=cardinality_mode,
        checkpoint_path=checkpoint_path,
        checkpoint_identity={"test": "binding"},
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
        termination_grace_s=0.2,
    )
    return evidence, matrices


@pytest.mark.parametrize("cardinality_mode", dist.DISTQLDPC_CARDINALITY_MODES)
def test_all_official_cardinality_modes_are_bound_and_replay(
    tmp_path,
    cardinality_mode,
):
    executable, digest = _exact_solver(tmp_path)
    evidence, matrices = _solve(
        executable,
        digest,
        cardinality_mode=cardinality_mode,
    )

    assert evidence["outcome"] == "exact"
    assert evidence["threshold_infeasible"] is True
    assert evidence["command_flags"][1:] == list(
        dist.distqldpc_cardinality_flags(cardinality_mode)
    )
    assert not dist.verify_distqldpc_lower_evidence(
        evidence,
        *matrices,
        max_weight=2,
        cardinality_mode=cardinality_mode,
        expected_checkpoint_identity={"test": "binding"},
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
    )


def test_detector_tamper_fails_even_after_resealing(tmp_path):
    executable, digest = _exact_solver(tmp_path)
    evidence, matrices = _solve(executable, digest)
    tampered = copy.deepcopy(evidence)
    tampered["instance"]["logical_detector"]["verified"] = False
    unsigned_instance = dict(tampered["instance"])
    unsigned_instance.pop("binding_sha256")
    tampered["instance"]["binding_sha256"] = dist._canonical_sha256(
        unsigned_instance
    )
    tampered.pop("evidence_sha256")
    tampered["evidence_sha256"] = dist._canonical_sha256(tampered)

    failures = dist.verify_distqldpc_exact_evidence(
        tampered,
        *matrices,
        max_weight=2,
        expected_checkpoint_identity={"test": "binding"},
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
    )
    assert any("logical detector completeness" in failure for failure in failures)


def test_incomplete_logical_basis_is_rejected_before_launch(tmp_path):
    executable, digest = _exact_solver(tmp_path)
    hx, hz, lx, lz = _steane_matrices()
    with pytest.raises(ValueError, match="duality|completeness"):
        dist.solve_css_distance_distqldpc_lower(
            hx,
            hz,
            lx,
            np.zeros_like(lz),
            max_weight=2,
            timeout=3,
            binary=executable,
            expected_binary_sha256=digest,
            expected_source_commit="test-source",
        )


def test_exact_at_or_below_threshold_is_not_checkpointed_or_resumed(tmp_path):
    counter = tmp_path / "counter"
    executable, digest = _write_solver(
        tmp_path,
        "\n".join([
            "from pathlib import Path",
            f"counter = Path({str(counter)!r})",
            "run = int(counter.read_text()) + 1 if counter.exists() else 1",
            "counter.write_text(str(run))",
            "distance = 3 if run == 1 else 4",
            "print(f'c d_lb: {distance}')",
            "print(f'c d_ub: {distance}')",
            "print(f'c d : {distance}')",
            "print(f'o {distance}')",
            "",
        ]),
    )
    checkpoint = tmp_path / "lower.json"
    first, _ = _solve(
        executable, digest, max_weight=3, checkpoint_path=checkpoint,
    )
    assert first["exact_distance"] == 3
    assert first["threshold_infeasible"] is False
    assert not checkpoint.exists()

    checkpoint.write_text(json.dumps(first), encoding="utf-8")
    second, _ = _solve(
        executable, digest, max_weight=3, checkpoint_path=checkpoint,
    )
    assert second["exact_distance"] == 4
    assert second.get("resumed") is not True
    assert counter.read_text(encoding="utf-8") == "2"


@pytest.mark.parametrize(
    ("body", "expected_outcome"),
    [
        (
            "print('c d_lb: 2')\nprint('c d_ub: 3')\nprint('o 3')\n",
            "solver_error",
        ),
        (
            "print('c d_lb: 2')\nprint('c d_ub: 3')\n"
            "print('o 3')\nprint('c status: TIMEOUT')\n",
            "hard_timeout",
        ),
    ],
)
def test_o_only_and_timeout_output_never_become_terminal_lower(
    tmp_path,
    body,
    expected_outcome,
):
    executable, digest = _write_solver(tmp_path, body)
    checkpoint = tmp_path / "lower.json"
    evidence, matrices = _solve(
        executable, digest, checkpoint_path=checkpoint,
    )
    assert evidence["outcome"] == expected_outcome
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert dist.verify_distqldpc_lower_evidence(
        evidence,
        *matrices,
        max_weight=2,
        expected_checkpoint_identity={"test": "binding"},
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
    )
    assert not checkpoint.exists()


@pytest.mark.skipif(os.name != "posix", reason="requires POSIX process groups")
@pytest.mark.parametrize("capture_kind", ["invalid-utf8", "oversize"])
def test_dead_leader_surviving_descendant_is_reaped_before_capture_errors(
    tmp_path,
    monkeypatch,
    capture_kind,
):
    child_pid_path = tmp_path / "child.pid"
    payload = (
        "sys.stdout.buffer.write(b'\\xff')"
        if capture_kind == "invalid-utf8"
        else "sys.stdout.write('x' * 128)"
    )
    executable, digest = _write_solver(
        tmp_path,
        "\n".join([
            "import os, sys, time",
            "from pathlib import Path",
            "child = os.fork()",
            "if child == 0:",
            "    time.sleep(60)",
            "    os._exit(0)",
            f"Path({str(child_pid_path)!r}).write_text(str(child))",
            payload,
            "",
        ]),
    )
    if capture_kind == "oversize":
        monkeypatch.setattr(dist, "_MAX_CAPTURE_BYTES", 64)
    evidence, _ = _solve(executable, digest)

    assert evidence["outcome"] == "solver_error"
    cleanup = evidence["cleanup"]
    assert cleanup is None or cleanup["group_survived"] is False
    child_pid = int(child_pid_path.read_text(encoding="utf-8"))
    deadline = time.monotonic() + 2
    while Path(f"/proc/{child_pid}").exists() and time.monotonic() < deadline:
        time.sleep(0.01)
    assert not Path(f"/proc/{child_pid}").exists()


def test_runtime_source_identity_tamper_fails_after_resealing(tmp_path):
    executable, digest = _exact_solver(tmp_path)
    evidence, matrices = _solve(executable, digest)
    tampered = copy.deepcopy(evidence)
    runtime = tampered["instance"]["solver_execution"]["runtime_source"]
    runtime["supervisor"]["sha256"] = "0" * 64
    unsigned_runtime = dict(runtime)
    unsigned_runtime.pop("identity_sha256")
    runtime["identity_sha256"] = dist._canonical_sha256(unsigned_runtime)
    unsigned_instance = dict(tampered["instance"])
    unsigned_instance.pop("binding_sha256")
    tampered["instance"]["binding_sha256"] = dist._canonical_sha256(
        unsigned_instance
    )
    tampered.pop("evidence_sha256")
    tampered["evidence_sha256"] = dist._canonical_sha256(tampered)

    failures = dist.verify_distqldpc_exact_evidence(
        tampered,
        *matrices,
        max_weight=2,
        expected_checkpoint_identity={"test": "binding"},
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
    )
    assert any("solver execution mode" in failure for failure in failures)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires Linux PDEATHSIG and /proc",
)
def test_supervisor_reaps_forked_solver_tree_when_owner_is_killed(tmp_path):
    supervisor_pid_path = tmp_path / "supervisor.pid"
    solver_pid_path = tmp_path / "solver.pid"
    forked_pid_path = tmp_path / "forked.pid"
    executable, _digest = _write_solver(
        tmp_path,
        "\n".join([
            "import os, signal, time",
            "from pathlib import Path",
            "signal.signal(signal.SIGTERM, signal.SIG_IGN)",
            "child = os.fork()",
            "if child == 0:",
            f"    Path({str(forked_pid_path)!r}).write_text(str(os.getpid()))",
            "    while True: time.sleep(60)",
            f"Path({str(solver_pid_path)!r}).write_text(str(os.getpid()))",
            "while True: time.sleep(60)",
            "",
        ]),
    )
    supervisor = Path(dist.__file__).with_name("distqldpc_supervisor.py")
    owner_code = "\n".join([
        "import os, subprocess, sys, time",
        "from pathlib import Path",
        "process = subprocess.Popen([",
        "    sys.executable, '-I', '-B',",
        f"    {str(supervisor)!r},",
        "    '--expected-parent-pid', str(os.getpid()),",
        "    '--termination-grace-s', '0.2',",
        "    '--absolute-cleanup-deadline',",
        "    str(time.monotonic() + 10),",
        f"    '--', {str(executable)!r},",
        "], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,",
        "   stderr=subprocess.DEVNULL, start_new_session=True)",
        f"Path({str(supervisor_pid_path)!r}).write_text(str(process.pid))",
        "time.sleep(60)",
    ])
    owner = subprocess.Popen(
        [sys.executable, "-c", owner_code],
        start_new_session=True,
    )
    known_pids: list[int] = []
    try:
        paths = (supervisor_pid_path, solver_pid_path, forked_pid_path)
        deadline = time.monotonic() + 5
        while (
            not all(path.exists() for path in paths)
            and owner.poll() is None
            and time.monotonic() < deadline
        ):
            time.sleep(0.01)
        assert owner.poll() is None
        assert all(path.exists() for path in paths)
        known_pids = [
            int(path.read_text(encoding="utf-8")) for path in paths
        ]
        supervisor_pid, solver_pid, forked_pid = known_pids
        assert os.getpgid(supervisor_pid) == supervisor_pid
        assert os.getsid(supervisor_pid) == supervisor_pid
        assert os.getpgid(solver_pid) == supervisor_pid
        assert os.getpgid(forked_pid) == supervisor_pid

        os.kill(owner.pid, signal.SIGKILL)
        owner.wait(timeout=2)
        deadline = time.monotonic() + 5
        while (
            any(Path(f"/proc/{pid}").exists() for pid in known_pids)
            and time.monotonic() < deadline
        ):
            time.sleep(0.01)
        assert not [
            pid for pid in known_pids if Path(f"/proc/{pid}").exists()
        ]
    finally:
        if owner.poll() is None:
            os.kill(owner.pid, signal.SIGKILL)
            owner.wait(timeout=2)
        if known_pids:
            supervisor_pid = known_pids[0]
            try:
                if os.getpgid(supervisor_pid) == supervisor_pid:
                    os.killpg(supervisor_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


@pytest.mark.skipif(os.name != "posix", reason="requires POSIX process groups")
def test_cleanup_absolute_deadline_does_not_renew_grace(tmp_path):
    ready = tmp_path / "ready"
    executable, _digest = _write_solver(
        tmp_path,
        "\n".join([
            "import signal, time",
            "from pathlib import Path",
            "signal.signal(signal.SIGTERM, signal.SIG_IGN)",
            f"Path({str(ready)!r}).write_text('ready')",
            "while True: time.sleep(60)",
            "",
        ]),
    )
    process = subprocess.Popen(
        [str(executable)],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    try:
        ready_deadline = time.monotonic() + 2
        while not ready.exists() and time.monotonic() < ready_deadline:
            time.sleep(0.01)
        assert ready.exists()
        cleanup_started = time.monotonic()
        report = dist._terminate_process_group(
            process,
            grace_s=5.0,
            absolute_deadline=cleanup_started + 0.2,
        )
        elapsed = time.monotonic() - cleanup_started

        assert elapsed < 0.7
        assert report["sent_sigkill"] is True
        assert report["leader_reaped"] is True
        assert report["group_survived"] is False
        assert process.poll() is not None
        assert not Path(f"/proc/{process.pid}").exists()
    finally:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=2)
