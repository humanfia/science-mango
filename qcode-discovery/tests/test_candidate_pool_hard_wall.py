"""Process-level liveness tests for Stage 2 and certificate pools."""

from __future__ import annotations

import json
import os
import signal
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import pytest

import scripts.audit_candidate_pool as candidate_pool
from evaluation.process_hard_wall import terminate_process_pool


pytestmark = pytest.mark.skipif(
    not hasattr(signal, "SIGKILL"),
    reason="proof hard-wall tests require POSIX process signals",
)


def _ignore_term_forever(pid_path: str) -> None:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    Path(pid_path).write_text(str(os.getpid()))
    while True:
        signal.pause()


def _stage2_partial_then_hang(payload) -> dict:
    candidate, config = payload
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    digest = str(candidate["triage_identity"]["canonical_digest"])
    paths = candidate_pool.state_paths(config.state_dir, digest)
    fixture = candidate["_partial_checkpoint_fixture"]
    construction = fixture["construction"]
    symmetry = fixture["translation_symmetry"]
    candidate_pool.write_artifact(
        paths["audit"],
        construction,
        [fixture["sector"]],
        threshold_only=True,
        translation_symmetry=symmetry,
        cache_binding=fixture["cache_binding"],
    )
    (config.state_dir / "stage2-worker.pid").write_text(str(os.getpid()))
    while True:
        signal.pause()


def _certificate_checkpoint_then_hang(payload):
    _candidate, digest, config, _certifier = payload
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    paths = candidate_pool.state_paths(config.state_dir, digest)
    paths["certificate_checkpoint"].parent.mkdir(parents=True, exist_ok=True)
    paths["certificate_checkpoint"].write_text(
        json.dumps({"directions": [{"position": 0}]})
    )
    (config.state_dir / "certificate-worker.pid").write_text(str(os.getpid()))
    while True:
        signal.pause()


def _candidate(digest: str = "hard-wall-candidate") -> dict:
    return {
        "source": "hard-wall-test",
        "ell": 6,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
        "n": 72,
        "k": 12,
        "required_distance": 7,
        "canonical_digest": digest,
        "triage_identity": {"canonical_digest": digest},
    }


def _assert_process_gone(pid: int) -> None:
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


def test_pool_termination_escalates_to_kill_and_reaps_worker(tmp_path):
    executor = ProcessPoolExecutor(max_workers=1)
    executor.submit(_ignore_term_forever, str(tmp_path / "worker.pid"))
    deadline = time.monotonic() + 5
    while not (tmp_path / "worker.pid").exists():
        assert time.monotonic() < deadline
        time.sleep(0.01)
    pid = int((tmp_path / "worker.pid").read_text())

    report = terminate_process_pool(executor, grace_s=0.05)

    assert pid in report["forced_worker_pids"]
    _assert_process_gone(pid)


def test_stage2_single_worker_hard_wall_keeps_partial_checkpoint(
    tmp_path, monkeypatch,
):
    monkeypatch.setattr(
        candidate_pool, "_audit_worker", _stage2_partial_then_hang,
    )
    config = candidate_pool.AuditConfig(
        state_dir=tmp_path,
        # Leave enough time for the child to start and durably install the
        # pre-built checkpoint fixture before exercising the hard wall.
        candidate_hard_timeout_s=1.0,
        hard_wall_termination_grace_s=0.05,
    )
    candidate = _candidate()
    digest = str(candidate["triage_identity"]["canonical_digest"])
    construction = candidate_pool._construction_candidate(candidate, digest)
    symmetry = candidate_pool.verify_bb_translation_symmetry(construction)
    assert symmetry["verified"] is True
    candidate["_partial_checkpoint_fixture"] = {
        "construction": construction,
        "translation_symmetry": symmetry,
        "cache_binding": candidate_pool._stage2_audit_cache_binding(
            construction,
            symmetry,
        ),
        "sector": {
            "sector": "X",
            "formulation": "css-sector-xor-cpsat-v1",
            "solver": "ortools-cp-sat",
            "success": False,
            "threshold_infeasible": True,
            "status_name": "INFEASIBLE",
            "max_weight": int(construction["required_distance"]) - 1,
            "operator": None,
            "objective": None,
            "anchor_indices": symmetry["orbit_representatives"],
        },
    }

    started = time.monotonic()
    results = candidate_pool.audit_selected_candidates(
        [candidate],
        config,
        candidate_workers=1,
    )

    # The one-second worker wall is followed by an authoritative reconstruction
    # and replay in the parent.  That replay is intentionally outside the
    # solver wall and may import/build qLDPC state on a cold test process.
    assert time.monotonic() - started < 10
    assert results[0]["status"] == "UNRESOLVED"
    assert results[0]["completed_sectors"] == 1
    assert results[0]["hard_wall"]["timed_out"] is True
    _assert_process_gone(int((tmp_path / "stage2-worker.pid").read_text()))


def test_certificate_single_worker_hard_wall_keeps_direction_checkpoint(
    tmp_path, monkeypatch,
):
    monkeypatch.setattr(
        candidate_pool,
        "_certificate_worker",
        _certificate_checkpoint_then_hang,
    )
    config = candidate_pool.AuditConfig(
        state_dir=tmp_path,
        certificate_hard_timeout_s=0.15,
        hard_wall_termination_grace_s=0.05,
    )

    results = candidate_pool.certify_selected_candidates(
        [_candidate()],
        config,
        certificate_workers=1,
        max_total_workers=1,
    )

    result = results["hard-wall-candidate"]
    assert result["hard_wall"]["timed_out"] is True
    assert "hard-wall timeout" in result["error"]
    checkpoint = candidate_pool.state_paths(
        tmp_path, "hard-wall-candidate"
    )["certificate_checkpoint"]
    assert json.loads(checkpoint.read_text())["directions"] == [{"position": 0}]
    _assert_process_gone(
        int((tmp_path / "certificate-worker.pid").read_text())
    )


def test_certificate_hard_wall_does_not_bypass_worker_budget(tmp_path):
    config = candidate_pool.AuditConfig(
        state_dir=tmp_path,
        certificate_solver_workers=3,
    )
    with pytest.raises(ValueError, match="exceeds max_total_workers"):
        candidate_pool.certify_selected_candidates(
            [_candidate()],
            config,
            certificate_workers=2,
            max_total_workers=5,
        )
