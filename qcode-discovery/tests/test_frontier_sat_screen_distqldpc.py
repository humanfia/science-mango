"""Focused integration tests for DistQLDPC Stage-3 lower lanes."""

from __future__ import annotations

import hashlib
import json
import threading
import time
from pathlib import Path

import numpy as np
import pytest

from evaluation.admissibility_policy import (
    css_w6_admissibility_binding,
)
from evaluation import distance_distqldpc as dist
from evaluation.distance_sat import SAT_EVIDENCE_KIND, SAT_EVIDENCE_SCHEMA_VERSION
from evaluation.target_policy import TARGET_MODE_SCALAR_13_INCLUSIVE
from scripts import screen_frontier_sat as screen


def _steane_matrices() -> tuple[np.ndarray, ...]:
    checks = np.asarray([
        [1, 1, 1, 1, 0, 0, 0],
        [1, 1, 0, 0, 1, 1, 0],
        [1, 0, 1, 0, 1, 0, 1],
    ], dtype=np.uint8)
    logical = np.ones((1, 7), dtype=np.uint8)
    return checks, checks.copy(), logical, logical.copy()


def _candidate() -> dict:
    return {
        "k": 1,
        "required_distance": 3,
        "canonical_digest": "distqldpc-screen-test",
    }


def test_distqldpc_checkpoint_identity_binds_optional_css_w6_policy():
    legacy = _candidate()
    assert screen._admissibility_checkpoint_fields(legacy) == {}
    with pytest.raises(ValueError, match="lacks CSS weight-6 policy"):
        screen._admissibility_checkpoint_fields(
            {**legacy, "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE},
        )

    binding = css_w6_admissibility_binding()
    candidate = {**legacy, "admissibility": binding}
    assert screen._admissibility_checkpoint_fields(candidate) == {
        "admissibility_binding_sha256": binding["binding_sha256"],
    }

    with pytest.raises(ValueError, match="missing or stale"):
        screen._admissibility_checkpoint_fields(
            {**legacy, "admissibility": {**binding, "maximum": 7}},
        )


def _write_portfolio_solver(tmp_path: Path) -> tuple[Path, str]:
    executable = tmp_path / "fake-distqldpc-portfolio"
    executable.write_text(
        """#!/usr/bin/env python3
import sys
if '-card-sinz' in sys.argv:
    print('c d_lb: 2')
    print('c d_ub: 3')
    print('o 3')
    print('c status: TIMEOUT')
else:
    distance = 4 if '-no-card' in sys.argv else (2 if '-card-mto' in sys.argv else 3)
    print(f'c d_lb: {distance}')
    print(f'c d_ub: {distance}')
    print(f'c d : {distance}')
    print(f'o {distance}')
""",
        encoding="utf-8",
    )
    executable.chmod(0o755)
    return executable, hashlib.sha256(executable.read_bytes()).hexdigest()


def _context(tmp_path: Path, monkeypatch):
    matrices = _steane_matrices()
    detector = screen.verify_css_logical_detectors(*matrices)
    assert detector["verified"] is True
    candidate = _candidate()
    executable, digest = _write_portfolio_solver(tmp_path)

    def exact_verifier(evidence, *args, **kwargs):
        return dist.verify_distqldpc_exact_evidence(
            evidence,
            *args,
            **kwargs,
            expected_binary_sha256=digest,
            expected_source_commit="test-source",
        )

    def lower_verifier(evidence, *args, **kwargs):
        return dist.verify_distqldpc_lower_evidence(
            evidence,
            *args,
            **kwargs,
            expected_binary_sha256=digest,
            expected_source_commit="test-source",
        )

    monkeypatch.setattr(screen, "verify_distqldpc_exact_evidence", exact_verifier)
    monkeypatch.setattr(screen, "verify_distqldpc_lower_evidence", lower_verifier)
    return candidate, matrices, detector, executable, digest


def _external_unit(context, mode: str) -> tuple[str, dict]:
    candidate, matrices, detector, executable, digest = context
    identity = screen.distqldpc_stage3_checkpoint_identity(
        candidate,
        cardinality_mode=mode,
        coverage_mode="global",
        logical_detector=detector,
        translation_symmetry=None,
        construction_symmetry=None,
        xz_sector_isometry=None,
    )
    evidence = dist.solve_css_distance_distqldpc_lower(
        *matrices,
        max_weight=2,
        timeout=3,
        binary=executable,
        cardinality_mode=mode,
        checkpoint_identity=identity,
        expected_binary_sha256=digest,
        expected_source_commit="test-source",
    )
    phase = screen._distqldpc_phase(mode)
    key = screen._unit_key(phase, "XZ", None)
    return key, {
        "unit_id": key,
        "phase": phase,
        "sector": "XZ",
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": evidence,
    }


def _pysat_evidence(outcome: str, threshold: int, objective=None) -> dict:
    evidence = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "outcome": outcome,
        "decision_complete": True,
        "threshold_infeasible": outcome == "unsat",
        "retryable": False,
        "max_weight": threshold,
        "operator": None if outcome == "unsat" else {"test": True},
        "objective": objective,
        "zero_anchor_indices": [],
        "one_anchor_index": None,
        "anchor_cube_sha256": None,
    }
    evidence["evidence_sha256"] = screen._canonical_sha256(evidence)
    return evidence


def _pysat_unit(phase: str, sector: str, evidence: dict) -> tuple[str, dict]:
    key = screen._unit_key(phase, sector, None)
    return key, {
        "unit_id": key,
        "phase": phase,
        "sector": sector,
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": evidence,
    }


def _artifact(context, units: dict) -> dict:
    candidate, matrices, detector, _executable, _digest = context
    return screen._artifact(
        candidate,
        mode="global",
        translation_symmetry=None,
        logical_detector=detector,
        units=units,
        expected_units=9,
        started=time.monotonic(),
        lower_backend="distqldpc",
        hx=matrices[0],
        hz=matrices[1],
        lx=matrices[2],
        lz=matrices[3],
    )


def test_distqldpc_plan_prefixes_five_modes_and_keeps_pysat_fallback():
    plan = screen._proof_plan("global", 1, lower_backend="distqldpc")
    assert plan[:5] == [
        (screen._distqldpc_phase(mode), "XZ", None, None)
        for mode in dist.DISTQLDPC_CARDINALITY_MODES
    ]
    assert plan[5:] == screen._proof_plan("global", 1)


def test_any_one_external_lower_proves_threshold_and_upper_completes_exact(
    tmp_path,
    monkeypatch,
):
    context = _context(tmp_path, monkeypatch)
    external_key, external = _external_unit(context, "default")
    threshold = _artifact(context, {external_key: external})
    assert threshold["status"] == "THRESHOLD_PROVEN"
    assert threshold["lower_bound_backend"] == "distqldpc"
    assert threshold["distqldpc_exact_distances"] == [3]
    assert threshold["completed_lower_decisions"] == 1

    upper_key, upper = _pysat_unit(
        "upper", "X", _pysat_evidence("sat", 3, objective=3),
    )
    exact = _artifact(context, {external_key: external, upper_key: upper})
    assert exact["status"] == "EXACT_PROVEN"
    assert exact["distqldpc_conflict"] is False


def test_different_external_exact_values_fail_closed(tmp_path, monkeypatch):
    context = _context(tmp_path, monkeypatch)
    units = dict([
        _external_unit(context, "default"),
        _external_unit(context, "no-card"),
    ])
    artifact = _artifact(context, units)
    assert artifact["status"] == "UNRESOLVED"
    assert artifact["distqldpc_conflict"] is True
    assert artifact["distqldpc_exact_distances"] == [3, 4]
    assert artifact["lower_bound_decisions"] == []


def test_external_distance_disagreeing_with_upper_witness_fails_closed(
    tmp_path,
    monkeypatch,
):
    context = _context(tmp_path, monkeypatch)
    units = dict([
        _external_unit(context, "no-card"),
        _pysat_unit("upper", "X", _pysat_evidence("sat", 3, objective=3)),
    ])
    artifact = _artifact(context, units)
    assert artifact["status"] == "UNRESOLVED"
    assert artifact["distqldpc_conflict"] is True
    assert artifact["upper_witness"]["solver_evidence"]["objective"] == 3


def test_external_exact_conflicting_with_pysat_unsat_fails_whole_artifact(
    tmp_path,
    monkeypatch,
):
    context = _context(tmp_path, monkeypatch)
    lower_units = dict([
        _pysat_unit("lower", "X", _pysat_evidence("unsat", 2)),
        _pysat_unit("lower", "Z", _pysat_evidence("unsat", 2)),
    ])
    low_external = dict([_external_unit(context, "mto")])
    artifact = _artifact(context, {**lower_units, **low_external})
    assert artifact["status"] == "UNRESOLVED"
    assert artifact["distqldpc_conflict"] is True

    upper_units = dict([
        _pysat_unit("upper", "X", _pysat_evidence("unsat", 3)),
        _pysat_unit("upper", "Z", _pysat_evidence("unsat", 3)),
    ])
    exact_external = dict([_external_unit(context, "default")])
    artifact = _artifact(context, {**upper_units, **exact_external})
    assert artifact["status"] == "UNRESOLVED"
    assert artifact["distqldpc_conflict"] is True


def test_d_at_or_below_threshold_never_promotes_and_pysat_can_fallback(
    tmp_path,
    monkeypatch,
):
    context = _context(tmp_path, monkeypatch)
    low_key, low_external = _external_unit(context, "mto")
    unresolved = _artifact(context, {low_key: low_external})
    assert unresolved["status"] == "UNRESOLVED"
    assert unresolved["distqldpc_exact_distances"] == [2]
    assert unresolved["distqldpc_lower_decisions"] == []

    timeout_key, timeout_external = _external_unit(context, "sinz")
    fallback_units = dict([
        (timeout_key, timeout_external),
        _pysat_unit("lower", "X", _pysat_evidence("unsat", 2)),
        _pysat_unit("lower", "Z", _pysat_evidence("unsat", 2)),
        _pysat_unit("upper", "X", _pysat_evidence("sat", 3, objective=3)),
    ])
    fallback = _artifact(context, fallback_units)
    assert fallback["status"] == "EXACT_PROVEN"
    assert fallback["lower_bound_backend"] == "pysat"
    assert fallback["distqldpc_exact_distances"] == []


def test_workers_five_replay_then_reserves_pysat_fallback_slot():
    def job(phase: str, *, replay: bool = False):
        sector = "XZ" if phase.startswith(screen.DISTQLDPC_PHASE_PREFIX) else "X"
        return ((phase, sector, None, None), 0, {}, replay)

    upper_replay = job("upper", replay=True)
    external = [
        job(screen._distqldpc_phase(mode))
        for mode in dist.DISTQLDPC_CARDINALITY_MODES
    ]
    pysat_fallback = job("lower")
    ordered = screen._distqldpc_fair_job_order(
        [upper_replay, *external, pysat_fallback, job("upper")],
        workers=5,
    )

    first_wave = ordered[:5]
    assert first_wave[0] is upper_replay
    assert sum(
        screen._distqldpc_mode_from_phase(item[0][0]) is not None
        for item in first_wave
    ) == 4
    # The replay occupies one of at most five active slots.  Once it returns,
    # the queued PySAT lower lane starts before the fifth external mode.
    assert ordered[5] is pysat_fallback
    assert screen._distqldpc_mode_from_phase(ordered[6][0][0]) is not None

    without_replay = screen._distqldpc_fair_job_order(
        [*external, pysat_fallback],
        workers=6,
    )
    assert without_replay[:5] == external
    assert without_replay[5] is pysat_fallback


@pytest.mark.parametrize(
    (
        "external_distances",
        "completion_order",
        "expected_status",
        "workers",
        "expected_new_phases",
    ),
    [
        ({"mto": 2}, ("upper", "mto"), "EXACT_PROVEN", 2, ()),
        ({"mto": 2}, ("mto", "upper"), "EXACT_PROVEN", 2, ()),
        (
            {"mto": 2, "no-card": 3},
            ("mto", "upper", "no-card"),
            "UNRESOLVED",
            2,
            (),
        ),
        (
            {},
            ("upper", "default", "lower"),
            "EXACT_PROVEN",
            2,
            ("lower-distqldpc-default", "lower"),
        ),
    ],
)
def test_replay_barrier_drains_before_admitting_new_solver_work(
    tmp_path,
    monkeypatch,
    external_distances,
    completion_order,
    expected_status,
    workers,
    expected_new_phases,
):
    """Replay completion order cannot leak a fresh solver past the barrier."""

    candidate = {
        "ell": 1,
        "m": 1,
        "n": 2,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "replay-barrier",
    }
    hx = np.array([[1, 1]], dtype=np.uint8)
    hz = np.zeros((0, 2), dtype=np.uint8)
    lx = np.array([[1, 0]], dtype=np.uint8)
    lz = np.array([[1, 1]], dtype=np.uint8)
    matrices = (hx, hz, lx, lz)
    detector = screen.verify_css_logical_detectors(*matrices)
    assert detector["verified"] is True
    symmetry = {"verified": True, "orbit_representatives": [0]}
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "i" * 64,
    }
    cubes = screen.build_anchor_cover_cubes((0,))
    plan = screen._proof_plan(
        "first-nonzero",
        1,
        ("X",),
        cubes,
        "distqldpc",
    )

    external_evidence = {
        mode: {
            "evidence_kind": dist.DISTQLDPC_EVIDENCE_KIND,
            "outcome": "exact",
            "decision_complete": True,
            "threshold_infeasible": True,
            "retryable": False,
            "exact_distance": distance,
            "max_weight": 1,
            "hard_timeout_s": 10.0,
        }
        for mode, distance in external_distances.items()
    }
    upper_evidence = _pysat_evidence("sat", 2, objective=2)
    units = {}
    for mode, evidence in external_evidence.items():
        phase = screen._distqldpc_phase(mode)
        key = screen._unit_key(phase, "XZ", None)
        units[key] = {
            "unit_id": key,
            "phase": phase,
            "sector": "XZ",
            "partition_index": None,
            "anchor_cube": None,
            "solver_evidence": evidence,
        }
    upper_key = screen._unit_key("upper", "X", None)
    units[upper_key] = {
        "unit_id": upper_key,
        "phase": "upper",
        "sector": "X",
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": upper_evidence,
    }

    monkeypatch.setattr(
        screen,
        "verify_distqldpc_exact_evidence",
        lambda *_args, **_kwargs: [],
    )
    monkeypatch.setattr(
        screen,
        "verify_distqldpc_lower_evidence",
        lambda *_args, **_kwargs: [],
    )
    aggregate = screen._artifact(
        candidate,
        mode="first-nonzero",
        translation_symmetry=symmetry,
        logical_detector=detector,
        units=units,
        expected_units=len(plan),
        started=time.monotonic(),
        xz_sector_isometry=isometry,
        proof_sectors=("X",),
        anchor_cover_cubes=cubes,
        lower_backend="distqldpc",
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    )
    output = tmp_path / "candidate.json"
    output.write_text(json.dumps(aggregate), encoding="utf-8")

    monkeypatch.setattr(screen, "build_candidate_code", lambda _claim: object())
    monkeypatch.setattr(
        screen,
        "validate_candidate_parameters",
        lambda _claim, _code: {
            "n": 2,
            "k": 1,
            "required_distance": 2,
        },
    )
    monkeypatch.setattr(screen, "get_code_matrices", lambda _code: matrices)
    monkeypatch.setattr(
        screen,
        "verify_bb_translation_symmetry",
        lambda _claim: symmetry,
    )
    monkeypatch.setattr(
        screen,
        "verify_bb_xz_sector_isometry",
        lambda *_args, **_kwargs: isometry,
    )
    monkeypatch.setattr(
        screen,
        "verify_css_threshold_sat_witness",
        lambda *_args, **_kwargs: [],
    )

    def external_solver(*_args, cardinality_mode, **_kwargs):
        if cardinality_mode in external_evidence:
            evidence = dict(external_evidence[cardinality_mode])
            evidence["resumed"] = True
        else:
            assert cardinality_mode == "default"
            evidence = {
                "evidence_kind": dist.DISTQLDPC_EVIDENCE_KIND,
                "outcome": "exact",
                "decision_complete": True,
                "threshold_infeasible": True,
                "retryable": False,
                "exact_distance": 2,
                "max_weight": 1,
                "hard_timeout_s": 10.0,
                "resumed": False,
            }
        return evidence

    def pysat_solver(_checks, _logicals, **kwargs):
        if kwargs["max_weight"] == 2:
            evidence = dict(upper_evidence)
            evidence["resumed"] = True
        else:
            assert kwargs["cancel_event"].is_set()
            evidence = {
                "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
                "evidence_kind": SAT_EVIDENCE_KIND,
                "outcome": "cancelled",
                "decision_complete": False,
                "threshold_infeasible": False,
                "retryable": True,
                "max_weight": kwargs["max_weight"],
                "operator": None,
                "objective": None,
                "zero_anchor_indices": list(
                    kwargs.get("zero_anchor_indices") or ()
                ),
                "one_anchor_index": kwargs.get("one_anchor_index"),
                "anchor_cube_sha256": kwargs.get("anchor_cube_sha256"),
                "hard_timeout_s": kwargs["timeout"],
                "resumed": False,
            }
        evidence.pop("evidence_sha256", None)
        evidence["evidence_sha256"] = screen._canonical_sha256(evidence)
        return evidence

    monkeypatch.setattr(
        screen,
        "solve_css_distance_distqldpc_lower",
        external_solver,
    )
    monkeypatch.setattr(screen, "solve_css_sector_sat", pysat_solver)

    submitted = []

    class ControlledFuture:
        def __init__(self, function, job):
            self.function = function
            self.job = job
            self.value = None
            self.finished = False

        def run(self):
            assert not self.finished
            self.value = self.function(self.job)
            self.finished = True

        def result(self):
            assert self.finished
            return self.value

        def cancel(self):
            return False

    class ControlledExecutor:
        def __init__(self, *, max_workers):
            assert max_workers == workers

        def submit(self, function, job):
            if not job[3]:
                assert job[0][0] in expected_new_phases
            future = ControlledFuture(function, job)
            submitted.append(future)
            return future

        def shutdown(self, *, wait, cancel_futures):
            assert wait is True
            assert cancel_futures is True

    pending_order = [
        item
        if item in {"upper", "lower"}
        else screen._distqldpc_phase(item)
        for item in completion_order
    ]

    def controlled_wait(futures, *, timeout, return_when):
        del timeout
        assert return_when == screen.FIRST_COMPLETED
        if len(pending_order) == len(completion_order):
            expected_initial_replays = min(
                workers, len(external_distances) + 1
            )
            assert len(submitted) == expected_initial_replays
            assert all(future.job[3] is True for future in submitted)
        phase = pending_order.pop(0)
        future = next(item for item in futures if item.job[0][0] == phase)
        future.run()
        return {future}, set(futures) - {future}

    monkeypatch.setattr(screen, "ThreadPoolExecutor", ControlledExecutor)
    monkeypatch.setattr(screen, "wait", controlled_wait)
    result = screen.screen_sat_candidate(
        candidate,
        output=output,
        timeout=10,
        workers=workers,
        resume=True,
        lower_backend="distqldpc",
    )

    assert pending_order == []
    assert len(submitted) == (
        len(external_distances) + 1 + len(expected_new_phases)
    )
    assert [
        future.job[0][0] for future in submitted if not future.job[3]
    ] == list(expected_new_phases)
    assert result["status"] == expected_status
    assert result["distqldpc_conflict"] is (
        len(set(external_distances.values())) > 1
    )


def test_resume_rejects_exact_evidence_relabelled_to_another_mode(
    tmp_path,
    monkeypatch,
):
    context = _context(tmp_path, monkeypatch)
    _default_key, relabelled = _external_unit(context, "default")
    wrong_phase = screen._distqldpc_phase("no-card")
    wrong_key = screen._unit_key(wrong_phase, "XZ", None)
    relabelled = {
        **relabelled,
        "unit_id": wrong_key,
        "phase": wrong_phase,
    }
    artifact = _artifact(context, {wrong_key: relabelled})
    output = tmp_path / "relabelled.json"
    output.write_text(json.dumps(artifact), encoding="utf-8")
    candidate, matrices, detector, _executable, _digest = context

    resumed = screen._resume_units(
        output,
        candidate=candidate,
        mode="global",
        plan=screen._proof_plan(
            "global", 1, lower_backend="distqldpc",
        ),
        anchor_cover_cubes=None,
        translation_symmetry=None,
        logical_detector=detector,
        xz_sector_isometry=None,
        lower_backend="distqldpc",
        hx=matrices[0],
        hz=matrices[1],
        lx=matrices[2],
        lz=matrices[3],
    )
    assert wrong_key not in resumed


@pytest.mark.parametrize("conflicting_exact", [False, True])
def test_external_terminal_cancels_and_joins_all_active_lanes(
    tmp_path,
    monkeypatch,
    conflicting_exact,
):
    candidate = {
        "ell": 1, "m": 1, "n": 2, "k": 1,
        "required_distance": 2, "canonical_digest": "external-cancel",
    }
    hx = np.array([[1, 1]], dtype=np.uint8)
    hz = np.zeros((0, 2), dtype=np.uint8)
    lx = np.array([[1, 0]], dtype=np.uint8)
    lz = np.array([[1, 1]], dtype=np.uint8)
    barrier = threading.Barrier(6)
    exited: list[str] = []

    monkeypatch.setattr(screen, "build_candidate_code", lambda _claim: object())
    monkeypatch.setattr(
        screen, "validate_candidate_parameters",
        lambda _claim, _code: {"n": 2, "k": 1, "required_distance": 2},
    )
    monkeypatch.setattr(screen, "get_code_matrices", lambda _code: (hx, hz, lx, lz))
    monkeypatch.setattr(
        screen, "verify_bb_translation_symmetry",
        lambda _claim: {"verified": True, "orbit_representatives": [0]},
    )
    monkeypatch.setattr(
        screen, "verify_bb_xz_sector_isometry",
        lambda *_args, **_kwargs: {
            "verified": True, "canonical_sector": "X",
            "covered_sectors": ["X", "Z"], "report_sha256": "a" * 64,
        },
    )

    def external_solver(*_args, cardinality_mode, cancel_event, **_kwargs):
        barrier.wait(timeout=2)
        if cardinality_mode == "default":
            outcome, complete, infeasible, distance = "exact", True, True, 2
        elif conflicting_exact and cardinality_mode == "no-card":
            outcome, complete, infeasible, distance = "exact", True, True, 3
        else:
            while not cancel_event.is_set():
                time.sleep(0.001)
            outcome, complete, infeasible, distance = "cancelled", False, False, None
        exited.append(cardinality_mode)
        return {
            "evidence_kind": dist.DISTQLDPC_EVIDENCE_KIND,
            "outcome": outcome, "decision_complete": complete,
            "threshold_infeasible": infeasible, "retryable": not complete,
            "exact_distance": distance, "hard_timeout_s": 1,
        }

    def pysat_solver(_checks, _logicals, **kwargs):
        barrier.wait(timeout=2)
        while not kwargs["cancel_event"].is_set():
            time.sleep(0.001)
        exited.append("pysat")
        evidence = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "outcome": "cancelled", "decision_complete": False,
            "threshold_infeasible": False, "retryable": True,
            "max_weight": kwargs["max_weight"], "operator": None,
            "objective": None, "hard_timeout_s": kwargs["timeout"],
            "zero_anchor_indices": list(kwargs.get("zero_anchor_indices") or ()),
            "one_anchor_index": kwargs.get("one_anchor_index"),
            "anchor_cube_sha256": kwargs.get("anchor_cube_sha256"),
        }
        evidence["evidence_sha256"] = screen._canonical_sha256(evidence)
        return evidence

    monkeypatch.setattr(screen, "solve_css_distance_distqldpc_lower", external_solver)
    monkeypatch.setattr(screen, "solve_css_sector_sat", pysat_solver)
    monkeypatch.setattr(
        screen, "verify_distqldpc_exact_evidence",
        lambda evidence, *_args, **_kwargs: [] if evidence["outcome"] == "exact" else ["nonterminal"],
    )
    monkeypatch.setattr(
        screen, "verify_distqldpc_lower_evidence",
        lambda evidence, *_args, **_kwargs: [] if evidence["outcome"] == "exact" else ["nonterminal"],
    )
    artifact = screen.screen_sat_candidate(
        candidate,
        output=tmp_path / "candidate.json",
        timeout=1,
        workers=6,
        resume=False,
        lower_backend="distqldpc",
    )
    if conflicting_exact:
        assert artifact["status"] == "UNRESOLVED"
        assert artifact["distqldpc_conflict"] is True
    else:
        assert artifact["status"] == "THRESHOLD_PROVEN"
        assert artifact["lower_bound_backend"] == "distqldpc"
    assert len(exited) == 6
    assert set(exited) == set(dist.DISTQLDPC_CARDINALITY_MODES) | {"pysat"}
