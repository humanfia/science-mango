"""Focused tests for the optional global CSS threshold SAT backend."""

from __future__ import annotations

from copy import deepcopy
import json
from itertools import product
import os
from pathlib import Path
import threading
import time

import numpy as np
import pytest

import evaluation.distance_sat as distance_sat


def _progress_until_stopped_worker(
    connection,
    _expected_parent_pid,
    *worker_args,
):
    stop_event = worker_args[7]
    sequence = 0
    try:
        while not stop_event.is_set():
            connection.send((
                "progress",
                {
                    "event": "test-progress",
                    "worker_pid": os.getpid(),
                    "sequence": sequence,
                },
            ))
            sequence += 1
            time.sleep(0.01)
    finally:
        connection.close()


def _operator_assignments(cnf: dict, operator: tuple[int, ...]):
    n = int(cnf["n"])
    auxiliary = int(cnf["num_variables"]) - n
    for tail in product((False, True), repeat=auxiliary):
        yield (False, *(bool(value) for value in operator), *tail)


def _clause_set_satisfied(clauses: list[list[int]], assignment: tuple[bool, ...]):
    return all(
        any(
            assignment[abs(literal)] == (literal > 0)
            for literal in clause
        )
        for clause in clauses
    )


def _has_extension(cnf: dict, operator: tuple[int, ...]) -> bool:
    return any(
        _clause_set_satisfied(cnf["clauses"], assignment)
        for assignment in _operator_assignments(cnf, operator)
    )


@pytest.fixture
def parity_only_builder(monkeypatch):
    # Parity and partition Tseitin clauses are native to this module.  Avoid
    # requiring the optional dependency for formulas whose threshold is n.
    monkeypatch.setattr(distance_sat, "_require_pysat", lambda: None)


def test_global_logical_or_cnf_matches_matrix_semantics(parity_only_builder):
    checks = np.array([[1, 1, 0]], dtype=np.uint8)
    logicals = np.array([[1, 0, 0], [0, 0, 1]], dtype=np.uint8)
    cnf = distance_sat.build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=3,
        sector="Z",
    )
    for operator in product((0, 1), repeat=3):
        vector = np.asarray(operator, dtype=np.uint8)
        expected = bool(
            not np.any((checks @ vector) & 1)
            and np.any((logicals @ vector) & 1)
        )
        assert _has_extension(cnf, operator) is expected


@pytest.mark.parametrize("partition", (0, 1))
def test_first_nonzero_partitions_are_exact_and_disjoint(
    parity_only_builder,
    partition,
):
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.array([[1, 0, 0], [0, 1, 0]], dtype=np.uint8)
    cnf = distance_sat.build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=3,
        sector="X",
        partition_index=partition,
    )
    for operator in product((0, 1), repeat=3):
        syndrome = ((logicals @ np.asarray(operator, dtype=np.uint8)) & 1).tolist()
        expected = bool(
            syndrome[partition] == 1 and not any(syndrome[:partition])
        )
        assert _has_extension(cnf, operator) is expected


def test_translation_anchor_clause_and_replay_are_explicit(parity_only_builder):
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.array([[1, 0, 0], [0, 1, 0]], dtype=np.uint8)
    cnf = distance_sat.build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=3,
        sector="Z",
        anchor_indices=(1,),
    )
    assert not _has_extension(cnf, (1, 0, 0))
    assert _has_extension(cnf, (0, 1, 0))

    vector = np.array([0, 1, 0], dtype=np.uint8)
    evidence = {
        "outcome": "sat",
        "operator": distance_sat._pack_vector(vector),
        "objective": 1,
        "max_weight": 1,
        "logical_syndrome": [0, 1],
        "partition_index": 1,
        "anchor_indices": [1],
    }
    assert distance_sat.verify_css_threshold_sat_witness(
        evidence, checks, logicals
    ) == []
    evidence["anchor_indices"] = [2]
    assert "operator violates stored symmetry anchors" in (
        distance_sat.verify_css_threshold_sat_witness(
            evidence, checks, logicals
        )
    )


def test_anchor_first_nonzero_cubes_are_disjoint_exhaustive_and_bound(
    parity_only_builder,
):
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.eye(3, dtype=np.uint8)
    anchors = (0, 2)
    cubes = [distance_sat._anchor_cube_record(anchors, index) for index in range(2)]
    formulas = [
        distance_sat.build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=3,
            sector="X",
            anchor_indices=anchors,
            zero_anchor_indices=cube["zero_anchor_indices"],
            one_anchor_index=cube["one_anchor_index"],
            anchor_cube_sha256=cube["cube_sha256"],
        )
        for cube in cubes
    ]
    for operator in product((0, 1), repeat=3):
        covered = [
            index for index, cnf in enumerate(formulas)
            if _has_extension(cnf, operator)
        ]
        assert len(covered) == int(bool(operator[0] or operator[2]))
    assert formulas[1]["anchor_unit_clauses"] == [[-1], [3]]
    assert formulas[1]["anchor_unit_clauses_sha256"] == (
        distance_sat._canonical_sha256([[-1], [3]])
    )


def test_anchor_cube_validation_fails_closed_on_prefix_or_hash_tampering(
    parity_only_builder,
):
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.eye(3, dtype=np.uint8)
    cube = distance_sat._anchor_cube_record((0, 2), 1)
    with pytest.raises(ValueError, match="ordered anchor prefix"):
        distance_sat.build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=3,
            sector="X",
            anchor_indices=(0, 2),
            zero_anchor_indices=(),
            one_anchor_index=2,
            anchor_cube_sha256=cube["cube_sha256"],
        )
    with pytest.raises(ValueError, match="hash does not match"):
        distance_sat.build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=3,
            sector="X",
            anchor_indices=(0, 2),
            zero_anchor_indices=(0,),
            one_anchor_index=2,
            anchor_cube_sha256="0" * 64,
        )


def test_cube_instance_binding_is_strict_but_legacy_upper_stays_cube_free():
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.eye(3, dtype=np.uint8)
    common = {
        "max_weight": 1,
        "sector": "X",
        "encoding": "seqcounter",
        "solver_name": "cadical195",
        "checkpoint_identity": {"phase": "upper"},
        "partition_index": None,
        "anchor_indices": (0, 2),
    }
    upper = distance_sat._instance_binding(checks, logicals, **common)
    assert "anchor_cube_sha256" not in upper
    assert "anchor_unit_clauses" not in upper

    cube = distance_sat._anchor_cube_record((0, 2), 1)
    lower = distance_sat._instance_binding(
        checks,
        logicals,
        **{
            **common,
            "checkpoint_identity": {
                "phase": "lower",
                "anchor_cube_sha256": cube["cube_sha256"],
            },
        },
        zero_anchor_indices=(0,),
        one_anchor_index=2,
        anchor_cube_sha256=cube["cube_sha256"],
    )
    assert lower["anchor_unit_clauses"] == [[-1], [3]]
    assert lower["anchor_unit_clauses_sha256"] == (
        distance_sat._canonical_sha256([[-1], [3]])
    )
    assert not distance_sat._checkpoint_binding_matches(upper, lower)


def test_sat_witness_replay_enforces_each_anchor_cube_literal():
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.eye(3, dtype=np.uint8)
    cube = distance_sat._anchor_cube_record((0, 2), 1)
    evidence = {
        "outcome": "sat",
        "operator": distance_sat._pack_vector(
            np.array([0, 0, 1], dtype=np.uint8),
        ),
        "objective": 1,
        "max_weight": 1,
        "logical_syndrome": [0, 0, 1],
        "partition_index": None,
        "anchor_indices": [0, 2],
        "zero_anchor_indices": [0],
        "one_anchor_index": 2,
        "anchor_cube_sha256": cube["cube_sha256"],
    }
    assert distance_sat.verify_css_threshold_sat_witness(
        evidence, checks, logicals,
    ) == []
    evidence["operator"] = distance_sat._pack_vector(
        np.array([1, 0, 1], dtype=np.uint8),
    )
    evidence["objective"] = 2
    assert "operator violates zero-anchor cube literals" in (
        distance_sat.verify_css_threshold_sat_witness(
            evidence, checks, logicals,
        )
    )


def test_sector_matrix_mapping_is_not_reversed():
    hx = np.array([[1, 0]], dtype=np.uint8)
    hz = np.array([[0, 1]], dtype=np.uint8)
    lx = np.array([[1, 1]], dtype=np.uint8)
    lz = np.array([[1, 0]], dtype=np.uint8)
    z_checks, z_targets = distance_sat.css_sector_matrices(hx, hz, lx, lz, "Z")
    x_checks, x_targets = distance_sat.css_sector_matrices(hx, hz, lx, lz, "X")
    assert np.array_equal(z_checks, hx)
    assert np.array_equal(z_targets, lx)
    assert np.array_equal(x_checks, hz)
    assert np.array_equal(x_targets, lz)


def test_sat_worker_budget_clamps_native_numeric_threads(monkeypatch):
    for variable in distance_sat.SAT_NATIVE_THREAD_ENV:
        monkeypatch.setenv(variable, "127")
    observed = distance_sat.enforce_sat_native_thread_budget()
    assert observed == {
        variable: "1" for variable in distance_sat.SAT_NATIVE_THREAD_ENV
    }


def test_native_minicard_constraint_is_explicit_in_cnf_identity(
    parity_only_builder,
):
    cnf = distance_sat.build_css_threshold_cnf(
        np.zeros((0, 3), dtype=np.uint8),
        np.eye(3, dtype=np.uint8),
        max_weight=1,
        sector="X",
        cardinality_encoding="native-minicard",
    )
    assert cnf["native_atmost"] == {"literals": [1, 2, 3], "bound": 1}
    assert cnf["cardinality_encoding"] == "native-minicard"
    assert cnf["cnf_sha256"] == distance_sat._canonical_sha256({
        "num_variables": cnf["num_variables"],
        "clauses": cnf["clauses"],
        "native_atmost": cnf["native_atmost"],
    })


def test_prelaunch_cancellation_is_retryable_and_self_hashed(tmp_path):
    cancellation = threading.Event()
    cancellation.set()
    evidence = distance_sat.solve_css_threshold_sat(
        np.zeros((0, 2), dtype=np.uint8),
        np.eye(2, dtype=np.uint8),
        max_weight=1,
        sector="X",
        hard_timeout_s=20,
        cancel_event=cancellation,
        checkpoint_path=tmp_path / "must-not-exist.json",
    )
    assert evidence["outcome"] == "cancelled"
    assert evidence["retryable"] is True
    assert evidence["decision_complete"] is False
    assert not (tmp_path / "must-not-exist.json").exists()
    unsigned = dict(evidence)
    evidence_hash = unsigned.pop("evidence_sha256")
    assert evidence_hash == distance_sat._canonical_sha256(unsigned)


def _migrated_test_bindings():
    current = {
        "formulation_revision": "same-formula",
        "source_sha256": distance_sat._SOURCE_SHA256,
        "check_matrix_sha256": "a" * 64,
        "checkpoint_identity": {
            "candidate_digest": "candidate",
            "xz_sector_isometry_sha256": "b" * 64,
        },
        "native_thread_environment": {
            variable: "1" for variable in distance_sat.SAT_NATIVE_THREAD_ENV
        },
        "solver_execution": {
            "policy": distance_sat.SAT_INCREMENTAL_POLICY,
            "incremental_conflict_budget": 25000,
        },
    }
    current["binding_sha256"] = distance_sat._canonical_sha256(current)
    old = deepcopy(current)
    old["source_sha256"] = (
        "9715c55e55b41aa08023c356863ccf06aee5c2170f6cba77986c66cfdad33f80"
    )
    old["checkpoint_identity"].pop("xz_sector_isometry_sha256")
    old["native_thread_environment"].pop("NUMBA_NUM_THREADS")
    old.pop("solver_execution")
    old.pop("binding_sha256")
    old["binding_sha256"] = distance_sat._canonical_sha256(old)
    return old, current


def test_allowlisted_runtime_upgrade_preserves_exact_checkpoint_binding():
    old, current = _migrated_test_bindings()

    assert distance_sat._checkpoint_binding_matches(old, current)
    tampered = deepcopy(old)
    tampered["check_matrix_sha256"] = "c" * 64
    tampered.pop("binding_sha256")
    tampered["binding_sha256"] = distance_sat._canonical_sha256(tampered)
    assert not distance_sat._checkpoint_binding_matches(tampered, current)


def test_source_migration_replays_sat_witness_but_never_bare_unsat(tmp_path):
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.eye(2, dtype=np.uint8)
    old, current = _migrated_test_bindings()
    common = {
        "schema_version": distance_sat.SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": distance_sat.SAT_EVIDENCE_KIND,
        "instance": old,
        "max_weight": 1,
        "partition_index": None,
        "anchor_indices": [],
    }
    sat = {
        **common,
        "outcome": "sat",
        "operator": distance_sat._pack_vector(
            np.array([1, 0], dtype=np.uint8),
        ),
        "objective": 1,
        "logical_syndrome": [1, 0],
    }
    sat["evidence_sha256"] = distance_sat._canonical_sha256(sat)
    sat_path = tmp_path / "sat.json"
    distance_sat._atomic_write_json(sat_path, sat)
    assert distance_sat._load_terminal_checkpoint(
        sat_path,
        binding=current,
        checks=checks,
        logicals=logicals,
    )["resumed"] is True

    unsat = {
        **common,
        "outcome": "unsat",
        "operator": None,
        "objective": None,
    }
    unsat["evidence_sha256"] = distance_sat._canonical_sha256(unsat)
    unsat_path = tmp_path / "unsat.json"
    distance_sat._atomic_write_json(unsat_path, unsat)
    assert distance_sat._load_terminal_checkpoint(
        unsat_path,
        binding=current,
        checks=checks,
        logicals=logicals,
    ) is None


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_allowlisted_kissat_sat_replays_before_incremental_capability_check(
    tmp_path,
):
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.eye(2, dtype=np.uint8)
    checkpoint = tmp_path / "kissat-sat.json"
    original = distance_sat.solve_css_threshold_sat(
        checks,
        logicals,
        max_weight=1,
        sector="X",
        hard_timeout_s=20,
        solver="kissat404",
        partition_index=0,
        checkpoint_path=checkpoint,
    )
    assert original["outcome"] == "sat"

    stored = json.loads(checkpoint.read_text(encoding="utf-8"))
    instance = dict(stored["instance"])
    instance["source_sha256"] = (
        "9715c55e55b41aa08023c356863ccf06aee5c2170f6cba77986c66cfdad33f80"
    )
    instance.pop("solver_execution")
    instance.pop("binding_sha256")
    instance["binding_sha256"] = distance_sat._canonical_sha256(instance)
    stored["instance"] = instance
    stored.pop("evidence_sha256")
    stored["evidence_sha256"] = distance_sat._canonical_sha256(stored)
    distance_sat._atomic_write_json(checkpoint, stored)

    replayed = distance_sat.solve_css_threshold_sat(
        checks,
        logicals,
        max_weight=1,
        sector="X",
        hard_timeout_s=20,
        solver="kissat404",
        incremental_conflict_budget=1,
        partition_index=0,
        checkpoint_path=checkpoint,
        resume=True,
    )
    assert replayed["outcome"] == "sat"
    assert replayed["resumed"] is True


def _composition_evidence(
    checks,
    logicals,
    *,
    outcome,
    max_weight,
    partition_index,
    operator=None,
    objective=None,
    logical_syndrome=None,
):
    backend = {
        "distribution": "python-sat",
        "version": "test",
        "solver": "test-solver",
    }
    instance = {
        "formulation": distance_sat.SAT_FORMULATION,
        "sector": "Z",
        "max_weight": max_weight,
        "backend": dict(backend),
        "partition_index": partition_index,
        "anchor_indices": [],
        "check_matrix_sha256": distance_sat._array_sha256("checks", checks),
        "target_logicals_sha256": distance_sat._array_sha256(
            "logicals", logicals,
        ),
    }
    instance["binding_sha256"] = distance_sat._canonical_sha256(instance)
    evidence = {
        "schema_version": distance_sat.SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": distance_sat.SAT_EVIDENCE_KIND,
        "formulation": distance_sat.SAT_FORMULATION,
        "instance": instance,
        "sector": "Z",
        "max_weight": max_weight,
        "backend": backend,
        "partition_index": partition_index,
        "anchor_indices": [],
        "outcome": outcome,
        "decision_complete": True,
        "threshold_infeasible": outcome == "unsat",
        "success": outcome == "sat",
        "operator": operator,
        "objective": objective,
        "logical_syndrome": logical_syndrome,
    }
    evidence["evidence_sha256"] = distance_sat._canonical_sha256(evidence)
    return evidence


def test_exact_composition_requires_all_lower_partitions_and_upper_witness():
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.array([[1, 0, 0], [0, 1, 0]], dtype=np.uint8)
    lowers = [
        _composition_evidence(
            checks,
            logicals,
            outcome="unsat",
            max_weight=0,
            partition_index=partition,
        )
        for partition in range(2)
    ]
    upper = _composition_evidence(
        checks,
        logicals,
        outcome="sat",
        max_weight=1,
        partition_index=None,
        operator=distance_sat._pack_vector(
            np.array([0, 1, 0], dtype=np.uint8),
        ),
        objective=1,
        logical_syndrome=[0, 1],
    )
    composed = distance_sat.compose_css_sector_exact_evidence(
        lowers,
        upper,
        checks,
        logicals,
        distance=1,
        sector="Z",
    )
    assert composed["exact"] is True
    assert composed["completed_partitions"] == 2

    incomplete = distance_sat.compose_css_sector_exact_evidence(
        lowers[:1],
        upper,
        checks,
        logicals,
        distance=1,
        sector="Z",
    )
    assert incomplete["exact"] is False
    assert any("do not cover" in failure for failure in incomplete["failures"])


def test_exact_composition_rejects_unbound_or_anchored_evidence():
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.eye(2, dtype=np.uint8)
    lowers = [
        _composition_evidence(
            checks,
            logicals,
            outcome="unsat",
            max_weight=0,
            partition_index=partition,
        )
        for partition in range(2)
    ]
    upper = _composition_evidence(
        checks,
        logicals,
        outcome="sat",
        max_weight=1,
        partition_index=None,
        operator=distance_sat._pack_vector(np.array([1, 0], dtype=np.uint8)),
        objective=1,
        logical_syndrome=[1, 0],
    )

    invalid_hash = deepcopy(lowers)
    invalid_hash[0]["evidence_sha256"] = "0" * 64
    result = distance_sat.compose_css_sector_exact_evidence(
        invalid_hash, upper, checks, logicals, distance=1, sector="Z",
    )
    assert result["exact"] is False
    assert any("invalid evidence hash" in item for item in result["failures"])

    invalid_backend = deepcopy(lowers)
    invalid_backend[0]["backend"]["distribution"] = "untrusted-sat"
    invalid_backend[0]["evidence_sha256"] = distance_sat._canonical_sha256(
        {key: value for key, value in invalid_backend[0].items()
         if key != "evidence_sha256"},
    )
    result = distance_sat.compose_css_sector_exact_evidence(
        invalid_backend, upper, checks, logicals, distance=1, sector="Z",
    )
    assert result["exact"] is False
    assert any("backend identity" in item for item in result["failures"])

    invalid_sector = deepcopy(lowers)
    invalid_sector[0]["sector"] = "X"
    invalid_sector[0]["evidence_sha256"] = distance_sat._canonical_sha256(
        {key: value for key, value in invalid_sector[0].items()
         if key != "evidence_sha256"},
    )
    result = distance_sat.compose_css_sector_exact_evidence(
        invalid_sector, upper, checks, logicals, distance=1, sector="Z",
    )
    assert result["exact"] is False
    assert any("claimed SAT instance" in item for item in result["failures"])

    anchored = deepcopy(lowers)
    anchored[0]["anchor_indices"] = [0]
    anchored[0]["instance"]["anchor_indices"] = [0]
    binding = dict(anchored[0]["instance"])
    binding.pop("binding_sha256")
    anchored[0]["instance"]["binding_sha256"] = (
        distance_sat._canonical_sha256(binding)
    )
    unsigned = dict(anchored[0])
    unsigned.pop("evidence_sha256")
    anchored[0]["evidence_sha256"] = distance_sat._canonical_sha256(unsigned)
    result = distance_sat.compose_css_sector_exact_evidence(
        anchored, upper, checks, logicals, distance=1, sector="Z",
    )
    assert result["exact"] is False
    assert any("code-aware typed" in item for item in result["failures"])


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_incremental_inprocess_reuses_solver_and_unknown_is_only_progress(
    monkeypatch,
):
    import pysat.solvers

    class FakeSolver:
        instances = []

        def __init__(self, **_kwargs):
            self.budgets = []
            self.calls = 0
            self.__class__.instances.append(self)

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return False

        def supports_atmost(self):
            return False

        def conf_budget(self, budget):
            self.budgets.append(budget)

        def solve_limited(self):
            self.calls += 1
            return (None, None, False)[self.calls - 1]

        def accum_stats(self):
            return {"conflicts": self.calls * 7, "decisions": self.calls}

        def get_model(self):
            return None

        def time(self):
            return 0.01 * self.calls

    monkeypatch.setattr(pysat.solvers, "Solver", FakeSolver)
    progress = []
    evidence = distance_sat._solve_inprocess(
        np.zeros((0, 2), dtype=np.uint8),
        np.eye(2, dtype=np.uint8),
        max_weight=0,
        sector="X",
        encoding="seqcounter",
        solver_name="cadical195",
        partition_index=0,
        anchor_indices=(),
        zero_anchor_indices=(),
        one_anchor_index=None,
        anchor_cube_sha256=None,
        incremental_conflict_budget=7,
        progress_callback=progress.append,
    )

    assert len(FakeSolver.instances) == 1
    assert FakeSolver.instances[0].budgets == [7, 7, 7]
    assert evidence["outcome"] == "unsat"
    assert evidence["decision_complete"] is True
    assert evidence["incremental_solver"] == {
        "policy": distance_sat.SAT_INCREMENTAL_POLICY,
        "conflict_budget_per_slice": 7,
        "solve_calls": 3,
        "unknown_slices": 2,
        "solver_object_reused": True,
        "solver_stats": {"conflicts": 21, "decisions": 3},
    }
    assert [item["event"] for item in progress] == [
        "solver_ready",
        "conflict_slice_complete",
        "conflict_slice_complete",
    ]


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_incremental_kissat_is_rejected_before_native_second_solve():
    evidence = distance_sat.solve_css_threshold_sat(
        np.zeros((0, 2), dtype=np.uint8),
        np.eye(2, dtype=np.uint8),
        max_weight=0,
        sector="X",
        hard_timeout_s=20,
        solver="kissat404",
        incremental_conflict_budget=1,
        partition_index=0,
    )
    assert evidence["outcome"] == "backend_unavailable"
    assert evidence["decision_complete"] is False
    assert evidence["retryable"] is True
    assert "does not support safe repeated limited solves" in evidence["message"]


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_incremental_child_persists_progress_but_only_terminal_checkpoint(
    tmp_path,
):
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.eye(2, dtype=np.uint8)
    terminal_path = tmp_path / "terminal.json"
    progress_path = tmp_path / "progress.json"
    evidence = distance_sat.solve_css_threshold_sat(
        checks,
        logicals,
        max_weight=0,
        sector="X",
        hard_timeout_s=20,
        solver="cadical195",
        incremental_conflict_budget=1,
        partition_index=0,
        checkpoint_path=terminal_path,
        progress_path=progress_path,
    )

    assert evidence["outcome"] == "unsat"
    assert evidence["decision_complete"] is True
    assert evidence["incremental_solver"]["policy"] == (
        distance_sat.SAT_INCREMENTAL_POLICY
    )
    assert evidence["incremental_solver"]["solve_calls"] >= 1
    assert terminal_path.exists()
    progress = json.loads(progress_path.read_text())
    assert progress["evidence_kind"] == distance_sat.SAT_PROGRESS_KIND
    assert progress["outcome"] == "running"
    assert progress["decision_complete"] is False
    unsigned = dict(progress)
    expected_hash = unsigned.pop("progress_sha256")
    assert expected_hash == distance_sat._canonical_sha256(unsigned)
    assert distance_sat._load_terminal_checkpoint(
        progress_path,
        binding=evidence["instance"],
        checks=checks,
        logicals=logicals,
    ) is None


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_progress_path_must_not_alias_terminal_checkpoint(tmp_path):
    shared_path = tmp_path / "shared.json"
    with pytest.raises(ValueError, match="progress_path must differ"):
        distance_sat.solve_css_threshold_sat(
            np.zeros((0, 2), dtype=np.uint8),
            np.eye(2, dtype=np.uint8),
            max_weight=0,
            sector="X",
            hard_timeout_s=20,
            solver="cadical195",
            incremental_conflict_budget=1,
            checkpoint_path=shared_path,
            progress_path=shared_path,
        )


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
def test_incremental_hard_wall_keeps_progress_nonterminal_and_reaps_child(
    monkeypatch,
    tmp_path,
):
    monkeypatch.setattr(
        distance_sat,
        "_solver_worker",
        _progress_until_stopped_worker,
    )
    terminal_path = tmp_path / "terminal.json"
    progress_path = tmp_path / "progress.json"
    writes = []
    atomic_write = distance_sat._atomic_write_json

    def tracked_write(path, value):
        writes.append(Path(path))
        atomic_write(path, value)

    monkeypatch.setattr(distance_sat, "_atomic_write_json", tracked_write)
    evidence = distance_sat.solve_css_threshold_sat(
        np.zeros((0, 2), dtype=np.uint8),
        np.eye(2, dtype=np.uint8),
        max_weight=0,
        sector="X",
        hard_timeout_s=1.0,
        termination_grace_s=1.0,
        solver="cadical195",
        incremental_conflict_budget=1,
        checkpoint_path=terminal_path,
        progress_path=progress_path,
    )

    assert evidence["outcome"] == "hard_timeout"
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert evidence["incremental_progress"]["sequence"] >= 2
    assert not terminal_path.exists()
    assert progress_path.exists()
    assert 1 <= writes.count(progress_path) <= 2
    worker_pid = int(evidence["incremental_progress"]["worker_pid"])
    assert not Path(f"/proc/{worker_pid}").exists()


@pytest.mark.parametrize("budget", (0, -1, True, 1.5))
def test_incremental_conflict_budget_must_be_positive_integer(budget):
    with pytest.raises(ValueError, match="incremental_conflict_budget"):
        distance_sat.solve_css_threshold_sat(
            np.zeros((0, 2), dtype=np.uint8),
            np.eye(2, dtype=np.uint8),
            max_weight=0,
            sector="X",
            hard_timeout_s=20,
            incremental_conflict_budget=budget,
        )


def test_missing_optional_backend_is_explicit_and_retryable():
    if distance_sat.pysat_available():
        pytest.skip("python-sat is installed in this environment")
    evidence = distance_sat.solve_css_sector_sat(
        np.zeros((0, 2), dtype=np.uint8),
        np.eye(2, dtype=np.uint8),
        max_weight=0,
        timeout=1,
    )
    assert evidence["outcome"] == "backend_unavailable"
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert evidence["retryable"] is True
    assert evidence["status_name"] == "BACKEND_UNAVAILABLE"


@pytest.mark.skipif(
    not distance_sat.pysat_available(),
    reason="optional python-sat backend is not installed",
)
@pytest.mark.parametrize(
    "encoding",
    ("seqcounter", "kmtotalizer", "native-minicard", "totalizer"),
)
def test_optional_backend_solves_tiny_sat_and_unsat(encoding, tmp_path):
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.eye(2, dtype=np.uint8)
    unsat = distance_sat.solve_css_sector_sat(
        checks,
        logicals,
        max_weight=0,
        timeout=20,
        cardinality_encoding=encoding,
        partition_index=0,
        checkpoint_path=tmp_path / f"{encoding}-unsat.json",
    )
    assert unsat["outcome"] == "unsat"
    assert unsat["threshold_infeasible"] is True
    resumed = distance_sat.solve_css_sector_sat(
        checks,
        logicals,
        max_weight=0,
        timeout=20,
        cardinality_encoding=encoding,
        partition_index=0,
        checkpoint_path=tmp_path / f"{encoding}-unsat.json",
        resume=True,
    )
    assert resumed["outcome"] == "unsat"
    assert resumed["resumed"] is True
    unsigned = dict(resumed)
    expected_hash = unsigned.pop("evidence_sha256")
    assert expected_hash == distance_sat._canonical_sha256(unsigned)
    sat = distance_sat.solve_css_sector_sat(
        checks,
        logicals,
        max_weight=1,
        timeout=20,
        cardinality_encoding=encoding,
        partition_index=1,
    )
    assert sat["outcome"] == "sat"
    assert distance_sat.verify_css_threshold_sat_witness(
        sat, checks, logicals
    ) == []
