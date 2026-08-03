"""Tests for the provisional native-XOR CryptoMiniSat backend."""

from __future__ import annotations

from itertools import product
import os
from pathlib import Path
import stat
import time

import numpy as np
import pytest

import evaluation.distance_cms as distance_cms


def _xor_forbidden_clauses(literals: list[int]) -> list[list[int]]:
    """CNF for XOR(signed literals) == True, for tiny truth-table tests."""

    clauses: list[list[int]] = []
    for values in product((False, True), repeat=len(literals)):
        signed_values = [
            value if literal > 0 else not value
            for literal, value in zip(literals, values, strict=True)
        ]
        if sum(signed_values) % 2 == 1:
            continue
        clauses.append([
            -abs(literal) if value else abs(literal)
            for literal, value in zip(literals, values, strict=True)
        ])
    return clauses


def _solver_for_rendered_xcnf(xcnf: str):
    from pysat.solvers import Solver

    lines = [line.strip() for line in xcnf.splitlines() if line.strip()]
    header = lines.pop(0).split()
    assert header[:2] == ["p", "cnf"]
    num_variables = int(header[2])
    declared_constraints = int(header[3])
    assert declared_constraints == len(lines)
    clauses: list[list[int]] = []
    for line in lines:
        if line.startswith("x"):
            literals = [int(token) for token in line[1:].split()]
            assert literals.pop() == 0
            clauses.extend(_xor_forbidden_clauses(literals))
        else:
            literals = [int(token) for token in line.split()]
            assert literals.pop() == 0
            clauses.append(literals)
    solver = Solver(name="cadical195")
    for clause in clauses:
        solver.add_clause(clause)
    return num_variables, solver


def _has_extension(xcnf: dict, operator: tuple[int, ...]) -> bool:
    _, solver = _solver_for_rendered_xcnf(xcnf["xcnf"])
    try:
        assumptions = [
            index + 1 if value else -(index + 1)
            for index, value in enumerate(operator)
        ]
        return bool(solver.solve(assumptions=assumptions))
    finally:
        solver.delete()


def test_rendered_xcnf_matches_first_nonzero_math_for_every_assignment():
    checks = np.array([[1, 1, 0, 0]], dtype=np.uint8)
    logicals = np.array(
        [[1, 0, 1, 0], [0, 1, 0, 1]], dtype=np.uint8
    )
    cube = distance_cms.cms_anchor_cube_record((0, 3), 1)
    xcnf = distance_cms.build_css_threshold_xcnf(
        checks,
        logicals,
        max_weight=2,
        sector="X",
        partition_index=1,
        anchor_indices=cube["anchor_indices"],
        zero_anchor_indices=cube["zero_anchor_indices"],
        one_anchor_index=cube["one_anchor_index"],
        anchor_cube_sha256=cube["cube_sha256"],
    )
    for operator in product((0, 1), repeat=4):
        vector = np.asarray(operator, dtype=np.uint8)
        syndrome = ((logicals @ vector) & 1).astype(int).tolist()
        expected = bool(
            not np.any((checks @ vector) & 1)
            and syndrome[0] == 0
            and syndrome[1] == 1
            and int(vector.sum()) <= 2
            and vector[0] == 0
            and vector[3] == 1
        )
        assert _has_extension(xcnf, operator) is expected


@pytest.mark.parametrize("partition", (0, 1, 2))
def test_native_logical_partitions_are_disjoint_and_exhaustive(partition):
    checks = np.zeros((0, 3), dtype=np.uint8)
    logicals = np.eye(3, dtype=np.uint8)
    formula = distance_cms.build_css_threshold_xcnf(
        checks,
        logicals,
        max_weight=3,
        sector="Z",
        partition_index=partition,
    )
    for operator in product((0, 1), repeat=3):
        expected = bool(operator[partition] and not any(operator[:partition]))
        assert _has_extension(formula, operator) is expected


def test_kmtotalizer_stays_small_and_xors_never_use_auxiliary_variables():
    checks = np.zeros((2, 360), dtype=np.uint8)
    checks[0, [0, 3, 7, 11, 19, 23]] = 1
    # The empty stabilizer row is a tautology and should be omitted.
    logicals = np.zeros((2, 360), dtype=np.uint8)
    logicals[0, [1, 2, 101]] = 1
    logicals[1, [4, 5, 201]] = 1
    formula = distance_cms.build_css_threshold_xcnf(
        checks,
        logicals,
        max_weight=23,
        sector="X",
        partition_index=1,
    )
    assert formula["cardinality_encoding"] == "kmtotalizer"
    assert formula["num_variables"] == 1727
    assert formula["num_normal_clauses"] == 4386
    assert formula["num_xor_constraints"] == 3
    assert all(
        1 <= variable <= 360
        for xor in formula["xor_constraints"]
        for variable in xor["variables"]
    )
    assert formula["xcnf_sha256"] == distance_cms.hashlib.sha256(
        formula["xcnf"].encode("ascii")
    ).hexdigest()


def test_even_xor_is_rendered_by_flipping_exactly_one_literal():
    formula = distance_cms.build_css_threshold_xcnf(
        np.array([[1, 1, 1]], dtype=np.uint8),
        np.array([[0, 1, 1]], dtype=np.uint8),
        max_weight=3,
        sector="X",
        partition_index=0,
    )
    lines = formula["xcnf"].splitlines()
    assert "x-1 2 3 0" in lines
    assert "x2 3 0" in lines


def test_empty_odd_logical_row_is_an_explicit_contradiction():
    formula = distance_cms.build_css_threshold_xcnf(
        np.zeros((0, 2), dtype=np.uint8),
        np.zeros((1, 2), dtype=np.uint8),
        max_weight=2,
        sector="X",
        partition_index=0,
    )
    assert [] in formula["clauses"]
    for operator in product((0, 1), repeat=2):
        assert not _has_extension(formula, operator)


def test_anchor_cube_binding_fails_closed():
    cube = distance_cms.cms_anchor_cube_record((0, 2), 1)
    with pytest.raises(ValueError, match="anchor_cube_sha256"):
        distance_cms.build_css_threshold_xcnf(
            np.zeros((0, 3), dtype=np.uint8),
            np.eye(1, 3, dtype=np.uint8),
            max_weight=3,
            sector="X",
            partition_index=0,
            anchor_indices=cube["anchor_indices"],
            zero_anchor_indices=cube["zero_anchor_indices"],
            one_anchor_index=cube["one_anchor_index"],
            anchor_cube_sha256="0" * 64,
        )


_FAKE_CMS = """#!/usr/bin/env python3
import os
from pathlib import Path
import subprocess
import sys
import time

COMMIT = "3c8e228e8a48e41276e8ab039f763daa08d61161"
if "--version" in sys.argv:
    print(f"c CMS SHA1: {COMMIT}")
    print("c CryptoMiniSat version 5.14.7")
    print("c CMS compilation env deterministic-test-double")
    raise SystemExit(0)

mode = os.environ.get("QCODE_FAKE_CMS_MODE", "sat")
if mode == "sat":
    print("s SATISFIABLE")
    print("v " + os.environ.get("QCODE_FAKE_CMS_MODEL", "1 -2") + " 0")
    raise SystemExit(10)
if mode == "unsat":
    print("s UNSATISFIABLE")
    raise SystemExit(20)
if mode == "unknown":
    print("s INDETERMINATE")
    raise SystemExit(15)
if mode == "mismatch":
    print("s UNSATISFIABLE")
    raise SystemExit(10)
if mode == "timeout":
    pid_path = Path(os.environ["QCODE_FAKE_CMS_CHILD_PID"])
    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    pid_path.write_text(str(child.pid), encoding="ascii")
    time.sleep(60)
raise SystemExit(2)
"""


def _fake_cms(tmp_path: Path) -> Path:
    path = tmp_path / "cryptominisat5"
    path.write_text(_FAKE_CMS, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def _tiny_problem():
    checks = np.zeros((0, 2), dtype=np.uint8)
    logicals = np.array([[1, 0]], dtype=np.uint8)
    return checks, logicals


def test_binary_identity_binds_version_commit_file_and_hash(tmp_path):
    binary = _fake_cms(tmp_path)
    identity = distance_cms.inspect_cryptominisat_binary(binary)
    assert identity["reported_version"] == distance_cms.CMS_RELEASE_VERSION
    assert identity["reported_commit"] == distance_cms.CMS_RELEASE_COMMIT
    assert identity["file_sha256"] == distance_cms._file_sha256(binary)
    assert identity["identity_sha256"] == distance_cms._canonical_sha256({
        key: value for key, value in identity.items() if key != "identity_sha256"
    })


def test_runner_extracts_and_replays_sat_model(monkeypatch, tmp_path):
    binary = _fake_cms(tmp_path)
    monkeypatch.setenv("QCODE_FAKE_CMS_MODE", "sat")
    monkeypatch.setenv("QCODE_FAKE_CMS_MODEL", "1 -2")
    checks, logicals = _tiny_problem()
    evidence = distance_cms.solve_css_threshold_cms(
        checks,
        logicals,
        max_weight=1,
        sector="X",
        partition_index=0,
        hard_timeout_s=2,
        binary=binary,
        checkpoint_identity={"candidate": "tiny"},
    )
    assert evidence["outcome"] == "sat"
    assert evidence["decision_complete"] is True
    assert evidence["objective"] == 1
    assert evidence["publication_lower_bound_eligible"] is False
    assert distance_cms.verify_cms_sat_witness(evidence, checks, logicals) == []
    binding = evidence["instance"]
    assert binding["backend"]["file_sha256"] == distance_cms._file_sha256(binary)
    assert binding["xcnf_sha256"]
    assert binding["solver_flags"][: len(distance_cms._FIXED_FLAGS)] == list(
        distance_cms._FIXED_FLAGS
    )
    assert binding["proof_status"] == distance_cms.CMS_PROOF_STATUS


def test_unsat_is_terminal_but_explicitly_not_publishable(monkeypatch, tmp_path):
    binary = _fake_cms(tmp_path)
    monkeypatch.setenv("QCODE_FAKE_CMS_MODE", "unsat")
    checks, logicals = _tiny_problem()
    evidence = distance_cms.solve_css_threshold_cms(
        checks,
        logicals,
        max_weight=0,
        sector="X",
        partition_index=0,
        hard_timeout_s=2,
        binary=binary,
    )
    assert evidence["outcome"] == "unsat"
    assert evidence["decision_complete"] is True
    assert evidence["threshold_infeasible"] is True
    assert evidence["retryable"] is False
    assert evidence["publication_lower_bound_eligible"] is False
    assert evidence["proof_status"] == "provisional-no-proof-log"


@pytest.mark.parametrize(
    ("mode", "expected"),
    (("unknown", "unknown"), ("mismatch", "solver_error")),
)
def test_unknown_and_status_mismatch_never_become_unsat(
    monkeypatch, tmp_path, mode, expected
):
    binary = _fake_cms(tmp_path)
    monkeypatch.setenv("QCODE_FAKE_CMS_MODE", mode)
    checks, logicals = _tiny_problem()
    evidence = distance_cms.solve_css_threshold_cms(
        checks,
        logicals,
        max_weight=0,
        sector="X",
        partition_index=0,
        hard_timeout_s=2,
        binary=binary,
    )
    assert evidence["outcome"] == expected
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert evidence["retryable"] is True


def _pid_is_running(pid: int) -> bool:
    try:
        stat_line = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except FileNotFoundError:
        return False
    # Zombies cannot consume resources and are waiting for the host init to
    # reap them; importantly, no solver computation survived.
    return stat_line.split()[2] != "Z"


@pytest.mark.skipif(not Path("/proc").is_dir(), reason="Linux process test")
def test_hard_timeout_kills_private_process_group_without_running_orphan(
    monkeypatch, tmp_path
):
    binary = _fake_cms(tmp_path)
    child_pid_path = tmp_path / "child.pid"
    monkeypatch.setenv("QCODE_FAKE_CMS_MODE", "timeout")
    monkeypatch.setenv("QCODE_FAKE_CMS_CHILD_PID", str(child_pid_path))
    checks, logicals = _tiny_problem()
    evidence = distance_cms.solve_css_threshold_cms(
        checks,
        logicals,
        max_weight=0,
        sector="X",
        partition_index=0,
        hard_timeout_s=0.4,
        termination_grace_s=0.1,
        binary=binary,
    )
    assert evidence["outcome"] == "hard_timeout"
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert evidence["cleanup"]["leader_reaped"] is True
    assert child_pid_path.exists()
    child_pid = int(child_pid_path.read_text(encoding="ascii"))
    deadline = time.monotonic() + 2
    while _pid_is_running(child_pid) and time.monotonic() < deadline:
        time.sleep(0.02)
    assert not _pid_is_running(child_pid)


def test_missing_backend_fails_closed_without_network(tmp_path):
    checks, logicals = _tiny_problem()
    evidence = distance_cms.solve_css_threshold_cms(
        checks,
        logicals,
        max_weight=0,
        sector="X",
        partition_index=0,
        hard_timeout_s=1,
        binary=tmp_path / "missing",
    )
    assert evidence["outcome"] == "backend_unavailable"
    assert evidence["decision_complete"] is False
    assert evidence["threshold_infeasible"] is False
    assert evidence["publication_lower_bound_eligible"] is False
