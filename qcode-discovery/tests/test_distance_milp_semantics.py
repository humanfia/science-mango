from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import multiprocessing
import os
import signal
import sys
import threading
import time
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest
from scipy.sparse import issparse

from evaluation import distance_milp, evaluator


class DummyCssCode:
    num_qudits = 4
    dimension = 1


class DummySymplecticCode:
    num_qudits = 4
    dimension = 1
    matrix = np.zeros((1, 8), dtype=int)


def test_css_timeout_without_incumbent_has_no_lower_bound(monkeypatch):
    hx = np.zeros((1, 4), dtype=int)
    hz = np.zeros((1, 4), dtype=int)
    lx = np.array([[1, 0, 0, 0]], dtype=int)
    lz = np.array([[0, 1, 0, 0]], dtype=int)
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: (hx, hz, lx, lz)
    )
    monkeypatch.setattr(
        distance_milp, "ilp_min_weight", lambda *_args, **_kwargs: (None, False)
    )

    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(), early_stop=4, timeout_per_logical=1, total_timeout=10
    )

    assert distance == DummyCssCode.num_qudits
    assert details["all_timeout"] is True
    assert details["no_incumbent"] is True
    assert details["distance_status"] == "unknown"
    assert details["d_is_lower_bound"] is False


def test_symplectic_timeout_and_early_exit_are_never_exact(monkeypatch):
    from evaluation import pbb_code

    logicals = np.zeros((2, 8), dtype=int)
    monkeypatch.setattr(pbb_code, "get_symplectic_logicals", lambda _code: logicals)
    monkeypatch.setattr(
        distance_milp,
        "ilp_min_weight_symplectic",
        lambda *_args, **_kwargs: (None, False),
    )
    distance, details = distance_milp.compute_distance_milp_symplectic(
        DummySymplecticCode(), early_stop=4,
        timeout_per_logical=1, total_timeout=10,
    )
    assert distance == DummySymplecticCode.num_qudits
    assert details["distance_status"] == "unknown"
    assert details["d_is_lower_bound"] is False

    calls = iter([(2, True), (3, True)])
    monkeypatch.setattr(
        distance_milp,
        "ilp_min_weight_symplectic",
        lambda *_args, **_kwargs: next(calls),
    )
    distance, details = distance_milp.compute_distance_milp_symplectic(
        DummySymplecticCode(), early_stop=2,
        timeout_per_logical=1, total_timeout=10,
    )
    assert distance == 2
    assert details["num_logicals_checked"] == 1
    assert details["exact"] is False


def test_evaluator_accepts_none_and_timeout_is_fail_closed(monkeypatch):
    dummy = DummyCssCode()
    monkeypatch.setattr(
        evaluator, "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, dummy.num_qudits, dummy.dimension),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (3, 3, 3)
    )
    monkeypatch.setattr(
        evaluator, "compute_distance_milp",
        lambda *_args, **_kwargs: (
            dummy.num_qudits,
            {"exact": False, "all_timeout": True, "total_logicals": 2},
        ),
    )

    result = evaluator.evaluate_candidate_milp(
        2, 1, [(0, 0), (1, 0)], [(0, 0), (1, 0)],
        milp_early_stop=None,
    )
    assert result["d"] == 0
    assert result["score"] == 0.0
    assert result["stage"] == "milp_timeout_no_incumbent"
    assert "d_lower_bound" not in result


def test_none_with_incumbent_remains_an_upper_bound(monkeypatch):
    dummy = DummyCssCode()
    monkeypatch.setattr(
        evaluator, "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, dummy.num_qudits, dummy.dimension),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (3, 3, 3)
    )
    monkeypatch.setattr(
        evaluator, "compute_distance_milp",
        lambda *_args, **_kwargs: (
            3,
            {"exact": False, "total_logicals": 2, "num_logicals_checked": 1},
        ),
    )
    result = evaluator.evaluate_candidate_milp(
        2, 1, [(0, 0), (1, 0)], [(0, 0), (1, 0)],
        milp_early_stop=None,
    )
    assert result["d"] == 3
    assert result["d_is_exact"] is False
    assert result["stage"] == "milp_incumbent"


def test_dynamic_fom_cutoff_uses_exact_integer_boundaries():
    assert evaluator.compute_fom_rejection_cutoff(360, 16, 12.0) == 16
    assert evaluator.compute_fom_rejection_cutoff(288, 12, 12.0) == 16
    assert evaluator.compute_fom_rejection_cutoff(144, 12, 12.0) == 12


def test_challenge_cutoff_preserves_equal_fom_pareto_winner():
    assert evaluator.compute_fom_rejection_cutoff(36, 12, 12.0) == 6
    assert evaluator.compute_challenge_rejection_cutoff(36, 12, 12.0) == 5


def test_dynamic_cutoff_handles_parameter_sets_with_no_possible_winner():
    assert evaluator.compute_challenge_rejection_cutoff(4, 1, 12.0) == 4


def test_css_incumbent_at_cutoff_stops_after_first_direction(monkeypatch):
    hx = np.zeros((1, 4), dtype=int)
    hz = np.zeros((1, 4), dtype=int)
    lx = np.array([[1, 0, 0, 0]], dtype=int)
    lz = np.array([[0, 1, 0, 0]], dtype=int)
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: (hx, hz, lx, lz)
    )
    calls = []

    def incumbent(*_args, **_kwargs):
        calls.append(1)
        return 3, False, [1, 1, 1, 0]

    monkeypatch.setattr(distance_milp, "ilp_min_weight", incumbent)
    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(), early_stop=3, timeout_per_logical=1, total_timeout=10
    )

    assert distance == 3
    assert len(calls) == 1
    assert details["num_logicals_checked"] == 1
    assert details["logicals_incumbent"] == 1
    assert details["d_x_computed"] is False
    assert details["exact"] is False
    assert details["minimum_direction_witness"] == {
        "side": "Z",
        "index": 0,
        "weight": 3,
        "bits": [1, 1, 1, 0],
    }


def test_dynamic_cutoff_uses_rebuilt_n_k_and_stops_at_boundary(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    observed = {}
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (58, 58, 58)
    )

    def fake_distance(*_args, **kwargs):
        observed.update(kwargs)
        return 16, {
            "exact": False,
            "all_timeout": False,
            "total_logicals": 32,
            "num_logicals_checked": 1,
            "logicals_optimal": 0,
            "logicals_incumbent": 1,
            "d_x": 0,
            "d_z": 16,
            "minimum_direction_witness": {
                "side": "Z",
                "index": 0,
                "weight": 16,
                "bits": [1] * 16 + [0] * 344,
            },
        }

    monkeypatch.setattr(evaluator, "compute_distance_milp", fake_distance)
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_early_stop=4,
        milp_target_fom=12.0,
    )

    assert observed["early_stop"] == 16
    assert result["milp_effective_early_stop"] == 16
    assert result["d"] == 16
    assert result["d_is_exact"] is False
    assert result["stage"] == "milp_low_d"
    assert result["fom_target_excluded_by_upper_bound"] is True
    assert result["final_gate_excluded_by_upper_bound"] is True
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_lhs"] <= result["threshold_proof_rhs"]
    assert result["threshold_proof_distance"] == 16
    assert result["threshold_proof_source"] == "milp_feasible_upper_bound"


def test_dynamic_cutoff_does_not_reject_above_boundary(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (58, 58, 58)
    )
    monkeypatch.setattr(
        evaluator,
        "compute_distance_milp",
        lambda *_args, **_kwargs: (
            17,
            {
                "exact": False,
                "all_timeout": False,
                "total_logicals": 32,
                "num_logicals_checked": 1,
            },
        ),
    )

    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )

    assert result["d"] == 17
    assert result["stage"] == "milp_incumbent"
    assert result["fom_target_excluded_by_upper_bound"] is False
    assert result["final_gate_excluded_by_upper_bound"] is False
    assert result["threshold_rejection_proven"] is False


def test_exact_milp_threshold_rejection_keeps_direction_witness(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    witness = {
        "side": "Z",
        "index": 0,
        "weight": 16,
        "bits": [1] * 16 + [0] * 344,
    }
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (58, 58, 58)
    )
    monkeypatch.setattr(
        evaluator,
        "compute_distance_milp",
        lambda *_args, **_kwargs: (
            16,
            {
                "exact": True,
                "all_timeout": False,
                "total_logicals": 32,
                "num_logicals_checked": 32,
                "logicals_optimal": 32,
                "logicals_incumbent": 0,
                "d_x": 20,
                "d_z": 16,
                "minimum_direction_witness": witness,
            },
        ),
    )
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_source"] == "milp_exact"
    assert result["threshold_proof_witness"] == witness


def test_dynamic_cutoff_can_skip_milp_from_symplectic_upper_bound(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 16)
    )
    witness = {
        "side": "X",
        "index": 0,
        "dual_side": "Z",
        "dual_index": 0,
        "weight": 16,
        "bits": [1] * 16 + [0] * 344,
    }
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_witness",
        lambda _code, _distance: witness,
    )

    def unexpected_milp(*_args, **_kwargs):
        raise AssertionError("MILP must not run once the upper bound excludes a win")

    monkeypatch.setattr(evaluator, "compute_distance_milp", unexpected_milp)
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )

    assert result["stage"] == "symplectic_low_d"
    assert result["d"] == 16
    assert result["d_is_exact"] is False
    assert result["milp_solver_attempted"] is False
    assert result["final_gate_excluded_by_upper_bound"] is True
    assert result["threshold_proof_distance"] == 16
    assert result["threshold_proof_source"] == "symplectic_upper_bound"
    assert result["threshold_proof_witness"] == witness


def test_symplectic_prefilter_requires_real_anticommuting_dual(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 16)
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_witness", lambda *_args: None
    )
    called = []

    def fallback(*_args, **_kwargs):
        called.append(True)
        return 0, {"exact": False, "all_timeout": True, "total_logicals": 32}

    monkeypatch.setattr(evaluator, "compute_distance_milp", fallback)
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )
    assert called == [True]
    assert result["stage"] == "milp_timeout_no_incumbent"


def test_symplectic_weight_witness_binds_actual_dual_and_minimum(monkeypatch):
    from qldpc.objects import Pauli

    class Code:
        num_qudits = 4
        dimension = 1
        matrix_x = np.zeros((1, 4), dtype=int)
        matrix_z = np.zeros((1, 4), dtype=int)

        def get_logical_ops(self, pauli):
            if pauli == Pauli.X:
                return np.array([[1, 1, 0, 0]], dtype=int)
            return np.array([[1, 0, 0, 0]], dtype=int)

    witness = distance_milp.symplectic_weight_witness(Code(), 1)
    assert witness == {
        "side": "Z",
        "index": 0,
        "dual_side": "X",
        "dual_index": 0,
        "weight": 1,
        "bits": [1, 0, 0, 0],
    }

    monkeypatch.setattr(
        Code,
        "get_logical_ops",
        lambda self, pauli: np.array([[0, 1, 0, 0]], dtype=int)
        if pauli == Pauli.X
        else np.array([[1, 0, 0, 0]], dtype=int),
    )
    assert distance_milp.symplectic_weight_witness(Code(), 1) is None


@pytest.mark.parametrize(
    "original_bytes",
    [
        b'{"kind":"truncated-symplectic"',
        b'{"kind":"first","kind":"duplicate"}',
    ],
    ids=["truncated", "duplicate-key"],
)
def test_symplectic_checkpoint_reset_archives_bad_json_and_recomputes(
    tmp_path, original_bytes,
):
    from qldpc.objects import Pauli

    class Code:
        num_qudits = 4
        dimension = 1
        matrix_x = np.zeros((1, 4), dtype=int)
        matrix_z = np.zeros((1, 4), dtype=int)

        def get_logical_ops(self, pauli):
            if pauli == Pauli.X:
                return np.array([[1, 1, 0, 0]], dtype=int)
            return np.array([[1, 0, 0, 0]], dtype=int)

    code = Code()
    witness = distance_milp.symplectic_weight_witness(code, 1)
    checkpoint = tmp_path / "symplectic.json"
    checkpoint.write_bytes(original_bytes)
    original_sha256 = hashlib.sha256(original_bytes).hexdigest()
    arguments = {
        "checkpoint_path": checkpoint,
        "checkpoint_identity": {"candidate": "self-dual"},
        "witness": witness,
        "timeout_per_logical": 1,
        "total_timeout": 10,
        "hard_timeout_per_logical": 2,
        "early_stop": 1,
    }

    with pytest.raises(
        distance_milp.CssCheckpointCorruptionError,
        match="invalid CSS MILP checkpoint JSON",
    ):
        distance_milp.write_symplectic_weight_checkpoint(
            code,
            **arguments,
            reset_incompatible_checkpoint=False,
        )
    assert checkpoint.read_bytes() == original_bytes
    assert not list(tmp_path.glob(f"{checkpoint.name}.incompatible-*.json"))

    payload = distance_milp.write_symplectic_weight_checkpoint(
        code,
        **arguments,
        reset_incompatible_checkpoint=True,
    )

    archive = checkpoint.with_name(
        f"{checkpoint.name}.incompatible-{original_sha256}.json"
    )
    assert archive.read_bytes() == original_bytes
    assert payload["kind"] == "qcode-symplectic-weight-checkpoint"
    assert payload["status"] == "exact"
    assert payload["symplectic_witness"] == witness
    assert json.loads(checkpoint.read_text()) == payload


def _css_matrices():
    hx = np.zeros((1, 4), dtype=int)
    hz = np.zeros((1, 4), dtype=int)
    lx = np.array([[1, 0, 0, 0]], dtype=int)
    lz = np.array([[0, 1, 0, 0]], dtype=int)
    return hx, hz, lx, lz


def _abrupt_parent_with_css_worker(connection, exit_mode):
    solver = distance_milp._HardWallCssDirectionSolver(*_css_matrices())
    solver._start()
    connection.send(solver._process.pid)
    connection.close()
    if exit_mode == "os_exit":
        os._exit(0)
    os.kill(os.getpid(), signal.SIGKILL)


def _pid_is_live(pid):
    try:
        stat = (distance_milp.Path("/proc") / str(pid) / "stat").read_text()
    except (FileNotFoundError, ProcessLookupError):
        return False
    except OSError:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        return True
    # A killed orphan can briefly remain as a zombie until PID 1 reaps it;
    # it is no longer a surviving worker and cannot execute HiGHS.
    return stat.rsplit(")", 1)[1].strip().split()[0] != "Z"


def _wait_until_not_live(pid, timeout=5.0):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not _pid_is_live(pid):
            return True
        time.sleep(0.02)
    return not _pid_is_live(pid)


def test_css_checkpoint_resume_reuses_optimal_and_retries_unresolved(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    first_calls = []
    first_results = iter([
        (3, True, [1, 1, 1, 0]),
        (None, False, None),
    ])

    def first_solver(*_args, **_kwargs):
        first_calls.append(1)
        return next(first_results)

    monkeypatch.setattr(distance_milp, "ilp_min_weight", first_solver)
    checkpoint = tmp_path / "candidate.milp-checkpoint.json"
    identity = {"family": "css-bb", "candidate": "resume-me"}

    distance, partial = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )

    assert distance == 3
    assert partial["exact"] is False
    assert partial["checkpoint_status"] == "unresolved"
    assert partial["pending_direction_ids"] == ["X:0"]
    assert partial["minimum_direction_witness"] == {
        "side": "Z",
        "index": 0,
        "weight": 3,
        "bits": [1, 1, 1, 0],
    }
    assert len(first_calls) == 2
    first_checkpoint = json.loads(checkpoint.read_text())
    assert first_checkpoint["direction_results"]["Z:0"]["status"] == "optimal"
    assert (
        first_checkpoint["direction_results"]["X:0"]["status"]
        == "no_incumbent"
    )
    assert first_checkpoint["direction_results"]["Z:0"]["witness"] == [1, 1, 1, 0]
    assert first_checkpoint["direction_results"]["X:0"]["witness"] is None

    resumed_calls = []

    def resumed_solver(*_args, **_kwargs):
        resumed_calls.append(1)
        return 2, True, [1, 1, 0, 0]

    monkeypatch.setattr(distance_milp, "ilp_min_weight", resumed_solver)
    distance, exact = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=2,
        total_timeout=20,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )

    assert distance == 2
    assert exact["exact"] is True
    assert exact["checkpoint_resumed"] is True
    assert exact["checkpoint_directions_reused"] == 1
    assert exact["pending_direction_ids"] == []
    assert exact["minimum_direction_witness"] == {
        "side": "X",
        "index": 0,
        "weight": 2,
        "bits": [1, 1, 0, 0],
    }
    assert resumed_calls == [1]
    final_checkpoint = json.loads(checkpoint.read_text())
    assert final_checkpoint["status"] == "exact"
    assert len(final_checkpoint["parameter_history"]) == 2
    assert not list(tmp_path.glob(".*.tmp-*"))


def test_css_checkpoint_rejects_candidate_matrix_and_budget_mismatch(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def exact_logical_witness(_checks, logical, **_kwargs):
        witness = [int(value) for value in logical]
        return sum(witness), True, witness

    monkeypatch.setattr(distance_milp, "ilp_min_weight", exact_logical_witness)
    checkpoint = tmp_path / "bound.json"
    identity = {"candidate": "bound"}
    distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=2,
        total_timeout=20,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )
    payload = json.loads(checkpoint.read_text())
    binding = payload["proof_binding"]
    assert binding["candidate_identity"] == identity
    assert binding["matrix_bundle_sha256"]
    assert binding["directions_sha256"]
    assert payload["schema_version"] == 2
    assert [row["direction_id"] for row in binding["directions"]] == [
        "Z:0", "X:0",
    ]
    assert binding["solver"]["backend"] == "scipy.optimize.milp-highs"
    assert binding["solver"]["formulation_revision"]
    implementation = binding["implementation"]
    assert len(implementation["distance_milp_py_sha256"]) == 64
    assert implementation["formulation_revision"]
    assert set(implementation["versions"]) == {"numpy", "scipy", "qldpc"}
    assert all(
        isinstance(version, str) and version
        for version in implementation["versions"].values()
    )
    assert implementation["proof_runtime"]["schema_version"] == 2
    assert implementation["proof_runtime"]["interpreter"][
        "executable_file"
    ]["sha256"]

    with pytest.raises(ValueError, match="binding mismatch"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=2,
            total_timeout=20,
            checkpoint_path=checkpoint,
            checkpoint_identity={"candidate": "different"},
        )
    with pytest.raises(ValueError, match="cannot reduce bound budget"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=20,
            checkpoint_path=checkpoint,
            checkpoint_identity=identity,
        )

    changed = list(matrices)
    changed[2] = np.array([[0, 0, 1, 0]], dtype=int)
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: tuple(changed)
    )
    with pytest.raises(ValueError, match="binding mismatch"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=2,
            total_timeout=20,
            checkpoint_path=checkpoint,
            checkpoint_identity=identity,
        )


def test_css_checkpoint_replays_witness_and_rejects_corruption(
    tmp_path, monkeypatch,
):
    matrices = (
        np.array([[0, 1, 0, 0]], dtype=int),
        np.array([[1, 0, 0, 0]], dtype=int),
        np.array([[1, 0, 0, 0]], dtype=int),
        np.array([[0, 1, 0, 0]], dtype=int),
    )
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def exact_logical_witness(_checks, logical, **_kwargs):
        witness = [int(value) for value in logical]
        return sum(witness), True, witness

    monkeypatch.setattr(distance_milp, "ilp_min_weight", exact_logical_witness)
    checkpoint = tmp_path / "witness-bound.json"
    identity = {"candidate": "witness-bound"}
    distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )
    original = json.loads(checkpoint.read_text())

    corruptions = [
        (
            "invalid feasible witness",
            lambda row: row.update({"weight": 2, "witness": [1, 1, 0, 0]}),
        ),
        (
            "invalid feasible witness",
            lambda row: row.update({"weight": 1, "witness": [0, 0, 1, 0]}),
        ),
        (
            "invalid feasible witness",
            lambda row: row.update({"weight": 2, "witness": [1, 0, 0, 0]}),
        ),
        (
            "invalid feasible witness",
            lambda row: row.update({"weight": 1, "witness": [2, 0, 0, 0]}),
        ),
        (
            "unresolved direction retained a witness",
            lambda row: row.update({"status": "no_incumbent", "optimal": False}),
        ),
        (
            "invalid last attempt status",
            lambda row: row.update({"last_attempt_status": "corrupted"}),
        ),
    ]
    for message, mutate in corruptions:
        corrupted = json.loads(json.dumps(original))
        mutate(corrupted["direction_results"]["Z:0"])
        checkpoint.write_text(json.dumps(corrupted))
        with pytest.raises(ValueError, match=message):
            distance_milp.compute_distance_milp(
                DummyCssCode(),
                early_stop=None,
                timeout_per_logical=1,
                total_timeout=10,
                checkpoint_path=checkpoint,
                checkpoint_identity=identity,
            )

    old_schema = json.loads(json.dumps(original))
    old_schema["schema_version"] = 1
    checkpoint.write_text(json.dumps(old_schema))
    with pytest.raises(ValueError, match="unsupported.*schema"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity=identity,
        )

    wrong_fingerprint = json.loads(json.dumps(original))
    wrong_fingerprint["proof_binding"]["implementation"]["versions"]["scipy"] = (
        "tampered"
    )
    checkpoint.write_text(json.dumps(wrong_fingerprint))
    with pytest.raises(ValueError, match="binding mismatch"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity=identity,
        )

    distance, reset = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
        reset_incompatible_checkpoint=True,
    )
    assert distance == 1
    assert reset["exact"] is True
    assert reset["checkpoint_reset"] is True
    assert "binding mismatch" in reset["checkpoint_reset_reason"]
    archive = Path(reset["checkpoint_incompatible_archive"])
    assert archive.is_file()
    assert (
        json.loads(archive.read_text())["proof_binding"]["implementation"][
            "versions"
        ]["scipy"]
        == "tampered"
    )
    assert json.loads(checkpoint.read_text())["proof_binding"] != (
        wrong_fingerprint["proof_binding"]
    )


def test_css_checkpoint_reset_archives_truncated_json_by_raw_sha256(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def exact_logical_witness(_checks, logical, **_kwargs):
        witness = [int(value) for value in logical]
        return sum(witness), True, witness

    monkeypatch.setattr(distance_milp, "ilp_min_weight", exact_logical_witness)
    checkpoint = tmp_path / "truncated.json"
    original_bytes = b'{"kind":"truncated"'
    checkpoint.write_bytes(original_bytes)
    original_sha256 = hashlib.sha256(original_bytes).hexdigest()

    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity={"candidate": "truncated"},
        reset_incompatible_checkpoint=True,
    )

    archive = Path(details["checkpoint_incompatible_archive"])
    assert distance == 1
    assert details["exact"] is True
    assert details["checkpoint_reset"] is True
    assert "invalid CSS MILP checkpoint JSON" in details["checkpoint_reset_reason"]
    assert archive.name == (
        f"{checkpoint.name}.incompatible-{original_sha256}.json"
    )
    assert archive.read_bytes() == original_bytes
    assert json.loads(checkpoint.read_text())["status"] == "exact"


@pytest.mark.parametrize(
    ("label", "mutate", "reason"),
    [
        (
            "body",
            lambda payload: payload.update({"status": {"corrupt": True}}),
            "invalid aggregate status",
        ),
        (
            "witness",
            lambda payload: payload["direction_results"]["Z:0"].update(
                {"witness": [0, 0, 1, 0]}
            ),
            "invalid feasible witness",
        ),
        (
            "budget",
            lambda payload: payload["run_parameters"].update(
                {"timeout_per_logical_s": "corrupt"}
            ),
            "invalid bound budget",
        ),
        (
            "record",
            lambda payload: payload["direction_results"]["Z:0"].pop("attempts"),
            "direction record fields mismatch",
        ),
    ],
)
def test_css_checkpoint_reset_archives_bound_corruption_and_recomputes(
    tmp_path, monkeypatch, label, mutate, reason,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def exact_logical_witness(_checks, logical, **_kwargs):
        witness = [int(value) for value in logical]
        return sum(witness), True, witness

    monkeypatch.setattr(distance_milp, "ilp_min_weight", exact_logical_witness)
    checkpoint = tmp_path / f"{label}.json"
    identity = {"candidate": label}
    distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )
    corrupted = json.loads(checkpoint.read_text())
    mutate(corrupted)
    original_bytes = json.dumps(
        corrupted,
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    checkpoint.write_bytes(original_bytes)
    original_sha256 = hashlib.sha256(original_bytes).hexdigest()

    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
        reset_incompatible_checkpoint=True,
    )

    archive = Path(details["checkpoint_incompatible_archive"])
    assert distance == 1
    assert details["exact"] is True
    assert details["checkpoint_reset"] is True
    assert reason in details["checkpoint_reset_reason"]
    assert archive.name == (
        f"{checkpoint.name}.incompatible-{original_sha256}.json"
    )
    assert archive.read_bytes() == original_bytes
    assert json.loads(checkpoint.read_text())["status"] == "exact"


def test_css_checkpoint_reset_does_not_catch_fresh_solver_failure(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    calls = []

    def broken_fresh_solver(*_args, **_kwargs):
        calls.append(1)
        raise RuntimeError("fresh solver bug")

    monkeypatch.setattr(distance_milp, "ilp_min_weight", broken_fresh_solver)
    checkpoint = tmp_path / "fresh-failure.json"
    original_bytes = b'{"direction_results":'
    checkpoint.write_bytes(original_bytes)
    original_sha256 = hashlib.sha256(original_bytes).hexdigest()

    with pytest.raises(RuntimeError, match="fresh solver bug"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity={"candidate": "fresh-failure"},
            reset_incompatible_checkpoint=True,
        )

    archives = list(
        tmp_path.glob(f"{checkpoint.name}.incompatible-*.json")
    )
    assert calls == [1]
    assert len(archives) == 1
    assert archives[0].name == (
        f"{checkpoint.name}.incompatible-{original_sha256}.json"
    )
    assert archives[0].read_bytes() == original_bytes
    assert json.loads(checkpoint.read_text())["status"] == "running"


def test_css_checkpoint_none_to_finite_hard_timeout_reuses_only_optimal(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    initial_results = iter([
        (1, True, [1, 0, 0, 0]),
        (1, False, [0, 1, 0, 0]),
    ])
    monkeypatch.setattr(
        distance_milp,
        "ilp_min_weight",
        lambda *_args, **_kwargs: next(initial_results),
    )
    checkpoint = tmp_path / "hard-timeout-migration.json"
    identity = {"candidate": "hard-timeout-migration"}
    _, partial = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=10,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )
    assert partial["exact"] is False
    before = json.loads(checkpoint.read_text())
    assert before["direction_results"]["Z:0"]["status"] == "optimal"
    assert before["direction_results"]["X:0"]["status"] == "incumbent"

    calls = []

    class FakeHardWallSolver:
        def __init__(self, *_arrays):
            pass

        def solve(self, side, index, **_kwargs):
            calls.append((side, index))
            assert side == "X"
            return 1, True, "optimal", [0, 1, 0, 0]

        def close(self):
            pass

    monkeypatch.setattr(
        distance_milp, "_HardWallCssDirectionSolver", FakeHardWallSolver
    )
    distance, exact = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=2,
        total_timeout=20,
        hard_timeout_per_logical=5,
        checkpoint_path=checkpoint,
        checkpoint_identity=identity,
    )

    assert distance == 1
    assert exact["exact"] is True
    assert exact["checkpoint_directions_reused"] == 1
    assert calls == [("X", 0)]
    migrated = json.loads(checkpoint.read_text())
    assert migrated["direction_results"]["Z:0"]["attempts"] == 1
    assert migrated["direction_results"]["X:0"]["attempts"] == 1


def test_css_checkpoint_flock_serializes_complete_computation(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    first_direction_started = threading.Event()
    release_first_direction = threading.Event()
    calls_lock = threading.Lock()
    calls = []

    def slow_exact_solver(_checks, logical, **_kwargs):
        with calls_lock:
            calls.append([int(value) for value in logical])
            call_number = len(calls)
        if call_number == 1:
            first_direction_started.set()
            assert release_first_direction.wait(timeout=5)
        witness = [int(value) for value in logical]
        return sum(witness), True, witness

    monkeypatch.setattr(distance_milp, "ilp_min_weight", slow_exact_solver)
    checkpoint = tmp_path / "flock.json"

    def run():
        return distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity={"candidate": "flock"},
        )

    with ThreadPoolExecutor(max_workers=2) as pool:
        first = pool.submit(run)
        assert first_direction_started.wait(timeout=5)
        second = pool.submit(run)
        time.sleep(0.05)
        assert not second.done()
        release_first_direction.set()
        first_result = first.result(timeout=10)
        second_result = second.result(timeout=10)

    assert first_result[1]["exact"] is True
    assert second_result[1]["exact"] is True
    assert second_result[1]["checkpoint_directions_reused"] == 2
    assert len(calls) == 2
    assert json.loads(checkpoint.read_text())["status"] == "exact"


@pytest.mark.parametrize("lock_kind", ["symlink", "directory"])
def test_css_checkpoint_lock_rejects_symlink_and_non_regular_file(
    tmp_path, monkeypatch, lock_kind,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def unexpected_solver(*_args, **_kwargs):
        raise AssertionError("solver must not run with an unsafe lock path")

    monkeypatch.setattr(distance_milp, "ilp_min_weight", unexpected_solver)
    checkpoint = tmp_path / f"unsafe-{lock_kind}.json"
    lock_path = tmp_path / f".{checkpoint.name}.lock"
    if lock_kind == "symlink":
        target = tmp_path / "lock-target"
        target.write_text("must-not-change")
        lock_path.symlink_to(target)
    else:
        target = None
        lock_path.mkdir()

    with pytest.raises(ValueError, match="non-symlink regular file"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity={"candidate": f"unsafe-{lock_kind}"},
            reset_incompatible_checkpoint=True,
        )
    assert not checkpoint.exists()
    if target is not None:
        assert target.read_text() == "must-not-change"


@pytest.mark.parametrize("checkpoint_kind", ["symlink", "directory", "fifo"])
def test_css_checkpoint_file_rejects_symlink_and_non_regular_file(
    tmp_path, monkeypatch, checkpoint_kind,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )

    def unexpected_solver(*_args, **_kwargs):
        raise AssertionError("solver must not run with an unsafe checkpoint path")

    monkeypatch.setattr(distance_milp, "ilp_min_weight", unexpected_solver)
    checkpoint = tmp_path / f"unsafe-checkpoint-{checkpoint_kind}.json"
    if checkpoint_kind == "symlink":
        target = tmp_path / "checkpoint-target"
        target.write_text("must-not-change")
        checkpoint.symlink_to(target)
    elif checkpoint_kind == "directory":
        target = None
        checkpoint.mkdir()
    else:
        target = None
        os.mkfifo(checkpoint)

    with pytest.raises(ValueError, match="non-symlink regular file"):
        distance_milp.compute_distance_milp(
            DummyCssCode(),
            early_stop=None,
            timeout_per_logical=1,
            total_timeout=10,
            checkpoint_path=checkpoint,
            checkpoint_identity={
                "candidate": f"unsafe-checkpoint-{checkpoint_kind}"
            },
            reset_incompatible_checkpoint=True,
        )
    if target is not None:
        assert target.read_text() == "must-not-change"


def test_css_d_x_computed_requires_an_executed_x_direction(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    calls = []

    def z_only_solver(*_args, **_kwargs):
        calls.append(1)
        if len(calls) > 1:
            raise AssertionError("X direction must not execute after budget expiry")
        return 1, True, [1, 0, 0, 0]

    monkeypatch.setattr(distance_milp, "ilp_min_weight", z_only_solver)
    ticks = iter([0.0, 0.0, 0.0, 0.0, 2.0, 2.0])
    monkeypatch.setattr(distance_milp.time, "monotonic", lambda: next(ticks))
    _, details = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=1,
        total_timeout=1,
        checkpoint_path=tmp_path / "x-not-run.json",
        checkpoint_identity={"candidate": "x-not-run"},
    )
    assert calls == [1]
    assert details["d_x_computed"] is False
    assert details["pending_direction_ids"] == ["X:0"]


def test_css_hard_wall_timeout_kills_worker_and_is_never_exact(
    tmp_path, monkeypatch,
):
    matrices = _css_matrices()
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: matrices
    )
    checkpoint = tmp_path / "hard-timeout.json"
    children_before = {child.pid for child in multiprocessing.active_children()}

    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=10,
        total_timeout=1,
        hard_timeout_per_logical=0.01,
        checkpoint_path=checkpoint,
        checkpoint_identity={"candidate": "hard-timeout"},
    )

    assert distance == DummyCssCode.num_qudits
    assert details["exact"] is False
    assert details["all_timeout"] is True
    assert details["no_incumbent"] is True
    assert details["hard_wall_timeouts"] >= 1
    assert details["checkpoint_status"] == "unresolved"
    payload = json.loads(checkpoint.read_text())
    assert payload["status"] == "unresolved"
    assert all(
        row["status"] == "hard_timeout"
        and row["weight"] is None
        and row["witness"] is None
        for row in payload["direction_results"].values()
    )
    children_after = {child.pid for child in multiprocessing.active_children()}
    assert children_after <= children_before

    distance, resumed = distance_milp.compute_distance_milp(
        DummyCssCode(),
        early_stop=None,
        timeout_per_logical=10,
        total_timeout=20,
        hard_timeout_per_logical=10,
        checkpoint_path=checkpoint,
        checkpoint_identity={"candidate": "hard-timeout"},
    )

    assert distance == 1
    assert resumed["exact"] is True
    assert resumed["checkpoint_resumed"] is True
    assert resumed["checkpoint_directions_reused"] == 0
    assert resumed["hard_wall_timeouts"] >= 1
    assert resumed["direction_status_counts"]["optimal"] == 2
    recovered = json.loads(checkpoint.read_text())
    assert recovered["status"] == "exact"
    assert all(
        row["attempts"] == 2
        for row in recovered["direction_results"].values()
    )


@pytest.mark.skipif(not sys.platform.startswith("linux"), reason="Linux prctl")
@pytest.mark.parametrize("exit_mode", ["os_exit", "sigkill"])
def test_css_hard_wall_worker_dies_with_abrupt_parent(exit_mode):
    context = multiprocessing.get_context("fork")
    receiver, sender = context.Pipe(duplex=False)
    parent = context.Process(
        target=_abrupt_parent_with_css_worker,
        args=(sender, exit_mode),
        name=f"css-milp-abrupt-parent-{exit_mode}",
    )
    parent.start()
    sender.close()
    assert receiver.poll(10), "abrupt parent did not report worker pid"
    worker_pid = receiver.recv()
    receiver.close()
    parent.join(timeout=10)
    assert not parent.is_alive()
    if exit_mode == "sigkill":
        assert parent.exitcode == -signal.SIGKILL
    else:
        assert parent.exitcode == 0
    assert _wait_until_not_live(worker_pid), (
        f"hard-wall worker {worker_pid} survived abrupt parent {exit_mode}"
    )


def test_evaluator_forwards_checkpoint_hard_timeout_and_candidate_identity(
    tmp_path, monkeypatch,
):
    dummy = DummyCssCode()
    monkeypatch.setattr(
        evaluator, "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, dummy.num_qudits, dummy.dimension),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (3, 3, 3)
    )
    captured = {}

    def fake_distance(*_args, **kwargs):
        captured.update(kwargs)
        return dummy.num_qudits, {
            "exact": False,
            "all_timeout": True,
            "total_logicals": 2,
        }

    monkeypatch.setattr(evaluator, "compute_distance_milp", fake_distance)
    checkpoint = tmp_path / "forwarded.json"
    evaluator.evaluate_candidate_milp(
        2,
        1,
        [(1, 0), (0, 0)],
        [(1, 0), (0, 0)],
        milp_early_stop=None,
        milp_checkpoint_path=checkpoint,
        milp_resume=False,
        milp_hard_timeout_per_logical=7,
    )

    assert captured["checkpoint_path"] == checkpoint
    assert captured["resume"] is False
    assert captured["hard_timeout_per_logical"] == 7
    assert captured["checkpoint_identity"] == {
        "family": "css-bb",
        "ell": 2,
        "m": 1,
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 0], [1, 0]],
    }


def test_ilp_constraint_matrices_are_sparse(monkeypatch):
    observed = []

    def fake_milp(*, constraints, **_kwargs):
        observed.append(constraints.A)
        return SimpleNamespace(x=np.zeros(constraints.A.shape[1]), fun=1, success=True)

    monkeypatch.setattr(distance_milp, "milp", fake_milp)
    assert distance_milp.ilp_min_weight(
        np.array([[1, 1]], dtype=int), np.array([1, 0], dtype=int)
    ) == (1, True)
    assert distance_milp.ilp_min_weight_symplectic(
        np.array([[1, 0, 0, 1]], dtype=int),
        np.array([1, 0, 0, 0], dtype=int),
    ) == (1, True)
    assert len(observed) == 2
    assert all(issparse(matrix) for matrix in observed)
