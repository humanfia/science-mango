from itertools import product

import numpy as np

from evaluation import distance_milp
from evaluation.bb_code import build_bb_code


def _small_real_code():
    # A real [[8,4,2]] BB code with eight logical directions.
    return build_bb_code(
        2,
        2,
        [(0, 0), (0, 1)],
        [(1, 0), (1, 1)],
    )


def _direction_records(code, weight):
    return {
        f"{side}:{index}": {
            "side": side,
            "index": index,
            "weight": weight,
            # Stored solver claims are intentionally irrelevant to replay.
            "status": "optimal",
            "optimal": True,
        }
        for side in ("Z", "X")
        for index in range(int(code.dimension))
    }


def test_exact_replay_freshly_proves_every_direction_of_real_small_code():
    code = _small_real_code()

    replay = distance_milp.replay_css_exact_directions(
        code,
        _direction_records(code, 2),
        timeout_per_logical=5,
        hard_timeout_per_logical=10,
        total_timeout=60,
    )

    assert replay.status == "exact"
    assert replay.exact is True
    assert replay.checked_directions == replay.total_directions == 8
    assert replay.reason == "all_directions_replayed"


def test_exact_replay_rejects_feasible_high_weight_optimal_forgery():
    code = _small_real_code()
    hx, hz, lx, lz = distance_milp.get_code_matrices(code)
    forged = {}
    for side, checks, logicals in (("Z", hx, lx), ("X", hz, lz)):
        for index, logical in enumerate(logicals):
            feasible = [
                bits
                for bits in product((0, 1), repeat=int(code.num_qudits))
                if not np.any(
                    (checks @ np.asarray(bits, dtype=np.uint8)) % 2
                )
                and int(
                    np.dot(
                        logical,
                        np.asarray(bits, dtype=np.uint8),
                    )
                    % 2
                )
                == 1
            ]
            witness = max(feasible, key=sum)
            assert sum(witness) == 6
            forged[f"{side}:{index}"] = {
                "side": side,
                "index": index,
                "weight": 6,
                "witness": list(witness),
                "status": "optimal",
                "optimal": True,
            }

    replay = distance_milp.replay_css_exact_directions(
        code,
        forged,
        timeout_per_logical=5,
        hard_timeout_per_logical=10,
        total_timeout=60,
    )

    assert replay.status == "mismatch"
    assert replay.mismatch is True
    assert replay.reason == "optimal_weight_mismatch"
    assert replay.direction_id == "Z:0"
    assert replay.expected_weight == 6
    assert replay.observed_weight == 2


def test_exact_replay_reports_hard_timeout_as_unavailable(monkeypatch):
    code = _small_real_code()
    calls = []

    class TimeoutSolver:
        def __init__(self, *_matrices):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *_exc_info):
            pass

        def solve(self, side, index, *, soft_timeout, hard_timeout):
            calls.append((side, index, soft_timeout, hard_timeout))
            return None, False, "hard_timeout", None

    monkeypatch.setattr(
        distance_milp, "_HardWallCssDirectionSolver", TimeoutSolver
    )

    replay = distance_milp.replay_css_exact_directions(
        code,
        _direction_records(code, 2),
        timeout_per_logical=2,
        hard_timeout_per_logical=3,
        total_timeout=4,
    )

    assert replay.status == "unavailable"
    assert replay.unavailable is True
    assert replay.reason == "direction_hard_timeout"
    assert replay.direction_id == "Z:0"
    assert replay.checked_directions == 0
    assert len(calls) == 1
    assert 0 < calls[0][2] <= calls[0][3] <= 3


def test_exact_replay_enforces_total_wall_budget(monkeypatch):
    code = _small_real_code()
    calls = []

    class LateSolver:
        def __init__(self, *_matrices):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *_exc_info):
            pass

        def solve(self, side, index, *, soft_timeout, hard_timeout):
            calls.append((soft_timeout, hard_timeout))
            return 2, True, "optimal", [0] * int(code.num_qudits)

    ticks = iter((0.0, 0.0, 0.02, 0.02))
    monkeypatch.setattr(distance_milp.time, "monotonic", lambda: next(ticks))
    monkeypatch.setattr(
        distance_milp, "_HardWallCssDirectionSolver", LateSolver
    )

    replay = distance_milp.replay_css_exact_directions(
        code,
        _direction_records(code, 2),
        timeout_per_logical=1,
        hard_timeout_per_logical=1,
        total_timeout=0.01,
    )

    assert replay.status == "unavailable"
    assert replay.reason == "total_wall_timeout"
    assert replay.checked_directions == 0
    assert len(calls) == 1
    assert 0 < calls[0][0] <= calls[0][1] <= 0.01


def test_exact_replay_reports_solver_failure_as_unavailable(monkeypatch):
    code = _small_real_code()

    class BrokenSolver:
        def __init__(self, *_matrices):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *_exc_info):
            pass

        def solve(self, *_args, **_kwargs):
            raise RuntimeError("solver backend missing")

    monkeypatch.setattr(
        distance_milp, "_HardWallCssDirectionSolver", BrokenSolver
    )

    replay = distance_milp.replay_css_exact_directions(
        code,
        _direction_records(code, 2),
        timeout_per_logical=1,
        hard_timeout_per_logical=2,
        total_timeout=3,
    )

    assert replay.status == "unavailable"
    assert replay.reason == "solver_unavailable"
    assert replay.direction_id == "Z:0"
    assert replay.checked_directions == 0
