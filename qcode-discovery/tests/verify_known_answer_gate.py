"""Strict known-answer gate for the qLDPC benchmark challenge.

Rebuild and exactly verify [[72,12,6]], [[90,8,10]], and [[144,12,12]].
Acceptance requires valid inputs, CSS commutation, weight/degree at most six,
a connected Tanner graph, independent GF(2) ranks, and all 2k MILP logical
directions solved to proven optimality with early stopping disabled.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import platform
import sys
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.distance_milp import compute_distance_milp, get_code_matrices


BASELINES = [
    {
        "label": "[[72,12,6]]", "ell": 6, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": {"n": 72, "k": 12, "d": 6},
    },
    {
        "label": "[[90,8,10]]", "ell": 15, "m": 3,
        "A_terms": [(9, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (2, 0), (7, 0)],
        "expected": {"n": 90, "k": 8, "d": 10},
    },
    {
        "label": "[[144,12,12]]", "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": {"n": 144, "k": 12, "d": 12},
    },
]


def rank_f2(matrix: np.ndarray) -> int:
    """Compute matrix rank over GF(2), independently of qldpc."""
    work = np.asarray(matrix, dtype=np.uint8).copy() & 1
    rows, cols = work.shape
    rank = 0
    for col in range(cols):
        pivots = np.flatnonzero(work[rank:, col])
        if not pivots.size:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            work[[rank, pivot]] = work[[pivot, rank]]
        other_rows = np.flatnonzero(work[:, col])
        other_rows = other_rows[other_rows != rank]
        if other_rows.size:
            work[other_rows] ^= work[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def matrix_sha256(matrix: np.ndarray) -> str:
    """Hash a binary matrix with its shape using a stable packed encoding."""
    binary = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def connected_tanner_graph(checks: np.ndarray) -> tuple[bool, int]:
    """Check connectivity of the bipartite graph for stacked CSS checks."""
    matrix = np.asarray(checks, dtype=np.uint8) & 1
    num_checks, num_qubits = matrix.shape
    adjacency = [[] for _ in range(num_checks + num_qubits)]
    for check_idx, qubit_idx in np.argwhere(matrix):
        check_node = int(check_idx)
        qubit_node = num_checks + int(qubit_idx)
        adjacency[check_node].append(qubit_node)
        adjacency[qubit_node].append(check_node)
    unseen = set(range(len(adjacency)))
    components = 0
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            node = stack.pop()
            for neighbor in adjacency[node]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
    return components == 1, components


def package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def verify_baseline(spec: dict, *, timeout_per_logical: int,
                    total_timeout_per_code: int, verbose: bool) -> dict:
    """Rebuild one baseline and return its complete gate record."""
    ell, m = spec["ell"], spec["m"]
    a_terms, b_terms = spec["A_terms"], spec["B_terms"]
    expected = spec["expected"]
    checks: dict[str, bool] = {}
    failures: list[str] = []

    try:
        validate_terms(ell, m, a_terms, "A")
        validate_terms(ell, m, b_terms, "B")
        checks["valid_polynomials"] = True
    except ValueError as exc:
        checks["valid_polynomials"] = False
        failures.append(f"invalid polynomial input: {exc}")
        return {**spec, "status": "failed", "checks": checks,
                "failures": failures}

    code = build_bb_code(ell, m, a_terms, b_terms)
    hx, hz, _, _ = get_code_matrices(code)
    hx = np.asarray(hx, dtype=np.uint8) & 1
    hz = np.asarray(hz, dtype=np.uint8) & 1
    stacked = np.vstack((hx, hz))
    n = int(code.num_qudits)

    commutation_violations = int(np.count_nonzero((hx @ hz.T) & 1))
    checks["css_commutation"] = commutation_violations == 0
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    checks["weight_bound"] = max_row_weight <= 6 and max_qubit_degree <= 6
    connected, components = connected_tanner_graph(stacked)
    checks["connected_tanner_graph"] = connected

    rank_hx = rank_f2(hx)
    rank_hz = rank_f2(hz)
    k = n - rank_hx - rank_hz
    checks["expected_n"] = n == expected["n"]
    checks["expected_k"] = k == expected["k"]
    checks["qldpc_k_crosscheck"] = int(code.dimension) == k

    distance, milp = compute_distance_milp(
        code,
        timeout_per_logical=timeout_per_logical,
        total_timeout=total_timeout_per_code,
        early_stop=None,
        verbose=verbose,
    )
    total_logicals = 2 * k
    exact_milp = (
        bool(milp.get("exact"))
        and int(milp.get("num_logicals_checked", 0)) == total_logicals
        and int(milp.get("logicals_optimal", 0)) == total_logicals
        and int(milp.get("logicals_incumbent", 0)) == 0
    )
    checks["all_milp_directions_optimal"] = exact_milp
    checks["expected_d"] = exact_milp and int(distance) == expected["d"]
    failures.extend(name for name, passed in checks.items() if not passed)

    return {
        "label": spec["label"], "ell": ell, "m": m,
        "A_terms": a_terms, "B_terms": b_terms, "expected": expected,
        "observed": {
            "n": n, "rank_hx": rank_hx, "rank_hz": rank_hz, "k": k,
            "d": int(distance), "fom": k * int(distance) ** 2 / n,
            "commutation_violations": commutation_violations,
            "max_row_weight": max_row_weight,
            "max_qubit_degree": max_qubit_degree,
            "tanner_components": components,
        },
        "matrix_sha256": {"hx": matrix_sha256(hx), "hz": matrix_sha256(hz)},
        "milp": milp, "checks": checks, "failures": failures,
        "status": "passed" if not failures else "failed",
    }


def parse_args() -> argparse.Namespace:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=project / "results" / "known_answer_gate.json")
    parser.add_argument("--timeout-per-logical", type=int, default=300)
    parser.add_argument("--total-timeout-per-code", type=int, default=7200)
    parser.add_argument("-v", "--verbose", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    records = []
    for spec in BASELINES:
        print(f"\nVerifying {spec['label']} with all 2k MILP directions...",
              flush=True)
        record = verify_baseline(
            spec,
            timeout_per_logical=args.timeout_per_logical,
            total_timeout_per_code=args.total_timeout_per_code,
            verbose=args.verbose,
        )
        records.append(record)
        observed = record.get("observed", {})
        print(f"  {record['status'].upper()}: n={observed.get('n')} "
              f"k={observed.get('k')} d={observed.get('d')}", flush=True)
        if record["failures"]:
            print(f"  failures: {', '.join(record['failures'])}", flush=True)

    passed = all(record["status"] == "passed" for record in records)
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-known-answer-baselines",
        "challenge_source": "https://gist.github.com/ShuxiangCao/aa35ff78f403ed7ab730e36e165c3cf1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "method": {
            "distance": "scipy.optimize.milp (HiGHS), early_stop disabled",
            "acceptance": "all 2k logical directions solved to proven optimality",
            "timeout_per_logical_s": args.timeout_per_logical,
            "total_timeout_per_code_s": args.total_timeout_per_code,
        },
        "environment": {
            "python": platform.python_version(), "numpy": package_version("numpy"),
            "scipy": package_version("scipy"), "qldpc": package_version("qldpc"),
        },
        "passed": passed,
        "summary": {"passed": sum(r["status"] == "passed" for r in records),
                    "total": len(records)},
        "baselines": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(artifact, indent=2) + "\n")
    temporary.replace(args.output)
    print(f"\nGate {'PASSED' if passed else 'FAILED'}: {args.output}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
