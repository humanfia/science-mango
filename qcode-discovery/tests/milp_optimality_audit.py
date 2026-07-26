"""MILP optimality audit for the paper's key d>=12 codes.

Runs MILP with fixed per-logical timeouts and reports whether each
logical proved optimal. This verifies the "exact distance" claim.

Usage:
    uv run python tests/milp_optimality_audit.py
    uv run python tests/milp_optimality_audit.py --timeout 300
"""

import argparse
import sys
import json
import time
import logging


from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from evaluation.bb_code import build_bb_code
from evaluation.distance_milp import ilp_min_weight, get_code_matrices

logging.basicConfig(level=logging.INFO, format="  %(message)s")

# Focus on the codes that reviewers care about most:
# d=12 and d=14 codes where proving optimality is non-trivial
CODES_TO_AUDIT = [
    {
        "label": "[[144,12,12]] gross code (control)",
        "ell": 12, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "expected_d": 12,
    },
    {
        "label": "[[288,16,12]] at (12,12)",
        "ell": 12, "m": 12,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "expected_d": 12,
    },
    {
        "label": "[[288,24,12]] at (12,12)",
        "ell": 12, "m": 12,
        "A": [(6, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (2, 0), (4, 0)],
        "expected_d": 12,
    },
    {
        "label": "[[360,16,14]] at (15,12)",
        "ell": 15, "m": 12,
        "A": [(0, 2), (0, 4), (3, 0)],
        "B": [(0, 6), (2, 0), (4, 0)],
        "expected_d": 14,
    },
]


def audit_code(entry, timeout_per_logical):
    """Run MILP on all logicals with fixed per-logical timeout."""
    label = entry["label"]
    print(f"\n{'='*60}", flush=True)
    print(f"  {label}", flush=True)
    print(f"{'='*60}", flush=True)

    code = build_bb_code(entry["ell"], entry["m"], entry["A"], entry["B"])
    n, k = code.num_qudits, code.dimension
    print(f"  n={n}, k={k}, expected_d={entry['expected_d']}", flush=True)

    hx, hz, lx, lz = get_code_matrices(code)
    t_start = time.monotonic()

    z_results = []
    x_results = []
    d_z = n
    d_x = n

    print(f"  --- Z-logicals (k={k}) ---", flush=True)
    for i in range(k):
        t0 = time.monotonic()
        w, optimal = ilp_min_weight(hx, lx[i], timeout=timeout_per_logical)
        elapsed = time.monotonic() - t0
        if w is not None:
            d_z = min(d_z, w)
            tag = "optimal" if optimal else "INCUMBENT"
            print(f"    Z[{i:2d}]: w={w:3d} ({tag}, {elapsed:.1f}s)", flush=True)
            z_results.append({"idx": i, "weight": w, "optimal": optimal, "time_s": round(elapsed, 1)})
        else:
            print(f"    Z[{i:2d}]: NO SOLUTION ({elapsed:.1f}s)", flush=True)
            z_results.append({"idx": i, "weight": None, "optimal": False, "time_s": round(elapsed, 1)})

    print(f"  --- X-logicals (k={k}) ---", flush=True)
    for i in range(k):
        t0 = time.monotonic()
        w, optimal = ilp_min_weight(hz, lz[i], timeout=timeout_per_logical)
        elapsed = time.monotonic() - t0
        if w is not None:
            d_x = min(d_x, w)
            tag = "optimal" if optimal else "INCUMBENT"
            print(f"    X[{i:2d}]: w={w:3d} ({tag}, {elapsed:.1f}s)", flush=True)
            x_results.append({"idx": i, "weight": w, "optimal": optimal, "time_s": round(elapsed, 1)})
        else:
            print(f"    X[{i:2d}]: NO SOLUTION ({elapsed:.1f}s)", flush=True)
            x_results.append({"idx": i, "weight": None, "optimal": False, "time_s": round(elapsed, 1)})

    d = min(d_x, d_z)
    total_time = time.monotonic() - t_start

    all_z_optimal = all(r["optimal"] for r in z_results if r["weight"] is not None)
    all_x_optimal = all(r["optimal"] for r in x_results if r["weight"] is not None)
    no_z_missing = all(r["weight"] is not None for r in z_results)
    no_x_missing = all(r["weight"] is not None for r in x_results)
    all_optimal = all_z_optimal and all_x_optimal and no_z_missing and no_x_missing

    num_optimal = sum(1 for r in z_results + x_results if r.get("optimal"))
    num_incumbent = sum(1 for r in z_results + x_results if r["weight"] is not None and not r["optimal"])
    num_total = 2 * k

    print(f"\n  RESULT: d = {d} (d_X={d_x}, d_Z={d_z})", flush=True)
    print(f"  Proven exact: {all_optimal} ({num_optimal}/{num_total} optimal, {num_incumbent} incumbent)", flush=True)
    print(f"  Match expected: {d == entry['expected_d']}", flush=True)
    print(f"  Total time: {total_time:.1f}s", flush=True)

    return {
        "label": label, "n": n, "k": k,
        "d": d, "d_x": d_x, "d_z": d_z,
        "expected_d": entry["expected_d"],
        "match": d == entry["expected_d"],
        "all_optimal": all_optimal,
        "logicals_total": num_total,
        "logicals_optimal": num_optimal,
        "logicals_incumbent": num_incumbent,
        "total_time_s": round(total_time, 1),
        "timeout_per_logical": timeout_per_logical,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=120,
                        help="Timeout per logical operator (seconds)")
    args = parser.parse_args()

    results = []
    for entry in CODES_TO_AUDIT:
        result = audit_code(entry, args.timeout)
        results.append(result)

        # Incremental save
        with open("results/milp_optimality_audit.json", "w") as f:
            json.dump(results, f, indent=2)

    print(f"\n{'='*60}", flush=True)
    print(f"  SUMMARY (timeout={args.timeout}s per logical)", flush=True)
    print(f"{'='*60}", flush=True)

    for r in results:
        tag = "EXACT" if r["all_optimal"] else "UPPER BOUND"
        print(f"  {r['label']}: d={r['d']} [{tag}] ({r['logicals_optimal']}/{r['logicals_total']} optimal) ({r['total_time_s']}s)", flush=True)

    all_exact = all(r["all_optimal"] for r in results)
    print(f"\n  All proven exact: {all_exact}", flush=True)
    print(f"  Results saved to results/milp_optimality_audit.json", flush=True)


if __name__ == "__main__":
    main()
