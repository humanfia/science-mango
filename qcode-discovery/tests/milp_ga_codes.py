#!/usr/bin/env python3
"""MILP distance verification of best GA codes at (16,9) and (18,8).

Picks the highest-k codes found by the GA that passed the d>=3 screen
(no weight-2 logicals) and computes MILP-verified distances.
"""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.distance_milp import compute_distance_milp

# Best GA codes: k=64 d>=3 from verification run.
# 5 from (16,9) and 5 from (18,8) -- diverse polynomial structures.
GA_CODES = [
    # (16,9) codes -- k=64 at n=288
    {"ell": 16, "m": 9,
     "A": [(8, 4), (8, 6), (8, 8)], "B": [(2, 1), (2, 2), (2, 6)],
     "label": "GA-(16,9)-1"},
    {"ell": 16, "m": 9,
     "A": [(8, 1), (8, 6), (8, 8)], "B": [(2, 1), (2, 2), (2, 6)],
     "label": "GA-(16,9)-2"},
    {"ell": 16, "m": 9,
     "A": [(8, 2), (8, 4), (8, 6)], "B": [(2, 1), (2, 2), (2, 6)],
     "label": "GA-(16,9)-3"},
    {"ell": 16, "m": 9,
     "A": [(0, 4), (8, 6), (8, 8)], "B": [(2, 1), (2, 6), (10, 2)],
     "label": "GA-(16,9)-4"},
    {"ell": 16, "m": 9,
     "A": [(8, 4), (8, 6), (8, 8)], "B": [(2, 2), (2, 6), (2, 7)],
     "label": "GA-(16,9)-5"},
    # (18,8) codes -- k=64 at n=288
    {"ell": 18, "m": 8,
     "A": [(0, 0), (2, 0), (16, 0)], "B": [(5, 7), (13, 7), (15, 7)],
     "label": "GA-(18,8)-1"},
    {"ell": 18, "m": 8,
     "A": [(0, 0), (2, 0), (10, 0)], "B": [(13, 7), (15, 7), (17, 7)],
     "label": "GA-(18,8)-2"},
    {"ell": 18, "m": 8,
     "A": [(2, 0), (12, 0), (16, 0)], "B": [(13, 7), (15, 7), (17, 7)],
     "label": "GA-(18,8)-3"},
    {"ell": 18, "m": 8,
     "A": [(2, 0), (12, 0), (16, 0)], "B": [(5, 7), (13, 7), (15, 7)],
     "label": "GA-(18,8)-4"},
    {"ell": 18, "m": 8,
     "A": [(0, 0), (2, 0), (16, 0)], "B": [(3, 7), (5, 7), (13, 7)],
     "label": "GA-(18,8)-5"},
]

# Also include 2 LLM-discovered codes at n=288 as controls
CONTROLS = [
    {"ell": 24, "m": 6,
     "A": [(3, 0), (0, 2), (0, 4)], "B": [(0, 3), (1, 0), (2, 0)],
     "label": "LLM-[[288,12,18]]"},
    {"ell": 12, "m": 12,
     "A": [(6, 0), (0, 1), (0, 2)], "B": [(0, 3), (2, 0), (4, 0)],
     "label": "LLM-[[288,24,12]]"},
]


def main():
    results = []

    print("=" * 70)
    print("MILP DISTANCE VERIFICATION OF BEST GA CODES")
    print("=" * 70, flush=True)

    all_codes = GA_CODES + CONTROLS

    for entry in all_codes:
        ell, m = entry["ell"], entry["m"]
        A, B = entry["A"], entry["B"]
        label = entry["label"]
        n = 2 * ell * m

        code = build_bb_code(ell, m, A, B)
        _, k = get_code_params_fast(code)

        print(f"\n--- {label}: [[{n},{k}]] ---")
        print(f"  A={A}, B={B}", flush=True)

        t0 = time.time()
        d, details = compute_distance_milp(
            code,
            timeout_per_logical=30,
            total_timeout=600,
            early_stop=2,
            verbose=True,
        )
        elapsed = time.time() - t0

        fom = k * d * d / n
        exact = details.get("exact", False)
        tag = "exact" if exact else "upper bound"

        print(f"  d = {d} ({tag}), FOM = {fom:.1f}, time = {elapsed:.1f}s")
        print(f"  d_x = {details.get('d_x', '?')}, d_z = {details.get('d_z', '?')}")
        print(f"  logicals checked: {details.get('num_logicals_checked', '?')}"
              f"/{details.get('total_logicals', '?')}", flush=True)

        results.append({
            "label": label,
            "ell": ell, "m": m,
            "n": n, "k": k,
            "A": A, "B": B,
            "d": d, "fom": round(fom, 2),
            "exact": exact,
            "details": {k2: v for k2, v in details.items()
                        if k2 not in ("d_x_computed",)},
            "time_s": round(elapsed, 1),
        })

    # Summary table
    print(f"\n{'=' * 70}")
    print(f"{'Label':<22} {'n':>4} {'k':>4} {'d':>4} {'FOM':>6} {'exact':>6}")
    print("-" * 50)
    for r in results:
        exact_str = "yes" if r["exact"] else "no"
        print(f"{r['label']:<22} {r['n']:>4} {r['k']:>4} {r['d']:>4} "
              f"{r['fom']:>6.1f} {exact_str:>6}")

    # Save
    out = Path(__file__).resolve().parent.parent / "results" / "milp_ga_codes.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out}")


if __name__ == "__main__":
    main()
