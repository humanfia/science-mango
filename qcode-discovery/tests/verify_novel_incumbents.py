"""Verify top novel incumbent codes from Campaign 5 with full MILP budgets.

These are BLISS-confirmed novel codes (not equivalent to any known reference)
with the highest FOM upper bounds from evolution. Full MILP verification
(300s/logical, 7200s total) should tighten or confirm distance bounds.

Usage:
    uv run python tests/verify_novel_incumbents.py
    uv run python tests/verify_novel_incumbents.py --quick   # 60s/logical
"""

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.distance_milp import compute_distance_milp


# Top 25 novel incumbent codes from Campaign 5, ordered by FOM upper bound.
# All confirmed novel via BLISS Tanner graph canonical labeling.
CODES_TO_VERIFY = [
    {
        "name": "[[360,8,d<=46]] A=x3+y+y2 B=y3+x13+x14",
        "ell": 15, "m": 12,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (13, 0), (14, 0)],
        "d_ub": 46, "expected_fom": 47.0,
    },
    {
        "name": "[[360,8,d<=44]] A=x5+y5+y6 B=y+x2+x6",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 5), (0, 6)],
        "B": [(0, 1), (2, 0), (6, 0)],
        "d_ub": 44, "expected_fom": 43.0,
    },
    {
        "name": "[[360,8,d<=42]] A=x3+y2+y7 B=y3+x+x2",
        "ell": 15, "m": 12,
        "A": [(3, 0), (0, 2), (0, 7)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "d_ub": 42, "expected_fom": 39.2,
    },
    {
        "name": "[[360,8,d<=40]] A=x3+y+y2 B=y6+x4+x5",
        "ell": 15, "m": 12,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 6), (4, 0), (5, 0)],
        "d_ub": 40, "expected_fom": 35.6,
    },
    {
        "name": "[[360,8,d<=36]] A=x5+y2+y3 B=y+x3+x11",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 2), (0, 3)],
        "B": [(0, 1), (3, 0), (11, 0)],
        "d_ub": 36, "expected_fom": 28.8,
    },
    {
        "name": "[[360,8,d<=36]] A=y+y3+x5 B=y6+x+x4",
        "ell": 15, "m": 12,
        "A": [(0, 1), (0, 3), (5, 0)],
        "B": [(0, 6), (1, 0), (4, 0)],
        "d_ub": 36, "expected_fom": 28.8,
    },
    {
        "name": "[[360,8,d<=32]] A=x5+y3+y5 B=y2+x2+x4",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 3), (0, 5)],
        "B": [(0, 2), (2, 0), (4, 0)],
        "d_ub": 32, "expected_fom": 22.8,
    },
    {
        "name": "[[360,8,d<=32]] A=x5+y2+y9 B=y+x3+x12",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 2), (0, 9)],
        "B": [(0, 1), (3, 0), (12, 0)],
        "d_ub": 32, "expected_fom": 22.8,
    },
    {
        "name": "[[360,8,d<=30]] mixed A=x5+y2+y7 B=y3+x+x3y",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 2), (0, 7)],
        "B": [(0, 3), (1, 0), (3, 1)],
        "d_ub": 30, "expected_fom": 20.0,
    },
    {
        "name": "[[360,8,d<=28]] A=x3+y4+y5 B=y3+x4+x5",
        "ell": 15, "m": 12,
        "A": [(3, 0), (0, 4), (0, 5)],
        "B": [(0, 3), (4, 0), (5, 0)],
        "d_ub": 28, "expected_fom": 17.4,
    },
    {
        "name": "[[360,8,d<=28]] A=x3+y+y2 B=y6+x+x2",
        "ell": 15, "m": 12,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 6), (1, 0), (2, 0)],
        "d_ub": 28, "expected_fom": 17.4,
    },
    {
        "name": "[[360,8,d<=28]] A=x10+y6+y11 B=y2+x+x2",
        "ell": 15, "m": 12,
        "A": [(10, 0), (0, 6), (0, 11)],
        "B": [(0, 2), (1, 0), (2, 0)],
        "d_ub": 28, "expected_fom": 17.4,
    },
    {
        "name": "[[360,8,d<=26]] A=x5+y+y3 B=y4+x2+x4",
        "ell": 15, "m": 12,
        "A": [(5, 0), (0, 1), (0, 3)],
        "B": [(0, 4), (2, 0), (4, 0)],
        "d_ub": 26, "expected_fom": 15.0,
    },
    # --- k=12 codes at (30,6) -- potentially high-value ---
    {
        "name": "[[360,12,d<=20]] A=x3+y+y2 B=y3+x4+x5",
        "ell": 30, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (4, 0), (5, 0)],
        "d_ub": 20, "expected_fom": 13.3,
    },
    {
        "name": "[[360,12,d<=20]] A=x3+y+y2 B=y3+x11+x16",
        "ell": 30, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (11, 0), (16, 0)],
        "d_ub": 20, "expected_fom": 13.3,
    },
    {
        "name": "[[360,12,d<=18]] mixed A=x9+x3y+y2 B=y3+x25+x26",
        "ell": 30, "m": 6,
        "A": [(9, 0), (3, 1), (0, 2)],
        "B": [(0, 3), (25, 0), (26, 0)],
        "d_ub": 18, "expected_fom": 10.8,
    },
    # --- k=8 codes at (30,6) -- different lattice ---
    {
        "name": "[[360,8,d<=24]] A=x3+y+y2 B=y2+x12+x16",
        "ell": 30, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 2), (12, 0), (16, 0)],
        "d_ub": 24, "expected_fom": 12.8,
    },
    {
        "name": "[[360,8,d<=24]] A=x3+y+y2 B=y+x14+x15",
        "ell": 30, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 1), (14, 0), (15, 0)],
        "d_ub": 24, "expected_fom": 12.8,
    },
    # --- k=12 at (12,12) -- novel non-Bravyi [[288,12]] codes ---
    {
        "name": "[[288,12,d<=16]] mixed A=x3+y2+xy9 B=y3+x+x2",
        "ell": 12, "m": 12,
        "A": [(3, 0), (0, 2), (1, 9)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "d_ub": 16, "expected_fom": 10.7,
    },
    {
        "name": "[[288,12,d<=16]] mixed A=x3+x2+y7 B=y3+x3y+x2",
        "ell": 12, "m": 12,
        "A": [(3, 0), (2, 0), (0, 7)],
        "B": [(0, 3), (3, 1), (2, 0)],
        "d_ub": 16, "expected_fom": 10.7,
    },
    {
        "name": "[[288,12,d<=16]] A=x3+y+y2 B=y3+x4+x5",
        "ell": 24, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (4, 0), (5, 0)],
        "d_ub": 16, "expected_fom": 10.7,
    },
    {
        "name": "[[288,8,d<=18]] A=x3+y+x22 B=y3+x+x2",
        "ell": 24, "m": 6,
        "A": [(3, 0), (0, 1), (22, 0)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "d_ub": 18, "expected_fom": 9.0,
    },
    {
        "name": "[[288,8,d<=18]] mixed A=x1y1+y+y2 B=y3+x4+x23",
        "ell": 24, "m": 6,
        "A": [(1, 1), (0, 1), (0, 2)],
        "B": [(0, 3), (4, 0), (23, 0)],
        "d_ub": 18, "expected_fom": 9.0,
    },
    {
        "name": "[[288,8,d<=16]] A=x+y2+y3 B=y3+x2+x7",
        "ell": 12, "m": 12,
        "A": [(1, 0), (0, 2), (0, 3)],
        "B": [(0, 3), (2, 0), (7, 0)],
        "d_ub": 16, "expected_fom": 7.1,
    },
    {
        "name": "[[288,16,d<=12]] mixed A=x6+y+x22y B=y3+x2+x6y",
        "ell": 24, "m": 6,
        "A": [(6, 0), (0, 1), (22, 1)],
        "B": [(0, 3), (2, 0), (6, 1)],
        "d_ub": 12, "expected_fom": 8.0,
    },
]


def verify_code(spec, timeout_per_logical=300, total_timeout=7200):
    """Run MILP verification on a single code."""
    ell, m = spec["ell"], spec["m"]
    A, B = spec["A"], spec["B"]

    print(f"\n{'='*60}")
    print(f"  {spec['name']}")
    print(f"  ({ell},{m}) A={A} B={B}")
    print(f"  Evolution bound: d <= {spec['d_ub']}")
    print(f"  Budget: {timeout_per_logical}s/logical, {total_timeout}s total")
    print(f"{'='*60}")

    code = build_bb_code(ell, m, A, B)
    n, k = get_code_params_fast(code)
    print(f"  n={n}, k={k}")

    if k == 0:
        print("  k=0 -- skip")
        return {"n": n, "k": 0, "d": n, "fom": 0, "exact": True}

    t0 = time.perf_counter()
    d, details = compute_distance_milp(
        code,
        timeout_per_logical=timeout_per_logical,
        total_timeout=total_timeout,
        early_stop=2,
        verbose=True,
    )
    elapsed = time.perf_counter() - t0

    fom = k * d * d / n if n > 0 else 0
    exact_str = "EXACT" if details.get("exact") else f"d<={d}"
    opt = details.get("logicals_optimal", "?")
    inc = details.get("logicals_incumbent", "?")
    total_log = details.get("total_logicals", "?")

    print(f"\n  RESULT: [[{n},{k},{d}]] FOM={fom:.1f} ({exact_str})")
    print(f"  d_X={details.get('d_x','?')} d_Z={details.get('d_z','?')}")
    print(f"  Logicals: {opt} optimal + {inc} incumbent / {total_log} total")
    print(f"  Time: {elapsed:.0f}s")

    if d < spec["d_ub"]:
        print(f"  >>> TIGHTER: d dropped from <={spec['d_ub']} to {'=' if details.get('exact') else '<='}{d}")
    elif d == spec["d_ub"] and details.get("exact"):
        print(f"  >>> CONFIRMED EXACT: d = {d}")
    else:
        print(f"  >>> Same bound: d <= {d}")

    return {
        "ell": ell, "m": m, "n": n, "k": k, "d": d,
        "fom": fom, "exact": details.get("exact", False),
        "d_x": details.get("d_x"), "d_z": details.get("d_z"),
        "logicals_optimal": opt,
        "logicals_incumbent": inc,
        "total_logicals": total_log,
        "time_s": elapsed,
        "A_terms": A, "B_terms": B,
        "d_ub_evolution": spec["d_ub"],
    }


def _verify_worker(args):
    """Worker for parallel verification (must be top-level for pickling)."""
    idx, spec, timeout_per_logical, total_timeout = args
    r = verify_code(spec, timeout_per_logical, total_timeout)
    r["_idx"] = idx
    return r


def main():
    import os
    from concurrent.futures import ProcessPoolExecutor, as_completed

    quick = "--quick" in sys.argv
    timeout_per_logical = 60 if quick else 300
    total_timeout = 1800 if quick else 7200

    max_workers = min(len(CODES_TO_VERIFY), max(1, os.cpu_count() - 5))

    mode = "QUICK (60s/logical)" if quick else "FULL (300s/logical)"
    print(f"Campaign 5 Novel Incumbent Verification -- {mode}")
    print(f"{len(CODES_TO_VERIFY)} codes to verify, {max_workers} parallel workers")
    sys.stdout.flush()

    worker_args = [
        (i, spec, timeout_per_logical, total_timeout)
        for i, spec in enumerate(CODES_TO_VERIFY)
    ]

    results = [None] * len(CODES_TO_VERIFY)
    with ProcessPoolExecutor(max_workers=max_workers) as pool:
        futures = {pool.submit(_verify_worker, args): args[0] for args in worker_args}
        for future in as_completed(futures):
            r = future.result()
            idx = r.pop("_idx")
            results[idx] = r
            spec = CODES_TO_VERIFY[idx]
            exact_str = "exact" if r["exact"] else f"d<={r['d']}"
            print(f"\n  DONE [{idx+1}/{len(CODES_TO_VERIFY)}]: "
                  f"[[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f} ({exact_str}) "
                  f"[{r['time_s']:.0f}s]")
            sys.stdout.flush()

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    for spec, r in zip(CODES_TO_VERIFY, results):
        exact_str = "exact" if r["exact"] else f"d<={r['d']}"
        delta = ""
        if r["d"] < spec["d_ub"]:
            delta = f" (was d<={spec['d_ub']})"
        elif r["d"] == spec["d_ub"] and r["exact"]:
            delta = " CONFIRMED"
        print(f"  [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f} ({exact_str}){delta}  [{r['time_s']:.0f}s]")

    # Codes that beat FOM=12.0 after verification
    beats_baseline = [r for r in results if r["fom"] > 12.0]
    if beats_baseline:
        print(f"\n  *** {len(beats_baseline)} codes beat FOM=12.0 baseline! ***")
        for r in sorted(beats_baseline, key=lambda x: -x["fom"]):
            exact_str = "exact" if r["exact"] else f"d<={r['d']}"
            print(f"    [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f} ({exact_str})")
    else:
        print(f"\n  No codes beat FOM=12.0 baseline after verification.")

    # Save results
    import json
    out_path = Path(__file__).parent.parent / "results" / "campaign5_novel_verification.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out_path}")


if __name__ == "__main__":
    main()
