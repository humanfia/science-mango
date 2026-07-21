"""Verify top Campaign 7c codes with high trial counts across multiple seeds."""

import sys
import time
sys.path.insert(0, "/root/qcode-discovery")

from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast
from evaluation.distance_bposd_noncss import estimate_distance_noncss

CODES_TO_VERIFY = [
    # Code 1: [[72,13,≤29]] FOM=151.8 -- Base 5 family (suspicious high d)
    {
        "name": "Code1 [[72,13,≤29]]",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 0), (4, 0)], "B": [(1, 0), (0, 1), (0, 2)],
        "C": [(4, 0)], "D": [(0, 5), (4, 2)],
    },
    # Code 2: [[72,13,≤29]] transpose variant
    {
        "name": "Code2 [[72,13,≤29]]t",
        "ell": 6, "m": 6,
        "A": [(1, 0), (0, 2), (0, 4)], "B": [(0, 1), (1, 0), (2, 0)],
        "C": [(3, 4)], "D": [(2, 0), (5, 4)],
    },
    # Code 3: [[72,13,≤26]] FOM=122.1
    {
        "name": "Code3 [[72,13,≤26]]",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 0), (4, 0)], "B": [(1, 0), (0, 1), (0, 2)],
        "C": [(4, 3)], "D": [(0, 2), (4, 5)],
    },
    # Code 4: [[72,10,≤28]] FOM=108.9
    {
        "name": "Code4 [[72,10,≤28]]",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 0), (4, 0)], "B": [(1, 0), (0, 1), (0, 2)],
        "C": [(0, 1), (0, 2)], "D": [(1, 2), (3, 5)],
    },
    # Code 5: [[72,40,≤14]] FOM=108.9 -- Base 6, high-k (most credible)
    {
        "name": "Code5 [[72,40,≤14]]",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (2, 4), (4, 0)], "D": [(1, 2), (1, 5)],
    },
    # Code 6: [[72,40,≤14]] variant
    {
        "name": "Code6 [[72,40,≤14]]v2",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (0, 5)], "D": [(1, 2), (3, 1), (5, 3)],
    },
    # Code 8: [[72,38,≤14]] FOM=103.4
    {
        "name": "Code8 [[72,38,≤14]]",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 4), (3, 1)], "D": [(1, 1), (4, 4)],
    },
    # Code 10: [[72,10,≤27]] minimal C,D
    {
        "name": "Code10 [[72,10,≤27]]",
        "ell": 6, "m": 6,
        "A": [(1, 0), (0, 2), (0, 4)], "B": [(0, 1), (1, 0), (2, 0)],
        "C": [(1, 1)], "D": [(0, 0), (0, 1)],
    },
    # Code 12: [[72,12,≤24]] FOM=96.0
    {
        "name": "Code12 [[72,12,≤24]]",
        "ell": 6, "m": 6,
        "A": [(1, 0), (0, 2), (0, 4)], "B": [(0, 1), (1, 0), (2, 0)],
        "C": [(4, 5), (5, 3)], "D": [(2, 0), (4, 0), (4, 5), (5, 4)],
    },
    # Also verify a known good code as sanity check
    {
        "name": "Sanity [[72,20,≤10]]",
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)], "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(0, 5), (1, 0)], "D": [(0, 0), (1, 0), (4, 0), (5, 5)],
    },
]

SEEDS = [42, 137, 2024, 7777, 31415]
TRIALS_PER_SEED = 5000


def verify_code(code_info):
    ell, m = code_info["ell"], code_info["m"]
    code = build_pbb_code(ell, m, code_info["A"], code_info["B"],
                          code_info["C"], code_info["D"])
    n, k = get_pbb_params_fast(code)

    print(f"\n{'='*60}")
    print(f"{code_info['name']}  n={n} k={k}")
    print(f"  A={code_info['A']}  B={code_info['B']}")
    print(f"  C={code_info['C']}  D={code_info['D']}")

    d_results = []
    for seed in SEEDS:
        t0 = time.time()
        d = estimate_distance_noncss(code, num_trials=TRIALS_PER_SEED, seed=seed)
        elapsed = time.time() - t0
        d_results.append(d)
        fom = k * d * d / n if d > 0 and n > 0 else 0
        print(f"  seed={seed:5d}: d≤{d:2d}  FOM={fom:6.1f}  ({elapsed:.1f}s)")

    d_best = min(d_results)
    d_worst = max(d_results)
    fom_best = k * d_best * d_best / n
    print(f"  >>> VERIFIED: d∈[{d_best},{d_worst}]  best FOM={fom_best:.1f}  "
          f"ratio d/√n={d_best/n**0.5:.2f}")
    return {"name": code_info["name"], "n": n, "k": k,
            "d_min": d_best, "d_max": d_worst, "fom": fom_best,
            "all_d": d_results}


if __name__ == "__main__":
    print(f"Verifying {len(CODES_TO_VERIFY)} codes with {TRIALS_PER_SEED} trials × {len(SEEDS)} seeds")
    results = []
    for code_info in CODES_TO_VERIFY:
        r = verify_code(code_info)
        results.append(r)
        sys.stdout.flush()

    print(f"\n{'='*60}")
    print("SUMMARY (sorted by verified FOM):")
    print(f"{'='*60}")
    results.sort(key=lambda x: x["fom"], reverse=True)
    for r in results:
        trust = "TRUSTED" if r["d_min"] / r["n"]**0.5 < 1.5 else \
                "PARTIAL" if r["d_min"] / r["n"]**0.5 < 2.5 else "UNTRUSTED"
        print(f"  {r['name']:30s}  [[{r['n']},{r['k']},≤{r['d_min']}]]  "
              f"FOM={r['fom']:6.1f}  d∈[{r['d_min']},{r['d_max']}]  {trust}")
