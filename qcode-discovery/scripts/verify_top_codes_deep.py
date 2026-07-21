"""Deep verification of top Campaign 7c codes.

Three approaches to increase confidence:
1. osd_0 with massive trials (20000 × 10 seeds) -- brute force coverage
2. osd_e (exhaustive OSD) order 7 -- systematically searches low-weight space
3. qldpc exact distance with timeout -- ground truth if it terminates
"""

import sys
import time
import multiprocessing
sys.path.insert(0, "/root/qcode-discovery")

from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast
from evaluation.distance_bposd_noncss import estimate_distance_noncss

CODES = [
    # Star code: [[72,40,≤12]] -- fully trusted, highest credible FOM
    {
        "name": "[[72,40,≤12]] Code6v2",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (0, 5)], "D": [(1, 2), (3, 1), (5, 3)],
    },
    # Second [[72,40]] variant
    {
        "name": "[[72,40,≤10]] Code5",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (2, 4), (4, 0)], "D": [(1, 2), (1, 5)],
    },
    # [[72,38,≤10]]
    {
        "name": "[[72,38,≤10]] Code8",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 4), (3, 1)], "D": [(1, 1), (4, 4)],
    },
    # High-d candidate: [[72,13,≤23]] -- untrusted but interesting
    {
        "name": "[[72,13,≤23]] Code1",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 0), (4, 0)], "B": [(1, 0), (0, 1), (0, 2)],
        "C": [(4, 0)], "D": [(0, 5), (4, 2)],
    },
]


def run_osd0_massive(code_info):
    """Phase 1: osd_0 with 20000 trials × 10 seeds."""
    print(f"\n  Phase 1: osd_0, 20000 trials × 10 seeds")
    code = build_pbb_code(code_info["ell"], code_info["m"],
                          code_info["A"], code_info["B"],
                          code_info["C"], code_info["D"])
    seeds = [42, 137, 2024, 7777, 31415, 99991, 54321, 11111, 77777, 33333]
    results = []
    for seed in seeds:
        t0 = time.time()
        d = estimate_distance_noncss(code, num_trials=20000, seed=seed)
        elapsed = time.time() - t0
        results.append(d)
        print(f"    seed={seed:5d}: d≤{d:2d}  ({elapsed:.1f}s)")
        sys.stdout.flush()
    d_min = min(results)
    d_max = max(results)
    print(f"    >>> osd_0: d∈[{d_min},{d_max}]")
    return d_min, d_max, results


def run_osde_thorough(code_info):
    """Phase 2: osd_e order 7 with 2000 trials × 5 seeds."""
    print(f"\n  Phase 2: osd_e order 7, 2000 trials × 5 seeds")
    code = build_pbb_code(code_info["ell"], code_info["m"],
                          code_info["A"], code_info["B"],
                          code_info["C"], code_info["D"])
    seeds = [42, 137, 2024, 7777, 31415]
    results = []
    for seed in seeds:
        t0 = time.time()
        d = estimate_distance_noncss(code, num_trials=2000, seed=seed,
                                     osd_method="osd_e", osd_order=7)
        elapsed = time.time() - t0
        results.append(d)
        print(f"    seed={seed:5d}: d≤{d:2d}  ({elapsed:.1f}s)")
        sys.stdout.flush()
    d_min = min(results)
    d_max = max(results)
    print(f"    >>> osd_e(7): d∈[{d_min},{d_max}]")
    return d_min, d_max, results


def _exact_worker(args, result_queue):
    """Worker for exact distance computation."""
    ell, m, A, B, C, D = args
    try:
        from evaluation.pbb_code import build_pbb_code
        code = build_pbb_code(ell, m, A, B, C, D)
        d = code.get_distance_exact()
        result_queue.put(("exact", int(d)))
    except Exception as e:
        result_queue.put(("error", str(e)))


def run_exact(code_info, timeout=300):
    """Phase 3: Exact distance with timeout."""
    print(f"\n  Phase 3: Exact distance (timeout={timeout}s)")
    sys.stdout.flush()

    args = (code_info["ell"], code_info["m"],
            code_info["A"], code_info["B"],
            code_info["C"], code_info["D"])
    queue = multiprocessing.Queue()
    proc = multiprocessing.Process(target=_exact_worker, args=(args, queue))
    t0 = time.time()
    proc.start()
    proc.join(timeout=timeout)

    if proc.is_alive():
        proc.terminate()
        proc.join(timeout=5)
        if proc.is_alive():
            proc.kill()
            proc.join()
        elapsed = time.time() - t0
        print(f"    >>> TIMEOUT after {elapsed:.0f}s")
        return None

    elapsed = time.time() - t0
    if not queue.empty():
        status, value = queue.get()
        if status == "exact":
            print(f"    >>> EXACT d={value}  ({elapsed:.1f}s)")
            return value
        else:
            print(f"    >>> ERROR: {value}  ({elapsed:.1f}s)")
            return None
    print(f"    >>> No result ({elapsed:.1f}s)")
    return None


if __name__ == "__main__":
    print(f"Deep verification of {len(CODES)} codes")
    print(f"=" * 70)

    summaries = []

    for code_info in CODES:
        code = build_pbb_code(code_info["ell"], code_info["m"],
                              code_info["A"], code_info["B"],
                              code_info["C"], code_info["D"])
        n, k = get_pbb_params_fast(code)

        print(f"\n{'='*70}")
        print(f"{code_info['name']}  n={n} k={k}")
        print(f"  A={code_info['A']}  B={code_info['B']}")
        print(f"  C={code_info['C']}  D={code_info['D']}")

        # Phase 1: Massive osd_0
        d_min_0, d_max_0, all_d_0 = run_osd0_massive(code_info)

        # Phase 2: osd_e exhaustive
        d_min_e, d_max_e, all_d_e = run_osde_thorough(code_info)

        # Phase 3: Exact (with short timeout for large codes)
        timeout = 120 if k <= 15 else 60  # shorter timeout for high-k codes
        d_exact = run_exact(code_info, timeout=timeout)

        # Combined result
        d_verified = min(d_min_0, d_min_e)
        if d_exact is not None:
            d_verified = d_exact  # ground truth overrides

        fom = k * d_verified * d_verified / n
        ratio = d_verified / n**0.5
        trust = "EXACT" if d_exact is not None else \
                "TRUSTED" if ratio < 1.5 else \
                "PARTIAL" if ratio < 2.5 else "UNTRUSTED"

        summary = {
            "name": code_info["name"], "n": n, "k": k,
            "d_osd0": f"[{d_min_0},{d_max_0}]",
            "d_osde": f"[{d_min_e},{d_max_e}]",
            "d_exact": d_exact,
            "d_verified": d_verified,
            "fom": fom, "trust": trust,
        }
        summaries.append(summary)
        print(f"\n  COMBINED: d≤{d_verified}  FOM={fom:.1f}  {trust}")
        sys.stdout.flush()

    # Final summary
    print(f"\n{'='*70}")
    print("FINAL SUMMARY")
    print(f"{'='*70}")
    summaries.sort(key=lambda x: x["fom"], reverse=True)
    for s in summaries:
        exact_str = f"  exact={s['d_exact']}" if s['d_exact'] is not None else ""
        print(f"  {s['name']:30s}  d≤{s['d_verified']:2d}  FOM={s['fom']:6.1f}  "
              f"osd0={s['d_osd0']}  osd_e={s['d_osde']}{exact_str}  [{s['trust']}]")
