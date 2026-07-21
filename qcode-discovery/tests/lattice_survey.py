"""Survey which lattices (ℓ, m) produce high-FOM BB codes.

What this produces
------------------
For each lattice in a fixed list, exhaustively k-screens the x/y-swap
trinomial family (A = x^a + y^b + y^c, B = y^d + x^e + x^f -- i.e., A
has one x-monomial and two y-monomials, B vice versa); picks the top-k
candidates by k; then runs a quick MILP probe on the best ~5 to
estimate the maximum achievable d at that lattice.  Output is a per-
lattice summary used by Sec.~VI of the paper to motivate the choice
of headline lattices.

Why x/y-swap specifically (and not the evolved seed function)
-------------------------------------------------------------
The x/y-swap subfamily is the only weight-3 trinomial family known
*a priori* to admit d >= 6 codes (Sec.~III.~A of the paper).  Using
``enumerate_xy_swap`` here gives a deterministic exhaustive sweep over
that family -- it is *not* the LLM-evolved candidate generator from
``evolve/seed_solution.py``.  The point is to map out lattices where
this structurally-favoured family is rich; broader exploration
(constant-monomial, mixed-monomial, etc.) is handled by the
evolutionary campaigns.

Usage:
    uv run python tests/lattice_survey.py
    uv run python tests/lattice_survey.py --deep    # longer MILP budgets
"""

import sys
import time
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.distance_milp import compute_distance_milp
from evaluation.evaluator import evaluate_batch_milp_parallel


def enumerate_xy_swap(ell, m):
    """Generate all x/y-swap trinomial pairs."""
    candidates = []
    for a in range(1, ell):
        for b in range(0, m):
            for c in range(b + 1, m):
                A = [(a, 0), (0, b), (0, c)]
                if len(set(A)) != 3 or (0, 0) in A:
                    continue
                for d in range(1, m):
                    for e in range(1, ell):
                        for f in range(e + 1, ell):
                            B = [(0, d), (e, 0), (f, 0)]
                            if len(set(B)) != 3 or (0, 0) in B:
                                continue
                            if sorted(A) == sorted(B):
                                continue
                            candidates.append((A, B))
    return candidates


def milp_probe(ell, m, A, B, timeout_per_logical=60, total_timeout=300):
    """Quick MILP distance probe on a single code."""
    code = build_bb_code(ell, m, A, B)
    n, k = get_code_params_fast(code)
    d, det = compute_distance_milp(
        code,
        timeout_per_logical=timeout_per_logical,
        total_timeout=total_timeout,
        early_stop=2,
        verbose=False,
    )
    return {
        "n": n, "k": k, "d": d,
        "fom": k * d * d / n if d > 0 else 0,
        "exact": det.get("exact", False),
        "logicals_optimal": det.get("logicals_optimal", 0),
        "total_logicals": det.get("total_logicals", 0),
        "A": A, "B": B,
    }


def main():
    deep = "--deep" in sys.argv
    timeout_per_logical = 120 if deep else 30
    total_timeout = 600 if deep else 120

    # Generate candidate lattices: n = 100..800
    lattices = set()
    for ell in range(3, 61):
        for m_val in range(3, min(ell + 1, 31)):
            n = 2 * ell * m_val
            if 100 <= n <= 800:
                lattices.add((ell, m_val))

    lattices = sorted(lattices, key=lambda x: 2 * x[0] * x[1])
    mode = "DEEP" if deep else "QUICK"
    print(f"Lattice Survey -- {mode} mode ({timeout_per_logical}s/logical, {total_timeout}s total)")
    print(f"{len(lattices)} lattices to probe")
    print(f"{'lattice':>10s} {'n':>5s} {'cands':>7s} {'k>0':>5s} {'max_k':>5s} "
          f"{'d':>4s} {'FOM':>6s} {'exact':>6s}  best code")
    print("-" * 100)
    sys.stdout.flush()

    all_results = []
    t_start = time.perf_counter()

    for ell, m_val in lattices:
        n = 2 * ell * m_val
        t0 = time.perf_counter()

        # Phase 1: Enumerate x/y-swap trinomials
        candidates = enumerate_xy_swap(ell, m_val)
        if not candidates:
            continue

        # Phase 2: Parallel k-screening
        tasks = [(ell, m_val, A, B) for A, B in candidates]
        try:
            results = evaluate_batch_milp_parallel(tasks, quick=True, max_workers=10)
        except Exception as e:
            print(f"({ell:2d},{m_val:2d})  {n:5d}  ERROR: {e}")
            sys.stdout.flush()
            continue

        # Filter k > 0
        codes_with_k = [r for r in results if r.get("k", 0) > 0]
        t_screen = time.perf_counter() - t0

        if not codes_with_k:
            if len(candidates) > 1000:
                print(f"({ell:2d},{m_val:2d})  {n:5d}  {len(candidates):7d}     0")
                sys.stdout.flush()
            continue

        max_k = max(r["k"] for r in codes_with_k)

        # Phase 3: MILP probe on top 5 codes (one per distinct k value)
        codes_with_k.sort(key=lambda r: -r["k"])
        seen_k = set()
        to_probe = []
        for r in codes_with_k:
            if r["k"] not in seen_k and len(to_probe) < 5:
                to_probe.append(r)
                seen_k.add(r["k"])

        best_fom = 0
        best_result = None
        for r in to_probe:
            try:
                probe = milp_probe(ell, m_val, r["A_terms"], r["B_terms"],
                                   timeout_per_logical, total_timeout)
                if probe["fom"] > best_fom:
                    best_fom = probe["fom"]
                    best_result = probe
            except Exception:
                pass

        t_total = time.perf_counter() - t0

        if best_result:
            exact_str = "exact" if best_result["exact"] else f"d<={best_result['d']}"
            marker = " ***" if best_fom >= 8.0 else " **" if best_fom >= 4.0 else ""
            print(f"({ell:2d},{m_val:2d})  {n:5d}  {len(candidates):7d} {len(codes_with_k):5d} "
                  f"k={max_k:3d}  d={best_result['d']:3d} {best_fom:6.1f} "
                  f"{exact_str:>8s}  A={best_result['A']} B={best_result['B']}"
                  f"{marker}  [{t_total:.0f}s]")
            all_results.append({
                "ell": ell, "m": m_val, "n": n,
                "total_candidates": len(candidates),
                "codes_with_k_gt_0": len(codes_with_k),
                "max_k": max_k,
                "best_fom": best_fom,
                "best_d": best_result["d"],
                "best_k": best_result["k"],
                "best_exact": best_result["exact"],
                "best_A": best_result["A"],
                "best_B": best_result["B"],
                "screen_time_s": t_screen,
                "total_time_s": t_total,
            })
        else:
            print(f"({ell:2d},{m_val:2d})  {n:5d}  {len(candidates):7d} {len(codes_with_k):5d} "
                  f"k={max_k:3d}  MILP failed  [{t_total:.0f}s]")

        sys.stdout.flush()

    # Summary
    elapsed = time.perf_counter() - t_start
    print(f"\n{'=' * 100}")
    print(f"SUMMARY -- {len(all_results)} productive lattices found in {elapsed:.0f}s ({elapsed/60:.1f}min)")
    print(f"{'=' * 100}")

    # Sort by FOM
    all_results.sort(key=lambda r: -r["best_fom"])
    print(f"\nTop lattices by FOM:")
    for r in all_results[:30]:
        exact_str = "exact" if r["best_exact"] else f"d<={r['best_d']}"
        print(f"  ({r['ell']:2d},{r['m']:2d}) n={r['n']:4d}: "
              f"[[{r['n']},{r['best_k']},{r['best_d']}]] "
              f"FOM={r['best_fom']:.1f} ({exact_str}) "
              f"max_k={r['max_k']} cands={r['total_candidates']}")

    # Save
    out_path = Path(__file__).parent.parent / "results" / "lattice_survey.json"
    output = {
        "mode": mode,
        "timeout_per_logical": timeout_per_logical,
        "total_timeout": total_timeout,
        "total_lattices": len(lattices),
        "productive_lattices": len(all_results),
        "elapsed_s": elapsed,
        "results": all_results,
    }
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {out_path}")


if __name__ == "__main__":
    main()
