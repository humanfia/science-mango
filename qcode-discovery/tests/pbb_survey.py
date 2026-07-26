#!/usr/bin/env python3
"""Exhaustive small-lattice survey for perturbed bivariate bicycle (PBB) codes.

What this produces
------------------
For a fixed lattice (ℓ, m), enumerates the trinomial CSS BB codes with
k > 0 ("base" codes), then for each base code performs a high-throughput
random search over multi-term perturbation polynomials (C, D) that
augment the CSS stabilizer group into a non-CSS PBB stabilizer group
satisfying the commutativity constraint (A C^T + B D^T symmetric).
Surviving PBB codes are distance-computed via symplectic MILP.  Output
is JSON-per-lattice under ``results/ptb_survey_<lattice>.json``.

Why a separate script (vs the evolutionary search)
--------------------------------------------------
The base CSS codes here come from ``find_css_base_codes_fast``, a quick
trinomial enumerator (NOT the evolved seed function in
``evolve/seed_solution.py``); for each base, (C, D) is sampled randomly
under the commutativity constraint.  The evolutionary search in
``evolve/`` instead works directly on whole 4-tuples (A, B, C, D) using
LLM-driven mutations.  This script's exhaustive base + random
perturbation sweep is a useful complement at small lattices where the
base-code space is tiny and random (C, D) sampling is competitive.

What the surveys are used for
-----------------------------
The survey JSON feeds the catalog deduplication and BLISS equivalence
analysis that produces the paper's PBB tables; specific survey runs at
(6, 6) are post-processed by ``tests/pbb_survey_milp_66.py``.

Usage:
    # Survey at (6,3) with 100k trials per base code
    uv run python tests/pbb_survey.py --lattice 6,3 --trials 100000

    # Survey at (6,6) with 500k trials
    uv run python tests/pbb_survey.py --lattice 6,6 --trials 500000

    # Quick test run
    uv run python tests/pbb_survey.py --lattice 6,3 --trials 1000 --skip-milp
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict
from itertools import combinations
from pathlib import Path

# Ensure project root is on path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np

from evaluation.bb_code import build_bb_code, get_code_params_fast, terms_to_poly
from evaluation.pbb_code import (
    build_pbb_code,
    check_commutativity,
    symplectic_weight_bound_pbb,
    _poly_to_matrix,
)
from evaluation.distance_milp import (
    compute_distance_milp,
    compute_distance_milp_symplectic,
)
from sympy.abc import x, y
from qldpc import codes


def find_css_base_codes(ell: int, m: int) -> list[dict]:
    """Find all trinomial BB codes with k>0 at given lattice."""
    all_monomials = [(i, j) for i in range(ell) for j in range(m)]
    found = []
    seen_params = set()

    for A_terms in combinations(all_monomials, 3):
        for B_terms in combinations(all_monomials, 3):
            try:
                bb = build_bb_code(ell, m, list(A_terms), list(B_terms))
                n, k = get_code_params_fast(bb)
                if k > 0:
                    key = (tuple(sorted(A_terms)), tuple(sorted(B_terms)))
                    if key not in seen_params:
                        seen_params.add(key)
                        found.append({
                            "A_terms": list(A_terms),
                            "B_terms": list(B_terms),
                            "n": n,
                            "k": k,
                        })
            except Exception:
                pass

    return found


def find_css_base_codes_fast(ell: int, m: int) -> list[dict]:
    """Find representative BB codes with distinct k values.

    Instead of exhaustive enumeration (slow for larger lattices),
    samples a large number of random trinomial pairs.
    """
    rng = np.random.default_rng(42)
    all_monomials = [(i, j) for i in range(ell) for j in range(m)]
    found = {}  # k -> best example

    num_trials = min(5000, len(all_monomials) ** 6)
    for _ in range(num_trials):
        A_idx = rng.choice(len(all_monomials), 3, replace=False)
        B_idx = rng.choice(len(all_monomials), 3, replace=False)
        A_terms = [all_monomials[i] for i in sorted(A_idx)]
        B_terms = [all_monomials[i] for i in sorted(B_idx)]

        try:
            bb = build_bb_code(ell, m, A_terms, B_terms)
            n, k = get_code_params_fast(bb)
            if k > 0 and k not in found:
                found[k] = {
                    "A_terms": A_terms,
                    "B_terms": B_terms,
                    "n": n,
                    "k": k,
                }
        except Exception:
            pass

    return sorted(found.values(), key=lambda x: x["k"])


def random_multi_term_poly(ell: int, m: int, rng: np.random.Generator,
                           min_terms: int = 1, max_terms: int = 6
                           ) -> list[tuple[int, int]]:
    """Generate a random polynomial with 1-6 terms."""
    num_terms = int(rng.integers(min_terms, max_terms + 1))
    all_monomials = [(i, j) for i in range(ell) for j in range(m)]
    idx = rng.choice(len(all_monomials), min(num_terms, len(all_monomials)),
                     replace=False)
    return [all_monomials[i] for i in sorted(idx)]


def run_survey(
    ell: int,
    m: int,
    num_trials: int,
    skip_milp: bool = False,
    milp_timeout_per_logical: int = 30,
    milp_total_timeout: int = 120,
    seed: int = 42,
    output_path: str | None = None,
    max_base_codes: int = 10,
) -> dict:
    """Run the PBB code survey at a given lattice."""
    import functools
    # ``_print`` flushes after every line so progress is visible when piping
    # to a log file during long sweeps (the default print buffers).
    _print = functools.partial(print, flush=True)

    _print(f"\n{'='*60}")
    _print(f"PBB Survey at ({ell},{m}), n={2*ell*m}")
    _print(f"Trials: {num_trials}, MILP: {'skip' if skip_milp else 'enabled'}")
    _print(f"{'='*60}\n")

    # Step 1: Find CSS base codes
    _print("Finding CSS base codes...")
    t0 = time.monotonic()
    base_codes = find_css_base_codes_fast(ell, m)

    # Deduplicate by k value -- keep one representative per k
    by_k = {}
    for bc in base_codes:
        k = bc["k"]
        if k not in by_k:
            by_k[k] = bc
    base_codes = sorted(by_k.values(), key=lambda x: x["k"], reverse=True)
    if max_base_codes and len(base_codes) > max_base_codes:
        base_codes = base_codes[:max_base_codes]

    _print(f"  Found {len(base_codes)} distinct-k CSS base codes "
          f"(k values: {[bc['k'] for bc in base_codes]})")

    # Step 2: Compute CSS distances for comparison
    css_results = {}
    if not skip_milp:
        _print("\nComputing CSS distances via MILP...")
        for bc in base_codes:
            bb = build_bb_code(ell, m, bc["A_terms"], bc["B_terms"])
            d, details = compute_distance_milp(
                bb,
                timeout_per_logical=milp_timeout_per_logical,
                total_timeout=milp_total_timeout,
                early_stop=2,
            )
            css_results[bc["k"]] = {
                "d": d,
                "exact": details.get("exact", False),
                "A_terms": bc["A_terms"],
                "B_terms": bc["B_terms"],
            }
            exact_tag = "" if details.get("exact") else " (upper bound)"
            _print(f"  CSS k={bc['k']}: d={d}{exact_tag}")

    # Step 3: Random (C, D) search
    _print(f"\nSearching for valid PBB codes ({num_trials} trials per base)...")
    rng = np.random.default_rng(seed)

    all_ptb_codes = []  # Collect all valid (A, B, C, D, k) tuples
    stats = defaultdict(lambda: {"trials": 0, "valid": 0, "k_dist": defaultdict(int)})

    for bi, bc in enumerate(base_codes):
        A_terms = bc["A_terms"]
        B_terms = bc["B_terms"]
        css_k = bc["k"]

        # Build base code for matrix extraction
        poly_a = terms_to_poly(A_terms)
        poly_b = terms_to_poly(B_terms)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)
        mat_A = _poly_to_matrix(bb, A_terms)
        mat_B = _poly_to_matrix(bb, B_terms)

        # Precompute all monomial matrices for fast (C, D) construction
        all_monomials = [(i, j) for i in range(ell) for j in range(m)]
        mono_matrices = {}
        for mono in all_monomials:
            mono_matrices[mono] = _poly_to_matrix(bb, [mono])

        def fast_poly_matrix(terms):
            """Build polynomial matrix by summing precomputed monomial matrices."""
            result = np.zeros_like(mat_A)
            for t in terms:
                result = (result + mono_matrices[t]) % 2
            return result

        valid_count = 0
        t_base = time.monotonic()

        for trial in range(num_trials):
            C_terms = random_multi_term_poly(ell, m, rng)
            D_terms = random_multi_term_poly(ell, m, rng)

            mat_C = fast_poly_matrix(C_terms)
            mat_D = fast_poly_matrix(D_terms)

            if not check_commutativity(mat_A, mat_B, mat_C, mat_D):
                continue

            try:
                # Build qubit stabilizer code directly from precomputed matrices (fast path)
                dim = ell * m
                zero = np.zeros((dim, dim), dtype=int)
                block1_x = np.hstack([mat_A, mat_B])
                block1_z = np.hstack([mat_C, mat_D])
                block2_x = np.hstack([zero, zero])
                block2_z = np.hstack([mat_B.T % 2, mat_A.T % 2])
                top = np.hstack([block1_x, block1_z])
                bottom = np.hstack([block2_x, block2_z])
                symplectic = np.vstack([top, bottom]) % 2
                from qldpc.codes import QuditCode
                code = QuditCode(symplectic)
                n = code.num_qudits
                k = code.dimension
            except Exception:
                continue

            valid_count += 1
            stats[css_k]["valid"] += 1
            stats[css_k]["k_dist"][k] += 1

            all_ptb_codes.append({
                "A_terms": A_terms,
                "B_terms": B_terms,
                "C_terms": C_terms,
                "D_terms": D_terms,
                "n": n,
                "k": k,
                "css_base_k": css_k,
            })

            if valid_count <= 3 or valid_count % 100 == 0:
                _print(f"  Base k={css_k}: {valid_count} valid "
                      f"({trial+1} trials, {valid_count/(trial+1)*100:.2f}%)")

        stats[css_k]["trials"] = num_trials
        elapsed_base = time.monotonic() - t_base
        rate = stats[css_k]["valid"] / num_trials * 100
        _print(f"  Base k={css_k}: {stats[css_k]['valid']}/{num_trials} valid "
              f"({rate:.2f}%) in {elapsed_base:.1f}s")
        k_dist = dict(stats[css_k]["k_dist"])
        _print(f"    k distribution: {dict(sorted(k_dist.items()))}")

    # Step 4: Deduplicate by (k, polynomial signature)
    _print(f"\nTotal valid PBB codes found: {len(all_ptb_codes)}")

    # Deduplicate: keep unique (k, sorted_C, sorted_D) per base
    seen = set()
    unique_codes = []
    for pc in all_ptb_codes:
        key = (pc["css_base_k"], pc["k"],
               tuple(sorted(pc["C_terms"])),
               tuple(sorted(pc["D_terms"])))
        if key not in seen:
            seen.add(key)
            unique_codes.append(pc)
    _print(f"Unique PBB codes: {len(unique_codes)}")

    # Step 5: MILP distance computation (two-pass: screen then verify)
    milp_results = []
    if not skip_milp and unique_codes:
        # --- Pass 1: Quick screening (5s) to identify d=2 vs d>2 ---
        _print(f"\nPass 1: Screening {len(unique_codes)} codes (5s MILP per code)...")
        screened = []
        d2_count = 0
        for ci, pc in enumerate(unique_codes):
            try:
                code = build_pbb_code(
                    ell, m,
                    pc["A_terms"], pc["B_terms"],
                    pc["C_terms"], pc["D_terms"],
                )
                ub = symplectic_weight_bound_pbb(code)
                d, details = compute_distance_milp_symplectic(
                    code,
                    timeout_per_logical=5,
                    total_timeout=5,
                    early_stop=2,
                )
                if d <= 2:
                    d2_count += 1
                else:
                    screened.append({**pc, "d_screen": d, "ub": ub})
            except Exception:
                pass

            if (ci + 1) % 100 == 0:
                _print(f"  Screened {ci+1}/{len(unique_codes)}: "
                      f"{d2_count} d<=2, {len(screened)} d>2")

        _print(f"  Screening done: {d2_count} d<=2, {len(screened)} d>2 "
              f"(of {len(unique_codes)} total)")

        # --- Pass 2: Full MILP on d>2 codes ---
        if screened:
            _print(f"\nPass 2: Full MILP on {len(screened)} codes "
                  f"({milp_timeout_per_logical}s/logical, "
                  f"{milp_total_timeout}s total)...")

            by_k = defaultdict(list)
            for pc in screened:
                by_k[pc["k"]].append(pc)

            for k_val in sorted(by_k.keys()):
                codes_at_k = by_k[k_val]
                _print(f"\n  k={k_val}: {len(codes_at_k)} codes (d>2)")
                best_d = 0
                best_code = None

                for ci, pc in enumerate(codes_at_k):
                    try:
                        code = build_pbb_code(
                            ell, m,
                            pc["A_terms"], pc["B_terms"],
                            pc["C_terms"], pc["D_terms"],
                        )

                        d, details = compute_distance_milp_symplectic(
                            code,
                            timeout_per_logical=milp_timeout_per_logical,
                            total_timeout=milp_total_timeout,
                            early_stop=2,
                        )

                        result = {**pc, "d": d, "ub": pc["ub"],
                                  "milp_details": details}
                        milp_results.append(result)

                        if d > best_d:
                            best_d = d
                            best_code = result

                        if ci < 3 or d >= 4:
                            exact_tag = "" if details.get("exact") else "≤"
                            _print(f"    [{ci+1}/{len(codes_at_k)}] "
                                  f"[[{pc['n']},{k_val},{exact_tag}{d}]] "
                                  f"FOM={k_val*d*d/pc['n']:.1f} "
                                  f"(ub={pc['ub']}, "
                                  f"{details.get('time_s', 0):.1f}s)")

                    except Exception as e:
                        _print(f"    [{ci+1}/{len(codes_at_k)}] ERROR: {e}")

                if best_code:
                    d = best_code["d"]
                    exact_tag = "" if best_code["milp_details"].get("exact") \
                        else "≤"
                    _print(f"  Best at k={k_val}: "
                          f"[[{best_code['n']},{k_val},{exact_tag}{d}]] "
                          f"FOM={k_val*d*d/best_code['n']:.1f}")

    # Step 6: Summary
    elapsed_total = time.monotonic() - t0
    _print(f"\n{'='*60}")
    _print(f"SURVEY SUMMARY -- ({ell},{m}), n={2*ell*m}")
    _print(f"{'='*60}")
    _print(f"Total time: {elapsed_total:.1f}s")
    _print(f"CSS base codes: {len(base_codes)}")
    total_valid = sum(s["valid"] for s in stats.values())
    total_trials = sum(s["trials"] for s in stats.values())
    _print(f"PBB codes found: {total_valid}/{total_trials} "
          f"({total_valid/max(total_trials,1)*100:.3f}%)")
    _print(f"Unique PBB codes: {len(unique_codes)}")

    # k values accessible
    css_k_values = set(bc["k"] for bc in base_codes)
    ptb_k_values = set(pc["k"] for pc in all_ptb_codes)
    new_k_values = ptb_k_values - css_k_values
    _print(f"\nCSS k values: {sorted(css_k_values)}")
    _print(f"PBB k values: {sorted(ptb_k_values)}")
    _print(f"NEW k values (non-CSS only): {sorted(new_k_values)}")

    if milp_results:
        _print(f"\nMILP-verified PBB codes: {len(milp_results)}")
        d4_plus = [r for r in milp_results if r["d"] >= 4]
        _print(f"  With d >= 4: {len(d4_plus)}")

        if d4_plus:
            _print("\n  Best codes with d >= 4:")
            d4_plus.sort(key=lambda r: r["k"] * r["d"]**2 / r["n"], reverse=True)
            for r in d4_plus[:10]:
                d = r["d"]
                exact_tag = "" if r["milp_details"].get("exact") else "≤"
                fom = r["k"] * d**2 / r["n"]
                _print(f"    [[{r['n']},{r['k']},{exact_tag}{d}]] "
                      f"FOM={fom:.1f} "
                      f"C={r['C_terms']} D={r['D_terms']}")

        # Pareto comparison
        _print("\n  CSS vs non-CSS Pareto front:")
        for k_val in sorted(set(r["k"] for r in milp_results)):
            codes_at_k = [r for r in milp_results if r["k"] == k_val]
            best_d = max(r["d"] for r in codes_at_k)
            css_d = css_results.get(k_val, {}).get("d", 0)
            marker = " ***NEW***" if k_val in new_k_values else ""
            css_info = f"CSS d={css_d}" if css_d else "no CSS"
            _print(f"    k={k_val}: best PBB d={best_d}, {css_info}{marker}")

    # Save results
    output = {
        "lattice": [ell, m],
        "n": 2 * ell * m,
        "num_trials_per_base": num_trials,
        "seed": seed,
        "css_base_codes": base_codes,
        "css_distances": {str(k): v for k, v in css_results.items()},
        "stats": {str(k): {"trials": v["trials"], "valid": v["valid"],
                            "k_dist": dict(v["k_dist"])}
                  for k, v in stats.items()},
        "ptb_k_values": sorted(ptb_k_values),
        "css_k_values": sorted(css_k_values),
        "new_k_values": sorted(new_k_values),
        "milp_results": [
            {k: v for k, v in r.items() if k != "milp_details"}
            for r in milp_results
        ] if milp_results else [],
        "total_time_s": elapsed_total,
    }

    if output_path is None:
        output_path = f"results/ptb_survey_{ell}x{m}.json"

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2, default=str)
    _print(f"\nResults saved to {output_path}")

    return output


def main():
    parser = argparse.ArgumentParser(description="PBB code survey")
    parser.add_argument("--lattice", required=True, help="Lattice as 'ell,m'")
    parser.add_argument("--trials", type=int, default=100000,
                        help="Number of random (C,D) trials per base code")
    parser.add_argument("--skip-milp", action="store_true",
                        help="Skip MILP distance computation (k-only survey)")
    parser.add_argument("--milp-timeout", type=int, default=30,
                        help="MILP timeout per logical operator (seconds)")
    parser.add_argument("--milp-total", type=int, default=120,
                        help="MILP total timeout per code (seconds)")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--output", type=str, default=None)
    parser.add_argument("--max-base", type=int, default=10,
                        help="Max number of CSS base codes to use")
    args = parser.parse_args()

    ell, m = map(int, args.lattice.split(","))
    run_survey(
        ell, m,
        num_trials=args.trials,
        skip_milp=args.skip_milp,
        milp_timeout_per_logical=args.milp_timeout,
        milp_total_timeout=args.milp_total,
        seed=args.seed,
        output_path=args.output,
        max_base_codes=args.max_base,
    )


if __name__ == "__main__":
    main()
