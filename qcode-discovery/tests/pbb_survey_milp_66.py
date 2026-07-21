#!/usr/bin/env python3
"""MILP verification of PBB codes found at (6,6) by ``tests/pbb_survey``.

What this produces
------------------
Reads the survey results from ``results/ptb_survey_6x6.json``
(produced by a ``--skip-milp`` run of ``tests/pbb_survey.py``) and runs
a two-pass MILP: a 5-second screen flagging codes with d <= 2, then a
full MILP pass on the remaining d > 2 codes.  Output is the
MILP-validated subset of (6, 6) PBB codes that go into the paper's
Table~II / supplemental PBB tables.

Why a separate script rather than ``pbb_survey.py --milp``
---------------------------------------------------------
The (6, 6) lattice is small enough that ``pbb_survey.py`` produces
many codes from random (C, D) sampling; running symplectic MILP inline
on every one is slow.  Splitting into a fast random sweep
(``--skip-milp``) followed by this verifier lets us iterate on the
sweep without redoing the MILP.

Usage:
    uv run python tests/pbb_survey_milp_66.py
    uv run python tests/pbb_survey_milp_66.py --timeout 60  # longer MILP
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import functools
import numpy as np
from qldpc.codes import QuditCode

from evaluation.pbb_code import (
    build_pbb_code,
    symplectic_weight_bound_pbb,
)
from evaluation.distance_milp import (
    compute_distance_milp,
    compute_distance_milp_symplectic,
)
from evaluation.bb_code import build_bb_code

# ``_print`` flushes after every line so progress is visible when piping
# to a log file during long MILP runs (the default print buffers).
_print = functools.partial(print, flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=30,
                        help="MILP timeout per logical (seconds)")
    parser.add_argument("--total-timeout", type=int, default=120,
                        help="MILP total timeout per code (seconds)")
    parser.add_argument("--screen-timeout", type=int, default=5,
                        help="Screening pass timeout (seconds)")
    parser.add_argument("--input", default="results/ptb_survey_6x6.json")
    parser.add_argument("--output", default="results/ptb_survey_6x6_milp.json")
    args = parser.parse_args()

    with open(args.input) as f:
        survey = json.load(f)

    ell, m = survey["lattice"]
    n = survey["n"]
    _print(f"\nMILP verification of PBB codes at ({ell},{m}), n={n}")

    # Reconstruct unique codes from the survey
    # The survey JSON doesn't store unique codes directly when skip-milp was used,
    # so we need to re-derive them from the stats
    # Actually, re-run the random search with the same seed to regenerate
    from evaluation.bb_code import terms_to_poly
    from evaluation.pbb_code import (
        check_commutativity, _poly_to_matrix,
    )
    from sympy.abc import x, y
    from qldpc import codes

    _print("Regenerating PBB codes from survey seed...")
    t0 = time.monotonic()

    # Re-find base codes (same as survey)
    from tests.ptb_survey import find_css_base_codes_fast, random_multi_term_poly
    base_codes = find_css_base_codes_fast(ell, m)
    by_k = {}
    for bc in base_codes:
        k = bc["k"]
        if k not in by_k:
            by_k[k] = bc
    base_codes = sorted(by_k.values(), key=lambda x: x["k"], reverse=True)
    base_codes = base_codes[:5]  # same max_base as survey

    _print(f"  Base codes: {[bc['k'] for bc in base_codes]}")

    # Regenerate all valid codes with same seed
    rng = np.random.default_rng(survey["seed"])
    all_ptb_codes = []
    seen = set()

    for bc in base_codes:
        A_terms = bc["A_terms"]
        B_terms = bc["B_terms"]
        css_k = bc["k"]

        poly_a = terms_to_poly(A_terms)
        poly_b = terms_to_poly(B_terms)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)
        mat_A = _poly_to_matrix(bb, A_terms)
        mat_B = _poly_to_matrix(bb, B_terms)

        all_monomials = [(i, j) for i in range(ell) for j in range(m)]
        mono_matrices = {}
        for mono in all_monomials:
            mono_matrices[mono] = _poly_to_matrix(bb, [mono])

        def fast_poly_matrix(terms):
            result = np.zeros_like(mat_A)
            for t in terms:
                result = (result + mono_matrices[t]) % 2
            return result

        num_trials = survey["num_trials_per_base"]
        for _ in range(num_trials):
            C_terms = random_multi_term_poly(ell, m, rng)
            D_terms = random_multi_term_poly(ell, m, rng)

            mat_C = fast_poly_matrix(C_terms)
            mat_D = fast_poly_matrix(D_terms)

            if not check_commutativity(mat_A, mat_B, mat_C, mat_D):
                continue

            try:
                dim = ell * m
                zero = np.zeros((dim, dim), dtype=int)
                block1_x = np.hstack([mat_A, mat_B])
                block1_z = np.hstack([mat_C, mat_D])
                block2_x = np.hstack([zero, zero])
                block2_z = np.hstack([mat_B.T % 2, mat_A.T % 2])
                top = np.hstack([block1_x, block1_z])
                bottom = np.hstack([block2_x, block2_z])
                symplectic = np.vstack([top, bottom]) % 2
                code = QuditCode(symplectic)
                k = code.dimension
            except Exception:
                continue

            key = (css_k, k,
                   tuple(sorted(tuple(t) for t in C_terms)),
                   tuple(sorted(tuple(t) for t in D_terms)))
            if key not in seen:
                seen.add(key)
                all_ptb_codes.append({
                    "A_terms": A_terms,
                    "B_terms": B_terms,
                    "C_terms": C_terms,
                    "D_terms": D_terms,
                    "n": 2 * dim,
                    "k": k,
                    "css_base_k": css_k,
                })

    _print(f"  Regenerated {len(all_ptb_codes)} unique codes in {time.monotonic()-t0:.1f}s")

    # CSS distances for comparison
    _print("\nComputing CSS distances...")
    css_results = {}
    for bc in base_codes:
        bb = build_bb_code(ell, m, bc["A_terms"], bc["B_terms"])
        d, details = compute_distance_milp(
            bb, timeout_per_logical=args.timeout,
            total_timeout=args.total_timeout, early_stop=2,
        )
        css_results[bc["k"]] = {"d": d, "exact": details.get("exact", False)}
        exact_tag = "" if details.get("exact") else "≤"
        _print(f"  CSS k={bc['k']}: d{exact_tag}{d}")

    # Pass 1: Screen for d=2
    _print(f"\nPass 1: Screening {len(all_ptb_codes)} codes ({args.screen_timeout}s)...")
    screened = []
    d2_count = 0
    t_screen = time.monotonic()

    for ci, pc in enumerate(all_ptb_codes):
        try:
            code = build_pbb_code(
                ell, m,
                pc["A_terms"], pc["B_terms"],
                pc["C_terms"], pc["D_terms"],
            )
            ub = symplectic_weight_bound_pbb(code)
            d, details = compute_distance_milp_symplectic(
                code,
                timeout_per_logical=args.screen_timeout,
                total_timeout=args.screen_timeout,
                early_stop=2,
            )
            if d <= 2:
                d2_count += 1
            else:
                screened.append({**pc, "d_screen": d, "ub": ub})
        except Exception as e:
            _print(f"  [{ci+1}] ERROR: {e}")

        if (ci + 1) % 50 == 0:
            _print(f"  Screened {ci+1}/{len(all_ptb_codes)}: "
                  f"{d2_count} d<=2, {len(screened)} d>2")

    screen_time = time.monotonic() - t_screen
    _print(f"  Screening done in {screen_time:.1f}s: "
          f"{d2_count} d<=2, {len(screened)} d>2")

    # Pass 2: Full MILP on d>2 codes
    milp_results = []
    if screened:
        _print(f"\nPass 2: Full MILP on {len(screened)} codes "
              f"({args.timeout}s/logical, {args.total_timeout}s total)...")

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
                        timeout_per_logical=args.timeout,
                        total_timeout=args.total_timeout,
                        early_stop=2,
                    )

                    result = {**pc, "d": d, "ub": pc["ub"],
                              "milp_details": {k: v for k, v in details.items()
                                               if k != "per_logical"}}
                    milp_results.append(result)

                    if d > best_d:
                        best_d = d
                        best_code = result

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
                exact_tag = "" if best_code["milp_details"].get("exact") else "≤"
                _print(f"  Best at k={k_val}: "
                      f"[[{best_code['n']},{k_val},{exact_tag}{d}]] "
                      f"FOM={k_val*d*d/best_code['n']:.1f}")

    # Summary
    total_time = time.monotonic() - t0
    _print(f"\n{'='*60}")
    _print(f"MILP VERIFICATION SUMMARY -- ({ell},{m}), n={n}")
    _print(f"{'='*60}")
    _print(f"Total time: {total_time:.1f}s")
    _print(f"Codes screened: {len(all_ptb_codes)}")
    _print(f"  d<=2: {d2_count}")
    _print(f"  d>2: {len(screened)}")
    _print(f"  MILP verified: {len(milp_results)}")

    css_k_values = set(bc["k"] for bc in base_codes)
    ptb_k_values = set(pc["k"] for pc in all_ptb_codes)
    new_k_values = ptb_k_values - css_k_values

    if milp_results:
        d4_plus = [r for r in milp_results if r["d"] >= 4]
        _print(f"\n  With d >= 4: {len(d4_plus)}")

        if d4_plus:
            _print("\n  Top 15 codes by FOM:")
            d4_plus.sort(key=lambda r: r["k"] * r["d"]**2 / r["n"], reverse=True)
            for r in d4_plus[:15]:
                d = r["d"]
                exact_tag = "" if r["milp_details"].get("exact") else "≤"
                fom = r["k"] * d**2 / r["n"]
                marker = " ***NEW k***" if r["k"] in new_k_values else ""
                _print(f"    [[{r['n']},{r['k']},{exact_tag}{d}]] "
                      f"FOM={fom:.1f}{marker}")
                _print(f"      C={r['C_terms']} D={r['D_terms']}")

        _print("\n  CSS vs non-CSS comparison:")
        for k_val in sorted(set(r["k"] for r in milp_results)):
            codes_at_k = [r for r in milp_results if r["k"] == k_val]
            best_d = max(r["d"] for r in codes_at_k)
            css_d = css_results.get(k_val, {}).get("d", 0)
            marker = " ***NEW k***" if k_val in new_k_values else ""
            css_info = f"CSS d={css_d}" if css_d else "no CSS"
            improvement = ""
            if css_d and best_d > css_d:
                improvement = f" (+{best_d - css_d})"
            _print(f"    k={k_val}: best PBB d≤{best_d}, {css_info}{improvement}{marker}")

    # Save results
    output = {
        "lattice": [ell, m],
        "n": n,
        "css_distances": {str(k): v for k, v in css_results.items()},
        "total_codes": len(all_ptb_codes),
        "d2_count": d2_count,
        "d_gt2_count": len(screened),
        "milp_timeout_per_logical": args.timeout,
        "milp_total_timeout": args.total_timeout,
        "milp_results": [
            {k: v for k, v in r.items() if k != "milp_details"}
            for r in milp_results
        ],
        "total_time_s": total_time,
    }

    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, "w") as f:
        json.dump(output, f, indent=2, default=str)
    _print(f"\nResults saved to {args.output}")


if __name__ == "__main__":
    main()
