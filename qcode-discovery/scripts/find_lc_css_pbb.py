"""Classify each PBB code in the catalog by Clifford-to-CSS equivalence.

Runs both checks referenced in paper §2.2 / App.~C on every record of
``results/campaign7_publication_merged.jsonl``:

  1. ``is_equivalently_css`` -- parity-2-coloring decision (derived in
     ``evaluation/clifford_equivalence``); catches codes whose generators
     reduce to pure-X / pure-Z under non-uniform per-qubit Hadamards.
  2. ``is_lc_equivalent_css_group`` -- uniform per-block S-gate check;
     catches codes reducible to CSS via uniform S on block 1 and/or 2.

Reproduces the paper's accounting: 10 of 295 are CSS-equivalent under
single-qubit Cliffords (9 Hadamard-CSS + 1 uniform-S-CSS); 285 genuinely
non-CSS.  Also prints the unique uniform-S code's polynomials for the
Table 2 (tab:pbb_best) footnote.
"""
from __future__ import annotations

import json
from pathlib import Path

from evaluation.clifford_equivalence import (
    is_equivalently_css,
    is_lc_equivalent_css_group,
)
from evaluation.pbb_code import build_pbb_code


def _term_to_tex(t):
    x_exp, y_exp = t
    if x_exp == 0 and y_exp == 0:
        return "1"
    parts = []
    if x_exp == 1:
        parts.append("x")
    elif x_exp > 1:
        parts.append(f"x^{x_exp}")
    if y_exp == 1:
        parts.append("y")
    elif y_exp > 1:
        parts.append(f"y^{y_exp}")
    return "".join(parts)


def _poly_tex(terms):
    if not terms:
        return "0"
    return "+".join(_term_to_tex(t) for t in terms)


def main() -> None:
    catalog = Path("results/campaign7_publication_merged.jsonl")
    records = [json.loads(line) for line in catalog.open()]
    print(f"catalog: {len(records)} PBB codes")

    hadamard_hits = []
    uniform_s_hits = []

    for rec in records:
        A = [tuple(t) for t in rec["A_terms"]]
        B = [tuple(t) for t in rec["B_terms"]]
        C = [tuple(t) for t in rec["C_terms"]] if rec["C_terms"] else None
        D = [tuple(t) for t in rec["D_terms"]] if rec["D_terms"] else None

        # Check 2 in paper §2.2: Hadamard 2-coloring
        code = build_pbb_code(rec["ell"], rec["m"], A, B, C, D)
        had = is_equivalently_css(code)

        # Check 3 in paper §2.2 / App. C: uniform per-block S
        s = is_lc_equivalent_css_group(rec["ell"], rec["m"], A, B, C, D)

        if had["is_css"]:
            hadamard_hits.append((rec, had))
        if s["is_lc_css"]:
            uniform_s_hits.append((rec, s))

    print(f"\nHadamard-CSS (non-uniform per-qubit H): {len(hadamard_hits)}  (paper: 9)")
    for rec, _ in hadamard_hits:
        print(f"  [[{rec['n']},{rec['k']},{rec['d']}]] at ({rec['ell']},{rec['m']})")

    print(f"\nUniform-S LC-CSS: {len(uniform_s_hits)}  (paper: 1)")
    for rec, result in uniform_s_hits:
        print(
            f"  [[{rec['n']},{rec['k']},{rec['d']}]] at ({rec['ell']},{rec['m']}) "
            f"  (s1={result['s1']}, s2={result['s2']})"
        )
        print(f"    A = {_poly_tex(rec['A_terms'])}")
        print(f"    B = {_poly_tex(rec['B_terms'])}")
        print(f"    C = {_poly_tex(rec['C_terms']) if rec['C_terms'] else '0'}")
        print(f"    D = {_poly_tex(rec['D_terms']) if rec['D_terms'] else '0'}")

    # Overlap should be empty (verified by construction)
    hadamard_keys = {id(r) for r, _ in hadamard_hits}
    overlap = [r for r, _ in uniform_s_hits if id(r) in hadamard_keys]
    total = len(hadamard_hits) + len(uniform_s_hits) - len(overlap)
    print(f"\nOverlap (caught by both checks): {len(overlap)}")
    print(f"Total CSS-equivalent under single-qubit Cliffords: {total}  (paper: 10)")
    print(f"Genuinely non-CSS: {len(records) - total}  (paper: 285)")


if __name__ == "__main__":
    main()
