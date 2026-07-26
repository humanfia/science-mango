#!/usr/bin/env python3
"""bridge_k.py — qcode-discovery BB codes → Lean 4 *logical-dimension* objectives.

For each bivariate-bicycle (BB) CSS code in qcode-discovery's ilp_catalog, emit a
self-contained Lean 4 file proving the code's logical dimension

    k = n - rank_F2(H_X) - rank_F2(H_Z),      n = 2·ℓ·m

by an *executable* F₂ Gaussian-elimination `rankF2` over bitmask rows, closed in
the kernel with `decide` (clean axioms — no `native_decide`, no `ofReduceBool`).

This is a strictly HARDER claim than CSS orthogonality / PBB commutation: those
are single algebraic identities, whereas k requires actually computing the ranks
of the two ℓm × 2ℓm parity-check matrices — a genuine linear-algebra fact whose
value distinguishes codes (a miscomputed circulant gives the wrong k, and
`decide` rejects it).

Circulant convention (validated against qldpc):
    G = [(a,b) for a in range(ell) for b in range(m)]
    circ_P[i][j] = 1  iff  (G[j] - G[i]) mod (ℓ,m) ∈ supp(P)
    H_X = [cA | cB],   H_Z = [cBᵀ | cAᵀ]

Usage:
    python3 bridge_k.py --catalog qcode-discovery/results/ilp_catalog.json \
        --out qcode_k_bridge [--lib-name KDim] [--limit N] [--sorry]
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from kmask import hx_hz_rows, rows_to_masks, rankF2


# ── identifier hygiene ──────────────────────────────────────────────────

def safe_ident(label: str, ell: int, m: int, idx: int) -> str:
    core = re.sub(r"[^0-9]+", "_", label).strip("_")
    return f"Code_{core}_l{ell}m{m}_{idx}"


# ── Lean file template ──────────────────────────────────────────────────

LEAN_TEMPLATE = """\
import Mathlib

/-!
# Logical dimension of BB code {label}

Bivariate-bicycle CSS code on the torus `ZMod {ell} × ZMod {m}` (n = 2·{ell}·{m} = {n})
with parity-check polynomials
  A = {a_math}
  B = {b_math}
over 𝔽₂.  Its logical dimension is
  `k = n - rank₂(H_X) - rank₂(H_Z)`
where `H_X = [circ A | circ B]` and `H_Z = [circ Bᵀ | circ Aᵀ]` are the block-
circulant parity checks.  The two rank₂ values are computed by an executable
F₂ Gaussian elimination (`rankF2`) over packed bitmask rows and the equation is
closed in the kernel by `decide`.

Source: qcode-discovery ilp_catalog, label `{label}`.
-/

namespace {module}

/-- Fully reduce `v` against a pivot-indexed F₂ basis (each element owns a distinct
    top bit); `fuel` bounds the reduction chain. -/
def reduceStep (basis : List Nat) : Nat → Nat → Nat
  | 0, v => v
  | fuel+1, v =>
    if v == 0 then 0
    else match basis.find? (fun b => b.log2 == v.log2) with
      | some b => reduceStep basis fuel (v ^^^ b)
      | none => v

/-- F₂ rank of a list of bitmask rows via Gaussian elimination. -/
def rankF2 (rows : List Nat) : Nat :=
  (rows.foldl (fun basis v =>
      let r := reduceStep basis {fuel} v
      if r == 0 then basis else r :: basis) []).length

/-- Rows of `H_X = [circ A | circ B]`, packed as F₂ bitmasks (LSB = column 0). -/
def Hx : List Nat := {hx}
/-- Rows of `H_Z = [circ Bᵀ | circ Aᵀ]`, packed as F₂ bitmasks. -/
def Hz : List Nat := {hz}

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1000000 in
/-- **Logical dimension**: `k = n - rank₂(H_X) - rank₂(H_Z) = {k}`. -/
theorem k_logical : {n} - rankF2 Hx - rankF2 Hz = {k} := {proof}

end {module}
"""

PROOF_FULL = "by decide"
PROOF_SORRY = "by\n  sorry"


def render_poly_math(terms) -> str:
    parts = []
    for a, b in terms:
        if a == 0 and b == 0:
            parts.append("1")
        elif b == 0:
            parts.append(f"x^{a}")
        elif a == 0:
            parts.append(f"y^{b}")
        else:
            parts.append(f"x^{a}·y^{b}")
    return " + ".join(parts) if parts else "0"


def render_lean(code: dict, module: str, proof: str) -> str:
    A = [tuple(t) for t in code["A"]]
    B = [tuple(t) for t in code["B"]]
    ell, m = code["ell"], code["m"]
    n = 2 * ell * m
    Hx, Hz = hx_hz_rows(A, B, ell, m)
    mx, mz = rows_to_masks(Hx), rows_to_masks(Hz)
    k = n - rankF2(mx) - rankF2(mz)
    return LEAN_TEMPLATE.format(
        label=code["label"], module=module, ell=ell, m=m, n=n, k=k, proof=proof,
        fuel=2 * n,
        a_math=render_poly_math(A), b_math=render_poly_math(B),
        hx="[" + ", ".join(map(str, mx)) + "]",
        hz="[" + ", ".join(map(str, mz)) + "]",
    ), k


def objective_row(code: dict, module: str, lib: str, k: int) -> dict:
    ell, m = code["ell"], code["m"]
    n = 2 * ell * m
    a_math = render_poly_math([tuple(t) for t in code["A"]])
    b_math = render_poly_math([tuple(t) for t in code["B"]])
    question = (
        f"Consider the bivariate-bicycle CSS code {code['label']} on the torus "
        f"Z_{ell} × Z_{m} (n = 2·{ell}·{m} = {n}), with parity-check polynomials "
        f"A = {a_math} and B = {b_math} over F₂. Its parity-check matrices are the "
        f"block circulants H_X = [circ A | circ B] and H_Z = [circ Bᵀ | circ Aᵀ]. "
        f"Prove that the logical dimension k = n - rank₂(H_X) - rank₂(H_Z) equals "
        f"{k}."
    )
    return {
        "index": module,
        "category": "quantum-ldpc/logical-dimension",
        "question": question,
        "lean_file": f"{lib}/{module}.lean",
        "target_theorem": f"{module}.k_logical",
        "source": {
            "dataset": "qcode-discovery/ilp_catalog",
            "label": code["label"], "ell": ell, "m": m, "n": n, "k": k,
            "A_terms": code["A"], "B_terms": code["B"],
        },
    }


def iter_codes(catalog: dict):
    for group, recs in catalog.items():
        for r in recs:
            if "A" in r and "B" in r and "ell" in r and "m" in r:
                yield r


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--catalog", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--lib-name", default="KDim")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--sorry", action="store_true")
    args = ap.parse_args()

    proof = PROOF_SORRY if args.sorry else PROOF_FULL
    lib = args.lib_name
    lean_dir = args.out / lib
    lean_dir.mkdir(parents=True, exist_ok=True)
    catalog = json.loads(args.catalog.read_text())

    objectives, modules, seen = [], [], set()
    for idx, code in enumerate(iter_codes(catalog)):
        if args.limit and len(modules) >= args.limit:
            break
        module = safe_ident(code["label"], code["ell"], code["m"], idx)
        base, n = module, 1
        while module in seen:
            module = f"{base}_{n}"; n += 1
        seen.add(module)
        text, k = render_lean(code, module, proof)
        (lean_dir / f"{module}.lean").write_text(text)
        objectives.append(objective_row(code, module, lib, k))
        modules.append(module)

    root = "\n".join(f"import {lib}.{mod}" for mod in modules) + "\n"
    (args.out / f"{lib}.lean").write_text(root)
    with (args.out / "objectives.jsonl").open("w") as f:
        for row in objectives:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")

    print(f"Emitted {len(modules)} Lean files under {lean_dir}")
    print(f"Root module: {args.out / (lib + '.lean')}")
    print(f"Objectives:  {args.out / 'objectives.jsonl'} ({len(objectives)} rows)")


if __name__ == "__main__":
    main()
