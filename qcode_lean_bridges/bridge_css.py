#!/usr/bin/env python3
"""bridge_css.py — qcode-discovery BB codes → Lean 4 CSS-orthogonality objectives.

Reads the bivariate-bicycle (BB) code catalog from qcode-discovery and, for each
CSS code, emits:

  1. A self-contained, fully-proved Lean 4 file asserting the CSS
     orthogonality identity  H_X · H_Zᵀ = A·B + B·A = 0  over F₂,
     modelled in the group algebra  𝔽₂[Z_ℓ × Z_m].
  2. One line in an Archon-ingestible objectives JSONL, carrying the raw
     polynomial data plus a natural-language statement of the claim.

Math background
---------------
A BB code on the torus Z_ℓ × Z_m is defined by two polynomials A, B in the
group algebra  GA = AddMonoidAlgebra (ZMod 2) (ZMod ℓ × ZMod m).  A monomial
x^a·y^b is the basis element  single (a, b) 1.  The CSS parity checks are
H_X = [A | B],  H_Z = [B | A] (block circulants), and CSS orthogonality
H_X H_Zᵀ = 0 reduces to the group-algebra identity  A·B + B·A = 0.

Because GA is a *commutative* ring of characteristic 2:
    A·B + B·A  =  A·B + A·B  (mul_comm)  =  0  (CharTwo.add_self_eq_zero).
The proof is therefore identical for every code — only the definitions of A and
B vary.  The CharP 2 instance is lifted from the coefficient ring ZMod 2 via
the (injective) algebra map.  This template was validated to compile against
Mathlib v4.32.0.

Usage
-----
    python3 bridge_css.py \
        --catalog /path/to/ilp_catalog.json \
        --out     /path/to/qcode_bridge \
        [--limit N] [--lib-name QCode]
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


# ── polynomial rendering ────────────────────────────────────────────────

def render_poly_lean(terms: list[list[int]]) -> str:
    """Render [[a,b],...] as a Lean sum of `mono a b` over the group algebra."""
    return " + ".join(f"mono {a} {b}" for a, b in terms)


def render_poly_math(terms: list[list[int]]) -> str:
    """Human-readable x^a·y^b polynomial for the natural-language claim."""
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
    return " + ".join(parts)


# ── identifier hygiene ──────────────────────────────────────────────────

def safe_ident(label: str, ell: int, m: int, idx: int) -> str:
    """Turn a label like '[[144,24,<=12]]' into a valid, unique Lean module name."""
    # keep the [[n,k,d]] numbers, drop brackets/≤/<= and spaces
    core = re.sub(r"[^0-9]+", "_", label).strip("_")
    return f"Code_{core}_l{ell}m{m}_{idx}"


# ── Lean file template ──────────────────────────────────────────────────

LEAN_TEMPLATE = """\
import Mathlib

/-!
# CSS orthogonality for BB code {label}

Bivariate-bicycle code on the torus `ZMod {ell} × ZMod {m}` with parity-check
polynomials
  A = {a_math}
  B = {b_math}
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `{label}`.
-/

open AddMonoidAlgebra

namespace {module}

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod {ell} × ZMod {m})

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod {ell}) (b : ZMod {m}) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `{label}`. -/
noncomputable def A : GA := {a_lean}

/-- Parity-check polynomial `B` of code `{label}`. -/
noncomputable def B : GA := {b_lean}

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := {proof}

end {module}
"""

# Fully-proved body (the proof is mechanical and identical for every code).
PROOF_FULL = "by\n  rw [mul_comm B A]\n  exact CharTwo.add_self_eq_zero _"
# Sorry stub — leave the proof for `archon loop`'s prover to fill.
PROOF_SORRY = "by\n  sorry"


def render_lean(code: dict, module: str, proof: str) -> str:
    return LEAN_TEMPLATE.format(
        label=code["label"],
        ell=code["ell"],
        m=code["m"],
        module=module,
        proof=proof,
        a_math=render_poly_math(code["A"]),
        b_math=render_poly_math(code["B"]),
        a_lean=render_poly_lean(code["A"]),
        b_lean=render_poly_lean(code["B"]),
    )


# ── objective JSONL row ─────────────────────────────────────────────────

def objective_row(code: dict, module: str, lib: str) -> dict:
    label = code["label"]
    a_math = render_poly_math(code["A"])
    b_math = render_poly_math(code["B"])
    question = (
        f"Consider the bivariate-bicycle CSS code {label} on the torus "
        f"Z_{code['ell']} × Z_{code['m']}, with parity-check polynomials "
        f"A = {a_math} and B = {b_math} over the field F₂. Working in the group "
        f"algebra F₂[Z_{code['ell']} × Z_{code['m']}], prove the CSS "
        f"orthogonality condition H_X · H_Zᵀ = A·B + B·A = 0."
    )
    return {
        "index": module,
        "category": "quantum-ldpc/css-orthogonality",
        "question": question,
        "lean_file": f"{lib}/{module}.lean",
        "target_theorem": f"{module}.css_orthogonal",
        "source": {
            "dataset": "qcode-discovery/ilp_catalog",
            "label": label,
            "ell": code["ell"],
            "m": code["m"],
            "A_terms": code["A"],
            "B_terms": code["B"],
            "k": code.get("k"),
        },
    }


# ── driver ──────────────────────────────────────────────────────────────

def iter_codes(catalog: dict):
    """Yield every code record across all top-level groups that has A and B."""
    for group, recs in catalog.items():
        if not isinstance(recs, list):
            continue
        for r in recs:
            if isinstance(r, dict) and "A" in r and "B" in r:
                yield group, r


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--catalog", required=True, type=Path,
                    help="Path to ilp_catalog.json")
    ap.add_argument("--out", required=True, type=Path,
                    help="Output directory (Lean files + objectives.jsonl)")
    ap.add_argument("--lib-name", default="QCode",
                    help="Lean library / directory name (default: QCode)")
    ap.add_argument("--limit", type=int, default=0,
                    help="Only emit the first N codes (0 = all)")
    ap.add_argument("--sorry", action="store_true",
                    help="Emit `by sorry` stubs instead of the full proof "
                         "(so archon's prover can close them end-to-end)")
    args = ap.parse_args()

    proof = PROOF_SORRY if args.sorry else PROOF_FULL

    catalog = json.loads(args.catalog.read_text())

    lib = args.lib_name
    lean_dir = args.out / lib
    lean_dir.mkdir(parents=True, exist_ok=True)

    objectives: list[dict] = []
    modules: list[str] = []
    seen: set[str] = set()

    for idx, (group, code) in enumerate(iter_codes(catalog)):
        if args.limit and len(modules) >= args.limit:
            break
        module = safe_ident(code["label"], code["ell"], code["m"], idx)
        # guarantee uniqueness
        base = module
        n = 1
        while module in seen:
            module = f"{base}_{n}"
            n += 1
        seen.add(module)

        (lean_dir / f"{module}.lean").write_text(render_lean(code, module, proof))
        objectives.append(objective_row(code, module, lib))
        modules.append(module)

    # root module importing every code file
    root = "\n".join(f"import {lib}.{mod}" for mod in modules) + "\n"
    (args.out / f"{lib}.lean").write_text(root)

    # objectives JSONL
    with (args.out / "objectives.jsonl").open("w") as f:
        for row in objectives:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")

    print(f"Emitted {len(modules)} Lean files under {lean_dir}")
    print(f"Root module: {args.out / (lib + '.lean')}")
    print(f"Objectives:  {args.out / 'objectives.jsonl'} ({len(objectives)} rows)")


if __name__ == "__main__":
    main()
