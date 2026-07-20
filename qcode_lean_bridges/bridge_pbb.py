#!/usr/bin/env python3
"""bridge_pbb.py — qcode-discovery PBB (non-CSS) codes → Lean 4 commutation objectives.

Reads the perturbed-bivariate-bicycle (PBB) non-CSS code catalog from
qcode-discovery (campaign7_publication_merged.jsonl) and, for each code, emits:

  1. A self-contained Lean 4 file asserting the within-block-1 *commutation*
     identity  M := A·Cᵀ + B·Dᵀ  is antipode-symmetric  (M = Mᵀ)  over 𝔽₂.
  2. One line in an Archon-ingestible objectives JSONL.

Math background
---------------
A PBB non-CSS code on the torus Z_ℓ × Z_m is built from FOUR polynomials
A, B, C, D over 𝔽₂.  The stabilizer matrix has block-1 x-part [A | B] and
block-1 z-part [C | D].  X- and Z-stabilizers commute iff the group-algebra
element  M = A·Cᵀ + B·Dᵀ  is invariant under the antipode  (x,y) ↦ (−x,−y),
i.e.  M = Mᵀ.  Here  Cᵀ  is the antipode of C, so the monomial x^a·y^b of A
times x^{−c}·y^{−d} of Cᵀ contributes  x^{a−c}·y^{b−d}, with 𝔽₂ (XOR)
coefficient cancellation.  This is the *exact* condition qcode-discovery's
`evaluation/pbb_code.check_commutativity` enforces:
    M = (A @ C^T + B @ D^T) % 2   must equal   M^T.

Unlike CSS orthogonality (trivially true for every code), commutation is a
GENUINE per-code arithmetic fact: it holds only for validly-constructed codes,
and each proof must actually compute M and check antipode-closure.

Lean modelling
--------------
Polynomials are their 𝔽₂ support, modelled as `List (ZMod ℓ × ZMod m)`.
`M = A·Cᵀ + B·Dᵀ` is computed by XOR-folding the monomials `p − q`.  The claim
`∀ g ∈ M, (−g) ∈ M` (= M = Mᵀ) is closed by `decide` under a raised
`maxRecDepth` (kernel-clean: axioms are only propext/Classical.choice/Quot.sound,
no sorryAx and no ofReduceBool).  Validated against Mathlib v4.32.0 on the
smallest (6,3) and largest (30,6) rings; the claim is non-vacuous (`decide`
rejects non-commuting A,B,C,D).

Usage
-----
    python3 bridge_pbb.py \
        --catalog /path/to/campaign7_publication_merged.jsonl \
        --out     /path/to/qcode_pbb_bridge \
        [--limit N] [--lib-name PBB] [--sorry]
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


# ── polynomial rendering ────────────────────────────────────────────────

def render_list_lean(terms: list[list[int]]) -> str:
    """Render [[a,b],...] as a Lean `List (ZMod ℓ × ZMod m)` literal."""
    return "[" + ", ".join(f"({a}, {b})" for a, b in terms) + "]"


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
    return " + ".join(parts) if parts else "0"


# ── identifier hygiene ──────────────────────────────────────────────────

def safe_ident(code_id: str, ell: int, m: int, idx: int) -> str:
    """Turn a code_id like '30_6_0260' into a valid, unique Lean module name."""
    core = "".join(ch if ch.isalnum() else "_" for ch in str(code_id)).strip("_")
    if not core:
        core = f"l{ell}m{m}_{idx}"
    return f"Code_{core}"


# ── Lean file template ──────────────────────────────────────────────────

LEAN_TEMPLATE = """\
import Mathlib

/-!
# PBB non-CSS commutation for code {label}

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod {ell} × ZMod {m}`
with block-1 stabilizer polynomials
  A = {a_math}
  B = {b_math}
  C = {c_math}
  D = {d_math}
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `{code_id}`.
-/

namespace {module}

abbrev G := ZMod {ell} × ZMod {m}

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := {a_lean}
/-- Parity polynomial `B`. -/
def B : List G := {b_lean}
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := {c_lean}
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := {d_lean}

/-- Toggle `g` in an 𝔽₂ support list (add mod 2). -/
def xorIns (p : List G) (g : G) : List G := if g ∈ p then p.erase g else g :: p

/-- Support of `P * Qᵀ` over 𝔽₂: XOR of all monomials `p - q` (antipode on `Q`). -/
def mulT (P Q : List G) : List G :=
  (P.flatMap (fun a => Q.map (fun c => a - c))).foldl xorIns []

/-- `M = A·Cᵀ + B·Dᵀ` (𝔽₂ addition = XOR of supports). -/
def M : List G := (mulT B D).foldl xorIns (mulT A C)

set_option maxRecDepth 100000 in
/-- **Within-block-1 commutation**: `M` is closed under the antipode `g ↦ -g`
    (equivalently `M = Mᵀ`), so the X/Z stabilizers of block 1 commute. -/
theorem pbb_commute : ∀ g ∈ M, (-g) ∈ M := {proof}

end {module}
"""

# Fully-proved body: the finite antipode-closure check reduces in the kernel.
PROOF_FULL = "by decide"
# Sorry stub — leave the proof for `archon loop`'s prover to fill.
PROOF_SORRY = "by\n  sorry"


def render_lean(code: dict, module: str, proof: str) -> str:
    n, k, d = code.get("n"), code.get("k"), code.get("d")
    label = f"[[{n},{k},{d}]]" if d is not None else f"[[{n},{k}]]"
    return LEAN_TEMPLATE.format(
        label=label,
        code_id=code.get("code_id", module),
        ell=code["ell"],
        m=code["m"],
        module=module,
        proof=proof,
        a_math=render_poly_math(code["A_terms"]),
        b_math=render_poly_math(code["B_terms"]),
        c_math=render_poly_math(code["C_terms"]),
        d_math=render_poly_math(code["D_terms"]),
        a_lean=render_list_lean(code["A_terms"]),
        b_lean=render_list_lean(code["B_terms"]),
        c_lean=render_list_lean(code["C_terms"]),
        d_lean=render_list_lean(code["D_terms"]),
    )


# ── objective JSONL row ─────────────────────────────────────────────────

def objective_row(code: dict, module: str, lib: str) -> dict:
    n, k, d = code.get("n"), code.get("k"), code.get("d")
    label = f"[[{n},{k},{d}]]" if d is not None else f"[[{n},{k}]]"
    a_math = render_poly_math(code["A_terms"])
    b_math = render_poly_math(code["B_terms"])
    c_math = render_poly_math(code["C_terms"])
    d_math = render_poly_math(code["D_terms"])
    question = (
        f"Consider the perturbed bivariate-bicycle (non-CSS) code {label} on the "
        f"torus Z_{code['ell']} × Z_{code['m']}, with block-1 stabilizer "
        f"polynomials A = {a_math}, B = {b_math}, C = {c_math}, D = {d_math} over "
        f"the field F₂. Working in the group algebra F₂[Z_{code['ell']} × "
        f"Z_{code['m']}], let M = A·Cᵀ + B·Dᵀ where (·)ᵀ is the antipode "
        f"x^a·y^b ↦ x^(-a)·y^(-b). Prove that M is antipode-symmetric, M = Mᵀ "
        f"(equivalently M is closed under g ↦ -g), i.e. the X- and Z-stabilizers "
        f"of block 1 commute."
    )
    return {
        "index": module,
        "category": "quantum-ldpc/pbb-commutation",
        "question": question,
        "lean_file": f"{lib}/{module}.lean",
        "target_theorem": f"{module}.pbb_commute",
        "source": {
            "dataset": "qcode-discovery/campaign7_publication_merged",
            "code_id": code.get("code_id"),
            "ell": code["ell"],
            "m": code["m"],
            "A_terms": code["A_terms"],
            "B_terms": code["B_terms"],
            "C_terms": code["C_terms"],
            "D_terms": code["D_terms"],
            "n": n,
            "k": k,
            "d": d,
        },
    }


# ── driver ──────────────────────────────────────────────────────────────

def iter_codes(catalog_path: Path):
    """Yield every non-CSS record (has A/B/C/D_terms and non-empty C,D)."""
    with catalog_path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if all(key in r for key in ("A_terms", "B_terms", "C_terms", "D_terms")):
                if r["C_terms"] and r["D_terms"]:
                    yield r


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--catalog", required=True, type=Path,
                    help="Path to campaign7_publication_merged.jsonl")
    ap.add_argument("--out", required=True, type=Path,
                    help="Output directory (Lean files + objectives.jsonl)")
    ap.add_argument("--lib-name", default="PBB",
                    help="Lean library / directory name (default: PBB)")
    ap.add_argument("--limit", type=int, default=0,
                    help="Only emit the first N codes (0 = all)")
    ap.add_argument("--sorry", action="store_true",
                    help="Emit `by sorry` stubs instead of the full proof "
                         "(so archon's prover can close them end-to-end)")
    args = ap.parse_args()

    proof = PROOF_SORRY if args.sorry else PROOF_FULL

    lib = args.lib_name
    lean_dir = args.out / lib
    lean_dir.mkdir(parents=True, exist_ok=True)

    objectives: list[dict] = []
    modules: list[str] = []
    seen: set[str] = set()

    for idx, code in enumerate(iter_codes(args.catalog)):
        if args.limit and len(modules) >= args.limit:
            break
        module = safe_ident(code.get("code_id", ""), code["ell"], code["m"], idx)
        base = module
        n = 1
        while module in seen:
            module = f"{base}_{n}"
            n += 1
        seen.add(module)

        (lean_dir / f"{module}.lean").write_text(render_lean(code, module, proof))
        objectives.append(objective_row(code, module, lib))
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
