#!/usr/bin/env python3
'''Generate Lean-checked exact [[n,k,d]] certificates for CSS BB codes.

Python/SciPy is an untrusted certificate producer. Lean reconstructs checks,
computes ranks, validates logical bases, checks an upper witness, and proves
the lower bound through bv_decide/LRAT.
'''
from __future__ import annotations
import argparse
import json
import shutil
from pathlib import Path
from bridge_distance import (append_witness, find_witness, fingerprint, iter_codes,
    load_witnesses, logical_bases, safe_ident, verify_certificate)
from kmask import hx_hz_rows, rows_to_masks

BASIC_LEAN = r'''import Mathlib
import Std.Tactic.BVDecide

namespace QExact

def parityAt {n : Nat} (x : BitVec n) (support : List Nat) : Bool :=
  support.foldl (fun acc i => Bool.xor acc (x.getLsbD i)) false

def orthogonal {n : Nat} (rows : List (List Nat)) (x : BitVec n) : Bool :=
  rows.all (fun row => parityAt x row == false)

def pairsAny {n : Nat} (duals : List (List Nat)) (x : BitVec n) : Bool :=
  duals.any (fun dual => parityAt x dual == true)

def weightBVAux {n : Nat} (x : BitVec n) : Nat -> BitVec 9
  | 0 => BitVec.ofNat 9 0
  | i + 1 => weightBVAux x i + (BitVec.ofBool (x.getLsbD i)).zeroExtend 9

/-- Exact Hamming weight for corpus blocks; every verified block also proves n < 512. -/
def weightBV {n : Nat} (x : BitVec n) : BitVec 9 := weightBVAux x n

def reduceStep (basis : List Nat) : Nat -> Nat -> Nat
  | 0, v => v
  | fuel+1, v =>
    if v == 0 then 0
    else match basis.find? (fun b => b.log2 == v.log2) with
      | some b => reduceStep basis fuel (v ^^^ b)
      | none => v

def rankF2 (fuel : Nat) (rows : List Nat) : Nat :=
  (rows.foldl (fun basis v =>
      let r := reduceStep basis fuel v
      if r == 0 then basis else r :: basis) []).length

def supportMask (support : List Nat) : Nat :=
  support.foldl (fun mask i => mask ||| (1 <<< i)) 0

def rowMasks (rows : List (List Nat)) : List Nat := rows.map supportMask

def pairSupports (a b : List Nat) : Bool :=
  a.foldl (fun acc i => Bool.xor acc (b.contains i)) false

def pairingRowAux (x : List Nat) : List (List Nat) -> Nat -> Nat
  | [], _ => 0
  | z :: zs, i =>
      (if pairSupports x z then (1 <<< i) else 0) ||| pairingRowAux x zs (i + 1)

def pairingRows (xs zs : List (List Nat)) : List Nat :=
  xs.map (fun x => pairingRowAux x zs 0)

structure CSSCode (n : Nat) where
  hx : List (List Nat)
  hz : List (List Nat)
  xDuals : List (List Nat)
  zDuals : List (List Nat)

def IsXLogical {n : Nat} (code : CSSCode n) (x : BitVec n) : Bool :=
  orthogonal code.hz x && pairsAny code.zDuals x

def IsZLogical {n : Nat} (code : CSSCode n) (z : BitVec n) : Bool :=
  orthogonal code.hx z && pairsAny code.xDuals z

def logicalDimension {n : Nat} (code : CSSCode n) : Nat :=
  n - rankF2 (2*n) (rowMasks code.hx) - rankF2 (2*n) (rowMasks code.hz)

def BasisValid {n : Nat} (code : CSSCode n) : Prop :=
  code.xDuals.length = logicalDimension code /\
  code.zDuals.length = logicalDimension code /\
  code.xDuals.all (fun s => orthogonal code.hz (BitVec.ofNat n (supportMask s))) = true /\
  code.zDuals.all (fun s => orthogonal code.hx (BitVec.ofNat n (supportMask s))) = true /\
  rankF2 (2*n) (rowMasks code.hx ++ rowMasks code.xDuals) =
    n - rankF2 (2*n) (rowMasks code.hz) /\
  rankF2 (2*n) (rowMasks code.hz ++ rowMasks code.zDuals) =
    n - rankF2 (2*n) (rowMasks code.hx) /\
  rankF2 (2*n) (pairingRows code.xDuals code.zDuals) = logicalDimension code

instance {n : Nat} (code : CSSCode n) : Decidable (BasisValid code) := by
  unfold BasisValid
  infer_instance

def HasDistanceAtMost {n : Nat} (code : CSSCode n) (d : Nat) : Prop :=
  exists x, (IsXLogical code x = true \/ IsZLogical code x = true) /\
    weightBV x <= BitVec.ofNat 9 d

def HasDistanceAtLeast {n : Nat} (code : CSSCode n) (d : Nat) : Prop :=
  forall x, IsXLogical code x = true \/ IsZLogical code x = true ->
    BitVec.ofNat 9 d <= weightBV x

def HasExactDistance {n : Nat} (code : CSSCode n) (d : Nat) : Prop :=
  HasDistanceAtMost code d /\ HasDistanceAtLeast code d

structure VerifiedParameters {n : Nat} (code : CSSCode n) (k d : Nat) : Prop where
  blockFits : n < 512
  dimension : logicalDimension code = k
  basis : BasisValid code
  distance : HasExactDistance code d

end QExact
'''

def support(mask: int, n: int) -> list[int]:
    return [i for i in range(n) if (mask >> i) & 1]

def lean_nat_list(xs) -> str:
    return "[" + ", ".join(str(int(x)) for x in xs) + "]"

def lean_rows(masks: list[int], n: int) -> str:
    return "[\n    " + ",\n    ".join(lean_nat_list(support(m, n)) for m in masks) + "\n  ]"

def render_module(code: dict, module: str, cert: dict, timeout: int) -> str:
    ell, m = int(code["ell"]), int(code["m"])
    n, k, d = 2 * ell * m, int(code["k"]), int(code["ilp_d"])
    matrix_hx, matrix_hz = hx_hz_rows([tuple(t) for t in code["A"]],
        [tuple(t) for t in code["B"]], ell, m)
    hx, hz = rows_to_masks(matrix_hx), rows_to_masks(matrix_hz)
    lx, lz = logical_bases(hx, hz, n)
    witness = int(cert["witness_mask"])
    return f'''import QExact.Basic

/-! Lean-checked exact parameters for {code["label"]}; target [[{n},{k},{d}]]. -/
namespace {module}
open QExact

def code : CSSCode {n} := {{
  hx := {lean_rows(hx, n)},
  hz := {lean_rows(hz, n)},
  xDuals := {lean_rows(lx, n)},
  zDuals := {lean_rows(lz, n)}
}}

def witness : BitVec {n} := BitVec.ofNat {n} {witness}

theorem block_length : 2 * {ell} * {m} = {n} := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dimension_verified : logicalDimension code = {k} := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basis_verified : BasisValid code := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem distance_upper : HasDistanceAtMost code {d} := by
  refine ⟨witness, ?_⟩
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem distance_lower : HasDistanceAtLeast code {d} := by
  intro x
  -- A broad `simp` spends minutes searching the full Mathlib simp set while
  -- expanding these concrete matrices. This closed list performs exactly the
  -- reductions needed by the bit-blaster and produces the same proposition.
  simp only [code, IsXLogical, IsZLogical, orthogonal, pairsAny, parityAt,
    weightBV, weightBVAux, List.all, List.any, List.foldl]
  bv_decide (config := {{ timeout := {timeout} }})

theorem exact_parameters : VerifiedParameters code {k} {d} := by
  exact ⟨by decide, dimension_verified, basis_verified,
    And.intro distance_upper distance_lower⟩

end {module}
'''

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--catalog", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--lib-name", default="QExact")
    ap.add_argument("--witnesses", type=Path)
    ap.add_argument("--search-timeout", type=float, default=600)
    ap.add_argument("--sat-timeout", type=int, default=10800)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--skip-missing", action="store_true")
    ap.add_argument("--seed-witnesses", type=Path,
        help="Import an existing JSONL witness cache before searching")
    args = ap.parse_args()
    catalog = json.loads(args.catalog.read_text())
    witness_path = args.witnesses or (args.out / "exact_witnesses.jsonl")
    args.out.mkdir(parents=True, exist_ok=True)
    if args.seed_witnesses and not witness_path.exists():
        shutil.copyfile(args.seed_witnesses, witness_path)
    cached = load_witnesses(witness_path)
    lean_dir = args.out / args.lib_name
    lean_dir.mkdir(parents=True, exist_ok=True)
    (lean_dir / "Basic.lean").write_text(BASIC_LEAN)
    modules, objectives = [], []
    for idx, _group, code in iter_codes(catalog):
        if code.get("ilp_d") is None or code.get("k") is None:
            continue
        if args.limit and len(modules) >= args.limit:
            break
        n, d = 2 * int(code["ell"]) * int(code["m"]), int(code["ilp_d"])
        matrix_hx, matrix_hz = hx_hz_rows([tuple(t) for t in code["A"]],
            [tuple(t) for t in code["B"]], int(code["ell"]), int(code["m"]))
        hx, hz = rows_to_masks(matrix_hx), rows_to_masks(matrix_hz)
        key, cert = fingerprint(code), cached.get(fingerprint(code))
        if cert is not None:
            try:
                verify_certificate(cert["logical_type"], int(cert["witness_mask"]),
                    int(cert["dual_mask"]), d, hx, hz, n)
            except ValueError:
                cert = None
        if cert is None:
            print(f"search exact upper witness {code['label']} (d={d})", flush=True)
            try:
                typ, witness, dual = find_witness(hx, hz, n, d, args.search_timeout)
            except RuntimeError as exc:
                if args.skip_missing:
                    print(f"SKIP {code['label']}: {exc}", flush=True)
                    continue
                raise
            cert = {"fingerprint": key, "label": code["label"], "logical_type": typ,
                "witness_mask": witness, "dual_mask": dual,
                "weight": witness.bit_count(), "target": d}
            verify_certificate(typ, witness, dual, d, hx, hz, n)
            append_witness(witness_path, cert)
            cached[key] = cert
            print(f"found {typ} witness of weight {witness.bit_count()}", flush=True)
        module = safe_ident(code["label"], int(code["ell"]), int(code["m"]), idx)
        (lean_dir / f"{module}.lean").write_text(render_module(
            code, module, cert, args.sat_timeout))
        modules.append(module)
        objectives.append({"index": module, "category": "quantum-ldpc/exact-parameters",
            "lean_file": f"{args.lib_name}/{module}.lean",
            "target_theorem": f"{module}.exact_parameters",
            "source": {"label": code["label"], "n": n, "k": int(code["k"]), "d": d}})
    (args.out / f"{args.lib_name}.lean").write_text("import QExact.Basic\n" +
        "\n".join(f"import {args.lib_name}.{m}" for m in modules) + "\n")
    with (args.out / "objectives.jsonl").open("w") as out:
        for row in objectives:
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
    print(f"Emitted {len(modules)} exact-parameter Lean modules under {lean_dir}")
    print(f"Witness cache: {witness_path}")

if __name__ == "__main__":
    main()
