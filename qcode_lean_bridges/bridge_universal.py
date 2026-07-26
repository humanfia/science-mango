#!/usr/bin/env python3
"""Generate Lean exact-distance proofs from generic CSS/non-CSS certificates.

The generated theorem uses the complete symplectic stabilizer matrix and a
complete 2k logical quotient basis stored in the certificate.  Lean checks
commutation, ranks, basis non-degeneracy, the upper witness, and the exhaustive
distance lower bound through ``bv_decide``/LRAT.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


SUPPORTED = {
    "qldpc-css-matrix-exact",
    "qldpc-pbb-noncss-exact",
    "qldpc-noncss-matrix-exact",
}


BASIC_LEAN = r'''import Mathlib
import Std.Tactic.BVDecide

namespace QUniversal

def parityAt {width : Nat} (x : BitVec width) (support : List Nat) : Bool :=
  support.foldl (fun acc i => Bool.xor acc (x.getLsbD i)) false

/-- Symplectic pairing of a concrete support row with `[x|z]`. -/
def sympParityAt (n : Nat) (x : BitVec (2*n)) (support : List Nat) : Bool :=
  support.foldl (fun acc i =>
    Bool.xor acc (if i < n then x.getLsbD (n+i) else x.getLsbD (i-n))) false

def commutes (n : Nat) (rows : List (List Nat)) (x : BitVec (2*n)) : Bool :=
  rows.all (fun row => sympParityAt n x row == false)

def pairsAny (n : Nat) (duals : List (List Nat)) (x : BitVec (2*n)) : Bool :=
  duals.any (fun dual => sympParityAt n x dual == true)

def sympWeightAux (n : Nat) (x : BitVec (2*n)) : Nat -> BitVec 9
  | 0 => BitVec.ofNat 9 0
  | i + 1 =>
      sympWeightAux n x i +
        (BitVec.ofBool (x.getLsbD i || x.getLsbD (n+i))).zeroExtend 9

def sympWeight (n : Nat) (x : BitVec (2*n)) : BitVec 9 :=
  sympWeightAux n x n

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

def pairSupports (n : Nat) (a b : List Nat) : Bool :=
  a.foldl (fun acc i =>
    Bool.xor acc (if i < n then b.contains (n+i) else b.contains (i-n))) false

def pairingRowAux (n : Nat) (x : List Nat) :
    List (List Nat) -> Nat -> Nat
  | [], _ => 0
  | z :: zs, i =>
      (if pairSupports n x z then (1 <<< i) else 0) |||
        pairingRowAux n x zs (i + 1)

def pairingRows (n : Nat) (xs : List (List Nat)) : List Nat :=
  xs.map (fun x => pairingRowAux n x xs 0)

structure StabilizerCode (n : Nat) where
  checks : List (List Nat)
  logicals : List (List Nat)

def logicalDimension {n : Nat} (code : StabilizerCode n) : Nat :=
  n - rankF2 (4*n) (rowMasks code.checks)

def IsLogical {n : Nat} (code : StabilizerCode n) (x : BitVec (2*n)) : Bool :=
  commutes n code.checks x && pairsAny n code.logicals x

def BasisValid {n : Nat} (code : StabilizerCode n) : Prop :=
  code.checks.all (fun s =>
    code.checks.all (fun t => pairSupports n s t == false)) = true /\
  code.logicals.length = 2 * logicalDimension code /\
  code.logicals.all (fun s =>
    code.checks.all (fun t => pairSupports n s t == false)) = true /\
  rankF2 (4*n) (rowMasks (code.checks ++ code.logicals)) =
    rankF2 (4*n) (rowMasks code.checks) + 2 * logicalDimension code /\
  rankF2 (4*n) (pairingRows n code.logicals) =
    2 * logicalDimension code

instance {n : Nat} (code : StabilizerCode n) : Decidable (BasisValid code) := by
  unfold BasisValid
  infer_instance

def HasDistanceAtMost {n : Nat} (code : StabilizerCode n) (d : Nat) : Prop :=
  exists x, IsLogical code x = true /\
    sympWeight n x <= BitVec.ofNat 9 d

def HasDistanceAtLeast {n : Nat} (code : StabilizerCode n) (d : Nat) : Prop :=
  forall x, IsLogical code x = true ->
    BitVec.ofNat 9 d <= sympWeight n x

def HasExactDistance {n : Nat} (code : StabilizerCode n) (d : Nat) : Prop :=
  HasDistanceAtMost code d /\ HasDistanceAtLeast code d

structure VerifiedParameters {n : Nat}
    (code : StabilizerCode n) (k d : Nat) : Prop where
  blockFits : n < 512
  dimension : logicalDimension code = k
  basis : BasisValid code
  distance : HasExactDistance code d

end QUniversal
'''


def unpack_vector(record: dict[str, Any]) -> list[int]:
    length = int(record["length"])
    packed = bytes.fromhex(record["packed_hex"])
    expected = hashlib.sha256(f"{length}:".encode() + packed).hexdigest()
    if record.get("sha256") != expected:
        raise ValueError("packed vector SHA-256 mismatch")
    return [
        (packed[index // 8] >> (index % 8)) & 1
        for index in range(length)
    ]


def unpack_matrix(record: dict[str, Any]) -> list[list[int]]:
    rows, cols = int(record["rows"]), int(record["cols"])
    data = record["data"]
    if len(data) != rows:
        raise ValueError("packed matrix row count mismatch")
    matrix = [unpack_vector(row) for row in data]
    if any(len(row) != cols for row in matrix):
        raise ValueError("packed matrix width mismatch")
    return matrix


def symplectic_css_checks(
    hx: list[list[int]], hz: list[list[int]],
) -> list[list[int]]:
    n = len(hx[0]) if hx else len(hz[0])
    zero = [0] * n
    return [row + zero for row in hx] + [zero + row for row in hz]


def css_target(evidence: dict[str, Any], n: int) -> list[int]:
    target = unpack_vector(evidence["target_logical"])
    if len(target) != n:
        raise ValueError("CSS target logical width mismatch")
    zero = [0] * n
    if evidence["logical_type"] == "Z":
        return target + zero
    if evidence["logical_type"] == "X":
        return zero + target
    raise ValueError("unexpected CSS logical_type")


def css_witness(witness: dict[str, Any], n: int) -> list[int]:
    operator = unpack_vector(witness["operator"])
    if len(operator) != n:
        raise ValueError("CSS witness width mismatch")
    zero = [0] * n
    if witness["logical_type"] == "Z":
        return zero + operator
    if witness["logical_type"] == "X":
        return operator + zero
    raise ValueError("unexpected CSS witness logical_type")


def certificate_payload(certificate: dict[str, Any]) -> dict[str, Any]:
    certificate_type = certificate.get("certificate_type")
    if certificate_type not in SUPPORTED:
        raise ValueError(f"unsupported universal certificate: {certificate_type!r}")
    if certificate.get("passed") is not True:
        raise ValueError("unpassed certificate cannot produce a Lean theorem")
    claim = certificate["claim"]
    n, k, d = int(claim["n"]), int(claim["k"]), int(claim["d"])
    directions = certificate["milp"]["directions"]
    if certificate_type == "qldpc-css-matrix-exact":
        hx = unpack_matrix(claim["H_X"])
        hz = unpack_matrix(claim["H_Z"])
        checks = symplectic_css_checks(hx, hz)
        logicals = [css_target(item, n) for item in directions]
        witness = css_witness(certificate["upper_witness"], n)
    else:
        checks = unpack_matrix(claim["symplectic_stabilizer"])
        logicals = [unpack_vector(item["target_logical"]) for item in directions]
        witness = unpack_vector(certificate["upper_witness"]["operator"])
    if len(checks) == 0 or any(len(row) != 2 * n for row in checks):
        raise ValueError("symplectic check matrix dimensions mismatch")
    if len(logicals) != 2 * k or any(len(row) != 2 * n for row in logicals):
        raise ValueError("certificate does not contain a complete 2k logical basis")
    if len(witness) != 2 * n:
        raise ValueError("upper witness dimensions mismatch")
    return {
        "n": n,
        "k": k,
        "d": d,
        "checks": checks,
        "logicals": logicals,
        "witness": witness,
        "certificate_type": certificate_type,
        "certificate_sha256": certificate["certificate_sha256"],
    }


def support(vector: list[int]) -> list[int]:
    return [index for index, value in enumerate(vector) if value]


def lean_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_rows(rows: list[list[int]]) -> str:
    return "[\n    " + ",\n    ".join(
        lean_nat_list(support(row)) for row in rows
    ) + "\n  ]"


def bitmask(vector: list[int]) -> int:
    return sum(int(value) << index for index, value in enumerate(vector))


def safe_module(certificate: dict[str, Any], index: int) -> str:
    kind = re.sub(r"[^A-Za-z0-9]+", "_", certificate["certificate_type"])
    digest = str(certificate["certificate_sha256"])[:12]
    return f"Certificate_{index}_{kind}_{digest}"


def render_module(
    payload: dict[str, Any],
    module: str,
    *,
    sat_timeout: int,
) -> str:
    n, k, d = payload["n"], payload["k"], payload["d"]
    return f'''import QUniversal.Basic

/-! Exact parameters reconstructed from certificate {payload["certificate_sha256"]}. -/
namespace {module}
open QUniversal

def code : StabilizerCode {n} := {{
  checks := {lean_rows(payload["checks"])},
  logicals := {lean_rows(payload["logicals"])}
}}

def witness : BitVec (2*{n}) :=
  BitVec.ofNat (2*{n}) {bitmask(payload["witness"])}

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
  simp only [code, IsLogical, commutes, pairsAny, sympParityAt,
    sympWeight, sympWeightAux, List.all, List.any, List.foldl]
  bv_decide (config := {{ timeout := {sat_timeout} }})

theorem exact_parameters : VerifiedParameters code {k} {d} := by
  exact ⟨by decide, dimension_verified, basis_verified,
    And.intro distance_upper distance_lower⟩

end {module}
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--sat-timeout", type=int, default=10800)
    args = parser.parse_args()
    release = json.loads(args.manifest.read_text())
    args.out.mkdir(parents=True, exist_ok=True)
    lean_dir = args.out / "QUniversal"
    lean_dir.mkdir(parents=True, exist_ok=True)
    (lean_dir / "Basic.lean").write_text(BASIC_LEAN)
    modules: list[str] = []
    objectives: list[dict[str, Any]] = []
    for index, entry in enumerate(release.get("certificates", [])):
        certificate_path = args.manifest.parent / entry["file"]
        certificate = json.loads(certificate_path.read_text())
        if certificate.get("certificate_type") not in SUPPORTED:
            continue
        payload = certificate_payload(certificate)
        module = safe_module(certificate, index)
        (lean_dir / f"{module}.lean").write_text(
            render_module(payload, module, sat_timeout=args.sat_timeout)
        )
        modules.append(module)
        objectives.append({
            "index": module,
            "category": "quantum-ldpc/universal-exact-parameters",
            "lean_file": f"QUniversal/{module}.lean",
            "target_theorem": f"{module}.exact_parameters",
            "source": {
                "certificate": str(certificate_path),
                "certificate_sha256": payload["certificate_sha256"],
                "certificate_type": payload["certificate_type"],
                "n": payload["n"], "k": payload["k"], "d": payload["d"],
            },
        })
    (args.out / "QUniversal.lean").write_text(
        "import QUniversal.Basic\n"
        + "\n".join(f"import QUniversal.{module}" for module in modules)
        + "\n"
    )
    with (args.out / "objectives.jsonl").open("w") as stream:
        for row in objectives:
            stream.write(json.dumps(row, ensure_ascii=False) + "\n")
    print(f"Emitted {len(modules)} universal exact modules under {lean_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
