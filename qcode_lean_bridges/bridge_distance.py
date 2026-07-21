#!/usr/bin/env python3
"""Generate Lean-checked CSS distance-upper-bound certificates for BB codes.

The search side is intentionally untrusted.  It may use SciPy/HiGHS to find a
low-weight logical operator, but the generated Lean theorem independently
checks its weight, zero syndrome, and odd pairing with a dual vector.  The odd
pairing proves that the operator is outside the relevant stabilizer row space.

Typical usage (the qcode-discovery venv provides NumPy/SciPy)::

    /root/proposal_for_physic/qcode-discovery/.venv/bin/python \
      bridge_distance.py \
      --catalog /root/proposal_for_physic/qcode-discovery/results/ilp_catalog.json \
      --out qcode_distance_bridge

Use ``--witnesses FILE`` to reuse a JSONL cache.  Newly found certificates are
appended atomically after each code, so an interrupted batch can be resumed.
Only labels containing a distance component (``[[n,k,<=d]]`` or ``[[n,k,d]]``)
are emitted by default.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
import time
from pathlib import Path
from typing import Iterable

from kmask import hx_hz_rows, rows_to_masks


LABEL_RE = re.compile(
    r"\[\[\s*(\d+)\s*,\s*(\d+)\s*,\s*(?:<=|≤)?\s*(\d+)\s*\]\]"
)


def safe_ident(label: str, ell: int, m: int, idx: int) -> str:
    core = re.sub(r"[^0-9]+", "_", label).strip("_")
    return f"Code_{core}_l{ell}m{m}_{idx}"


def label_bound(label: str) -> tuple[int, int, int] | None:
    match = LABEL_RE.search(label)
    if not match:
        return None
    return tuple(map(int, match.groups()))


def parity(mask: int) -> int:
    return mask.bit_count() & 1


def orthogonal(rows: Iterable[int], vector: int) -> bool:
    return all(parity(row & vector) == 0 for row in rows)


def insert_basis(basis: dict[int, int], value: int) -> bool:
    """Insert into an RREF-like F2 bitmask basis; return independence."""
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot]
    if not value:
        return False
    pivot = value.bit_length() - 1
    for other, row in list(basis.items()):
        if (row >> pivot) & 1:
            basis[other] = row ^ value
    basis[pivot] = value
    return True


def row_basis(rows: Iterable[int]) -> dict[int, int]:
    basis: dict[int, int] = {}
    for row in rows:
        insert_basis(basis, int(row))
    return basis


def nullspace_basis(rows: Iterable[int], n: int) -> list[int]:
    """Return an F2 nullspace basis for a bitmask row matrix."""
    basis = row_basis(rows)
    pivots = set(basis)
    result: list[int] = []
    for free in range(n):
        if free in pivots:
            continue
        vector = 1 << free
        for pivot, row in basis.items():
            if (row >> free) & 1:
                vector |= 1 << pivot
        result.append(vector)
    return result


def quotient_basis(kernel_rows: Iterable[int], subspace_rows: Iterable[int]) -> list[int]:
    """Extend ``subspace_rows`` by kernel vectors and return quotient reps."""
    basis = row_basis(subspace_rows)
    result: list[int] = []
    for vector in kernel_rows:
        if insert_basis(basis, vector):
            result.append(vector)
    return result


def logical_bases(hx: list[int], hz: list[int], n: int) -> tuple[list[int], list[int]]:
    # X logicals live in ker(Hz) / row(Hx); Z logicals are the counterpart.
    lx = quotient_basis(nullspace_basis(hz, n), hx)
    lz = quotient_basis(nullspace_basis(hx, n), hz)
    return lx, lz


def verify_certificate(
    logical_type: str,
    witness: int,
    dual: int,
    target: int,
    hx: list[int],
    hz: list[int],
    n: int,
) -> None:
    if logical_type not in {"X", "Z"}:
        raise ValueError(f"unknown logical type: {logical_type}")
    if witness < 0 or dual < 0 or witness.bit_length() > n or dual.bit_length() > n:
        raise ValueError("certificate has bits outside the code block")
    checks, dual_checks = (hz, hx) if logical_type == "X" else (hx, hz)
    failures = []
    if witness.bit_count() > target:
        failures.append(f"weight {witness.bit_count()} > target {target}")
    if not orthogonal(checks, witness):
        failures.append("witness has nonzero stabilizer syndrome")
    if not orthogonal(dual_checks, dual):
        failures.append("dual has nonzero stabilizer syndrome")
    if parity(witness & dual) != 1:
        failures.append("witness and dual do not pair oddly")
    if failures:
        raise ValueError("; ".join(failures))


def cheap_witness(
    lx: list[int], lz: list[int], target: int
) -> tuple[str, int, int] | None:
    for logical_type, candidates, duals in (("X", lx, lz), ("Z", lz, lx)):
        for witness in sorted(candidates, key=int.bit_count):
            if witness.bit_count() > target:
                continue
            for dual in duals:
                if parity(witness & dual):
                    return logical_type, witness, dual
    return None


def milp_witness(
    check_rows: list[int],
    dual: int,
    n: int,
    target: int,
    timeout: float,
) -> int | None:
    """Find a vector of weight <= target, orthogonal to checks, odd with dual."""
    try:
        import numpy as np
        from scipy.optimize import Bounds, LinearConstraint, milp
        from scipy.sparse import lil_matrix
    except ImportError as exc:
        raise RuntimeError(
            "witness search needs NumPy/SciPy; run with qcode-discovery/.venv/bin/python "
            "or pass a populated --witnesses cache"
        ) from exc

    m = len(check_rows)
    num_vars = n + m + 1
    matrix = lil_matrix((m + 2, num_vars), dtype=float)
    for r, mask in enumerate(check_rows):
        for j in range(n):
            if (mask >> j) & 1:
                matrix[r, j] = 1
        matrix[r, n + r] = -2
    for j in range(n):
        if (dual >> j) & 1:
            matrix[m, j] = 1
    matrix[m, n + m] = -2
    # Explicit upper-bound constraint often finds an incumbent much faster.
    matrix[m + 1, :n] = 1

    lower = np.zeros(m + 2)
    upper = np.zeros(m + 2)
    lower[m] = upper[m] = 1
    lower[m + 1] = 0
    upper[m + 1] = target

    lb = np.zeros(num_vars)
    ub = np.ones(num_vars)
    for r, mask in enumerate(check_rows):
        ub[n + r] = math.ceil(mask.bit_count() / 2)
    ub[n + m] = math.ceil(dual.bit_count() / 2)

    objective = np.zeros(num_vars)
    objective[:n] = 1
    options = {"presolve": True}
    if timeout > 0:
        options["time_limit"] = timeout
    result = milp(
        c=objective,
        constraints=LinearConstraint(matrix.tocsr(), lower, upper),
        integrality=np.ones(num_vars),
        bounds=Bounds(lb, ub),
        options=options,
    )
    if result.x is None:
        return None
    mask = 0
    for j, value in enumerate(result.x[:n]):
        if value > 0.5:
            mask |= 1 << j
    return mask


def find_witness(
    hx: list[int], hz: list[int], n: int, target: int, timeout: float
) -> tuple[str, int, int]:
    lx, lz = logical_bases(hx, hz, n)
    if len(lx) != len(lz) or not lx:
        raise ValueError(f"invalid logical bases: dim X={len(lx)}, dim Z={len(lz)}")

    cheap = cheap_witness(lx, lz, target)
    if cheap is not None:
        return cheap

    started = time.monotonic()
    for logical_type, checks, duals in (("X", hz, lz), ("Z", hx, lx)):
        for dual in sorted(duals, key=int.bit_count):
            elapsed = time.monotonic() - started
            remaining = timeout - elapsed if timeout > 0 else 0
            if timeout > 0 and remaining <= 0:
                break
            per_solve = min(remaining, max(2.0, timeout / max(1, len(lx)))) if timeout > 0 else 0
            witness = milp_witness(checks, dual, n, target, per_solve)
            if witness is not None:
                return logical_type, witness, dual
    raise RuntimeError(f"no weight <= {target} logical witness found within {timeout}s")


def iter_codes(catalog: dict):
    idx = 0
    for group, records in catalog.items():
        if not isinstance(records, list):
            continue
        for code in records:
            if isinstance(code, dict) and all(k in code for k in ("A", "B", "ell", "m", "label")):
                yield idx, group, code
                idx += 1


def fingerprint(code: dict) -> str:
    payload = {
        "label": code["label"], "ell": code["ell"], "m": code["m"],
        "A": code["A"], "B": code["B"],
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def load_witnesses(path: Path) -> dict[str, dict]:
    result: dict[str, dict] = {}
    if not path.exists():
        return result
    with path.open() as stream:
        for line_no, line in enumerate(stream, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if "fingerprint" not in row:
                raise ValueError(f"{path}:{line_no}: missing fingerprint")
            result[row["fingerprint"]] = row
    return result


def append_witness(path: Path, row: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as stream:
        stream.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


BASIC_LEAN = r'''import Mathlib

namespace QDistance

abbrev F2 := ZMod 2
abbrev Vec (n : Nat) := Fin n → F2

def inner {n : Nat} (x y : Vec n) : F2 := ∑ i, x i * y i

def weight {n : Nat} (x : Vec n) : Nat :=
  (Finset.univ.filter fun i => x i ≠ 0).card

def ofMask (n mask : Nat) : Vec n := fun i =>
  if mask.testBit i then 1 else 0

abbrev Term := Nat × Nat

/-- Entry (i,j) of the group-circulant matrix generated by a polynomial support. -/
def circEntry (ell m : Nat) (poly : List Term) (i j : Nat) : F2 :=
  if poly.any (fun t =>
      ((j / m + ell - i / m) % ell == t.1 % ell) &&
      ((j % m + m - i % m) % m == t.2 % m)) then 1 else 0

/-- H_X = [circ A | circ B], constructed inside Lean from A and B. -/
def hxRows (ell m : Nat) (A B : List Term) : List (Vec (2 * (ell * m))) :=
  (List.range (ell * m)).map fun i j =>
    if j.val < ell * m then circEntry ell m A i j.val
    else circEntry ell m B i (j.val - ell * m)

/-- H_Z = [circ B^T | circ A^T], constructed inside Lean from A and B. -/
def hzRows (ell m : Nat) (A B : List Term) : List (Vec (2 * (ell * m))) :=
  (List.range (ell * m)).map fun i j =>
    if j.val < ell * m then circEntry ell m B j.val i
    else circEntry ell m A (j.val - ell * m) i

def orthogonal {n : Nat} (rows : List (Vec n)) (x : Vec n) : Prop :=
  rows.all (fun r => inner r x == 0) = true

instance {n : Nat} (rows : List (Vec n)) (x : Vec n) :
    Decidable (orthogonal rows x) := by
  unfold orthogonal
  infer_instance

def rowSpace {n : Nat} (rows : List (Vec n)) : Submodule F2 (Vec n) :=
  Submodule.span F2 {r | r ∈ rows}

structure CSSCode (n : Nat) where
  hx : List (Vec n)
  hz : List (Vec n)

def IsXLogical {n : Nat} (code : CSSCode n) (x : Vec n) : Prop :=
  orthogonal code.hz x ∧ x ∉ rowSpace code.hx

def IsZLogical {n : Nat} (code : CSSCode n) (z : Vec n) : Prop :=
  orthogonal code.hx z ∧ z ∉ rowSpace code.hz

/-- Semantic statement `distance(code) ≤ d`. -/
def HasDistanceAtMost {n : Nat} (code : CSSCode n) (d : Nat) : Prop :=
  ∃ v, weight v ≤ d ∧ (IsXLogical code v ∨ IsZLogical code v)

def dotRight {n : Nat} (dual : Vec n) : Vec n →ₗ[F2] F2 where
  toFun x := inner x dual
  map_add' x y := by simp [inner, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [inner, Finset.mul_sum, mul_assoc]

theorem not_mem_rowSpace_of_pair {n : Nat} {rows : List (Vec n)}
    {x dual : Vec n} (hdual : orthogonal rows dual)
    (hpair : inner x dual ≠ 0) : x ∉ rowSpace rows := by
  intro hx
  have hle : rowSpace rows ≤ LinearMap.ker (dotRight dual) := by
    apply Submodule.span_le.2
    intro r hr
    change inner r dual = 0
    exact beq_iff_eq.mp (List.all_eq_true.mp hdual r hr)
  have hxker := hle hx
  change inner x dual = 0 at hxker
  exact hpair hxker

theorem distanceUpperOfX {n d : Nat} (code : CSSCode n) (x dual : Vec n)
    (hweight : weight x ≤ d) (hcommute : orthogonal code.hz x)
    (hdual : orthogonal code.hx dual) (hpair : inner x dual ≠ 0) :
    HasDistanceAtMost code d := by
  refine ⟨x, hweight, Or.inl ⟨hcommute, ?_⟩⟩
  exact not_mem_rowSpace_of_pair hdual hpair

theorem distanceUpperOfZ {n d : Nat} (code : CSSCode n) (z dual : Vec n)
    (hweight : weight z ≤ d) (hcommute : orthogonal code.hx z)
    (hdual : orthogonal code.hz dual) (hpair : inner z dual ≠ 0) :
    HasDistanceAtMost code d := by
  refine ⟨z, hweight, Or.inr ⟨hcommute, ?_⟩⟩
  exact not_mem_rowSpace_of_pair hdual hpair

end QDistance
'''


LEAN_TEMPLATE = r'''import QDistance.Basic

/-!
# Distance upper bound for BB code {label}

The untrusted search phase supplied an explicit weight-{weight} {logical_type}-type
logical operator.  Lean checks its syndrome, weight, and odd pairing with a dual
operator, which proves that it is not a stabilizer.
-/

namespace {module}

open QDistance

def A : List Term := {a_terms}
def B : List Term := {b_terms}
def Hx : List (Vec {n}) := hxRows {ell} {m} A B
def Hz : List (Vec {n}) := hzRows {ell} {m} A B
def code : CSSCode {n} := {{ hx := Hx, hz := Hz }}

def witness : Vec {n} := ofMask {n} {witness}
def dual : Vec {n} := ofMask {n} {dual}

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1000000 in
/-- Lean-checked upper bound: this CSS code has distance at most {target}. -/
theorem distance_upper : HasDistanceAtMost code {target} := by
  apply distanceUpperOf{logical_type} code witness dual
  all_goals {decision_tactic}

end {module}
'''


def render_masks(masks: list[int], n: int) -> str:
    return "[" + ", ".join(f"ofMask {n} {mask}" for mask in masks) + "]"


def render_lean(
    code: dict, module: str, target: int, logical_type: str,
    witness: int, dual: int, hx: list[int], hz: list[int], n: int,
    decision_tactic: str,
) -> str:
    return LEAN_TEMPLATE.format(
        label=code["label"], module=module, n=n, target=target,
        logical_type=logical_type, weight=witness.bit_count(),
        witness=witness, dual=dual, ell=code["ell"], m=code["m"],
        decision_tactic=decision_tactic,
        a_terms="[" + ", ".join(f"({a}, {b})" for a, b in code["A"]) + "]",
        b_terms="[" + ", ".join(f"({a}, {b})" for a, b in code["B"]) + "]",
    )


def objective_row(code: dict, module: str, lib: str, target: int, cert: dict) -> dict:
    return {
        "index": module,
        "category": "quantum-ldpc/distance-upper-bound",
        "question": (
            f"For the bivariate-bicycle CSS code {code['label']}, verify the explicit "
            f"weight-{cert['weight']} {cert['logical_type']}-logical certificate and "
            f"prove that the code distance is at most {target}."
        ),
        "lean_file": f"{lib}/{module}.lean",
        "target_theorem": f"{module}.distance_upper",
        "source": {
            "dataset": "qcode-discovery/ilp_catalog",
            "label": code["label"], "ell": code["ell"], "m": code["m"],
            "A_terms": code["A"], "B_terms": code["B"],
            "distance_upper": target,
            "certificate": {
                "logical_type": cert["logical_type"],
                "weight": cert["weight"],
                "witness_mask": cert["witness_mask"],
                "dual_mask": cert["dual_mask"],
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--catalog", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--lib-name", default="QDistance")
    parser.add_argument("--witnesses", type=Path,
                        help="JSONL witness cache (default: <out>/distance_witnesses.jsonl)")
    parser.add_argument("--timeout", type=float, default=300,
                        help="Maximum search time per code in seconds (default: 300)")
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument(
        "--target-field", choices=("label", "ilp_d"), default="label",
        help="Distance target source: parse the label (default), or use catalog ilp_d",
    )
    parser.add_argument("--kernel-decide", action="store_true",
                        help="Use pure kernel decide (much slower for n=360) instead of native_decide")
    parser.add_argument("--skip-missing", action="store_true",
                        help="Skip codes whose witness search times out instead of failing")
    args = parser.parse_args()

    catalog = json.loads(args.catalog.read_text())
    witness_path = args.witnesses or (args.out / "distance_witnesses.jsonl")
    cached = load_witnesses(witness_path)
    lean_dir = args.out / args.lib_name
    lean_dir.mkdir(parents=True, exist_ok=True)
    (lean_dir / "Basic.lean").write_text(BASIC_LEAN)

    modules: list[str] = []
    objectives: list[dict] = []
    skipped_no_bound = 0
    skipped_search = 0

    for idx, _group, code in iter_codes(catalog):
        n = 2 * int(code["ell"]) * int(code["m"])
        if args.target_field == "ilp_d":
            if code.get("ilp_d") is None:
                skipped_no_bound += 1
                continue
            target = int(code["ilp_d"])
        else:
            bound = label_bound(code["label"])
            if bound is None:
                skipped_no_bound += 1
                continue
            n_label, _k_label, target = bound
            if n != n_label:
                raise ValueError(f"{code['label']}: label n={n_label}, computed n={n}")
        if args.limit and len(modules) >= args.limit:
            break

        matrix_hx, matrix_hz = hx_hz_rows(
            [tuple(t) for t in code["A"]], [tuple(t) for t in code["B"]],
            int(code["ell"]), int(code["m"]),
        )
        hx, hz = rows_to_masks(matrix_hx), rows_to_masks(matrix_hz)
        key = fingerprint(code)
        cert = cached.get(key)
        if cert is None:
            print(f"search {code['label']} (target <= {target})", flush=True)
            try:
                logical_type, witness, dual = find_witness(hx, hz, n, target, args.timeout)
            except RuntimeError as exc:
                if args.skip_missing:
                    print(f"  SKIP: {exc}", file=sys.stderr, flush=True)
                    skipped_search += 1
                    continue
                raise
            cert = {
                "fingerprint": key,
                "label": code["label"],
                "logical_type": logical_type,
                "witness_mask": witness,
                "dual_mask": dual,
                "weight": witness.bit_count(),
                "target": target,
            }
            verify_certificate(logical_type, witness, dual, target, hx, hz, n)
            append_witness(witness_path, cert)
            cached[key] = cert
            print(f"  found {logical_type} witness, weight={witness.bit_count()}", flush=True)
        else:
            verify_certificate(
                cert["logical_type"], int(cert["witness_mask"]), int(cert["dual_mask"]),
                target, hx, hz, n,
            )

        # The witness can establish a strictly tighter bound than the
        # discovery-stage incumbent. State the strongest checked claim.
        proved_target = min(target, int(cert["weight"]))

        module = safe_ident(code["label"], int(code["ell"]), int(code["m"]), idx)
        (lean_dir / f"{module}.lean").write_text(render_lean(
            code, module, proved_target, cert["logical_type"],
            int(cert["witness_mask"]), int(cert["dual_mask"]), hx, hz, n,
            "decide" if args.kernel_decide else "native_decide",
        ))
        modules.append(module)
        objectives.append(objective_row(code, module, args.lib_name, proved_target, cert))

    imports = [f"import {args.lib_name}.Basic"]
    imports.extend(f"import {args.lib_name}.{module}" for module in modules)
    (args.out / f"{args.lib_name}.lean").write_text("\n".join(imports) + "\n")
    with (args.out / "objectives.jsonl").open("w") as stream:
        for row in objectives:
            stream.write(json.dumps(row, ensure_ascii=False) + "\n")

    print(f"Emitted {len(modules)} Lean distance certificates under {lean_dir}")
    print(f"Witness cache: {witness_path}")
    print(f"Skipped: {skipped_no_bound} labels without d, {skipped_search} search failures")


if __name__ == "__main__":
    main()
