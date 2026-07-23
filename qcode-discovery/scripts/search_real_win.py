#!/usr/bin/env python3
"""Targeted fail-fast search for a fully certifiable PBB challenge win.

The perturbations are sampled as subsets of the base A/B supports.  This
preserves Pauli check weight six by construction; every candidate is then
checked for degree, connectivity, dimension, a logical-basis upper bound,
and exact per-direction MILP distance in that order.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.final_gate import _connected
from evaluation.noncss_certificate import (
    build_noncss_certificate,
    solve_symplectic_direction,
    verify_noncss_certificate,
)
from evaluation.pbb_code import (
    build_pbb_code,
    get_symplectic_logicals,
    symplectic_weight,
)
from evaluation.registry import check_code_novelty


def _terms(rng: np.random.Generator, ell: int, m: int, count: int) -> list[list[int]]:
    choices = rng.choice(ell * m, size=count, replace=False)
    return [[int(value // m), int(value % m)] for value in choices]


def _subset(rng: np.random.Generator, terms: list[list[int]]) -> list[list[int]]:
    count = int(rng.integers(1, len(terms)))
    indices = rng.choice(len(terms), size=count, replace=False)
    return [terms[int(index)] for index in sorted(indices)]


def _candidate_key(claim: dict) -> tuple:
    return tuple(
        tuple(sorted(map(tuple, claim[name])))
        for name in ("A_terms", "B_terms", "C_terms", "D_terms")
    )


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ell", type=int, default=6)
    parser.add_argument("--m", type=int, default=6)
    parser.add_argument("--trials", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20260723)
    parser.add_argument("--timeout-per-logical", type=float, default=20)
    parser.add_argument("--total-timeout-per-code", type=float, default=300)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--output", type=Path,
        default=project / "results" / "real_win_search.jsonl",
    )
    parser.add_argument(
        "--certificate-output", type=Path,
        default=project / "results" / "real_win_certificate.json",
    )
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    seen: set[tuple] = set()
    stats = {
        "sampled": 0,
        "commuting": 0,
        "static_pass": 0,
        "basis_bound_pass": 0,
        "milp_attempted": 0,
        "exact": 0,
        "wins": 0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with args.output.open("w") as stream:
        for trial in range(args.trials):
            claim = {
                "source": f"targeted-subset-search seed={args.seed} trial={trial}",
                "ell": args.ell,
                "m": args.m,
                "A_terms": _terms(rng, args.ell, args.m, 3),
                "B_terms": _terms(rng, args.ell, args.m, 3),
            }
            claim["C_terms"] = _subset(rng, claim["A_terms"])
            claim["D_terms"] = _subset(rng, claim["B_terms"])
            key = _candidate_key(claim)
            if key in seen:
                continue
            seen.add(key)
            stats["sampled"] += 1
            try:
                code = build_pbb_code(**{
                    name: claim[name]
                    for name in ("ell", "m", "A_terms", "B_terms", "C_terms", "D_terms")
                })
            except ValueError:
                continue
            stats["commuting"] += 1
            stabilizer = np.asarray(code.matrix, dtype=np.uint8) & 1
            n, k = int(code.num_qudits), int(code.dimension)
            if k <= 0:
                continue
            support = stabilizer[:, :n] | stabilizer[:, n:]
            connected, components = _connected(support)
            max_weight = int(support.sum(axis=1).max(initial=0))
            max_degree = int(support.sum(axis=0).max(initial=0))
            if not connected or max_weight > 6 or max_degree > 6:
                continue
            stats["static_pass"] += 1
            required_distance = math.floor(math.sqrt(12 * n / k)) + 1
            logicals = get_symplectic_logicals(code)
            if logicals.shape != (2 * k, 2 * n):
                continue
            basis_bound = min(symplectic_weight(row) for row in logicals)
            if basis_bound < required_distance:
                continue
            stats["basis_bound_pass"] += 1
            stats["milp_attempted"] += 1
            directions = []
            exact = True
            code_started = time.monotonic()
            for index, target in enumerate(logicals):
                remaining = args.total_timeout_per_code - (
                    time.monotonic() - code_started
                )
                if remaining <= 0:
                    exact = False
                    break
                result = solve_symplectic_direction(
                    stabilizer, target,
                    timeout=min(args.timeout_per_logical, remaining),
                )
                directions.append({
                    "logical_index": index,
                    "objective": result["objective"],
                    "success": result["success"],
                    "status": result["status"],
                    "mip_gap": result["mip_gap"],
                    "mip_dual_bound": result["mip_dual_bound"],
                    "elapsed_s": result["elapsed_s"],
                })
                if result["objective"] is not None and result["objective"] < required_distance:
                    exact = False
                    break
                if not result["success"] or result["mip_gap"] != 0.0:
                    exact = False
                    break
            distance = min(
                (item["objective"] for item in directions if item["objective"] is not None),
                default=0,
            )
            if exact and len(directions) == 2 * k:
                stats["exact"] += 1
            novelty = (
                check_code_novelty(code, code_type="noncss")
                if exact and distance >= required_distance
                else None
            )
            record = {
                "trial": trial,
                "claim": claim,
                "n": n,
                "k": k,
                "required_distance": required_distance,
                "basis_bound": basis_bound,
                "distance": distance,
                "exact": exact and len(directions) == 2 * k,
                "fom": k * distance * distance / n if distance else 0.0,
                "max_row_weight": max_weight,
                "max_qubit_degree": max_degree,
                "tanner_components": components,
                "novelty": novelty,
                "directions": directions,
            }
            stream.write(json.dumps(record) + "\n")
            stream.flush()
            if (
                record["exact"]
                and record["fom"] > 12
                and novelty is not None
                and novelty["novel"]
            ):
                stats["wins"] += 1
                certificate = build_noncss_certificate(
                    claim,
                    known_answer_artifact=args.known_answer_artifact,
                    timeout_per_logical=args.timeout_per_logical,
                    total_timeout=args.total_timeout_per_code,
                )
                verification = verify_noncss_certificate(
                    certificate,
                    known_answer_artifact=args.known_answer_artifact,
                    rerun_milp=True,
                    timeout_per_logical=args.timeout_per_logical,
                )
                args.certificate_output.write_text(
                    json.dumps(certificate, indent=2) + "\n"
                )
                print(json.dumps({
                    "status": "WIN",
                    "trial": trial,
                    "n": n,
                    "k": k,
                    "d": distance,
                    "fom": record["fom"],
                    "certificate": str(args.certificate_output),
                    "independently_verified": verification["passed"],
                    "stats": stats,
                }, indent=2))
                return 0 if certificate["passed"] and verification["passed"] else 2
    print(json.dumps({
        "status": "NO_WIN",
        "elapsed_s": time.monotonic() - started,
        "stats": stats,
        "output": str(args.output),
    }, indent=2))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
