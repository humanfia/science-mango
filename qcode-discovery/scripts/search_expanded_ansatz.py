#!/usr/bin/env python3
"""Search a wider sparse CSS/BB ansatz with replayable fail-fast witnesses.

Unlike the original fixed 3+3 PBB subset search, this search samples CSS
bivariate bicycle codes with every sparse support split from 2+2 through 4+2
whose total check weight is at most six, and can mix several lattice shapes.
Every attempted MILP direction stores its operator and target logical, including
directions that disprove a candidate before full certification.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    _direction_specs,
    pack_vector,
    solve_css_direction,
    verify_css_witness,
)
from evaluation.certificate_dispatch import build_certificate, verify_certificate
from evaluation.distance_milp import get_code_matrices
from evaluation.final_gate import _connected, minimum_winning_distance
from evaluation.matrix_io import pack_matrix
from evaluation.registry import check_code_novelty


DEFAULT_SPLITS = ((2, 2), (2, 3), (3, 2), (2, 4), (4, 2), (3, 3))


def parse_term_splits(value: str) -> tuple[tuple[int, int], ...]:
    try:
        splits = tuple(
            tuple(int(part) for part in item.split("+"))
            for item in value.split(",")
        )
    except ValueError as exc:
        raise argparse.ArgumentTypeError("term splits must look like 2+2,3+3") from exc
    if (
        not splits
        or any(len(item) != 2 for item in splits)
        or any(a < 1 or b < 1 or a + b > 6 for a, b in splits)
    ):
        raise argparse.ArgumentTypeError("each support split must be positive and total at most 6")
    return splits


def parse_shapes(value: str) -> tuple[tuple[int, int], ...]:
    try:
        shapes = tuple(
            tuple(int(part) for part in item.lower().split("x"))
            for item in value.split(",")
        )
    except ValueError as exc:
        raise argparse.ArgumentTypeError("shapes must look like 6x6,9x6") from exc
    if (
        not shapes
        or any(len(item) != 2 for item in shapes)
        or any(ell < 2 or m < 2 for ell, m in shapes)
    ):
        raise argparse.ArgumentTypeError("each lattice shape must be at least 2x2")
    return shapes


def sample_css_claim(
    rng: np.random.Generator,
    shapes: tuple[tuple[int, int], ...],
    splits: tuple[tuple[int, int], ...],
    *,
    seed: int,
    trial: int,
) -> dict:
    ell, m = shapes[int(rng.integers(len(shapes)))]
    a_count, b_count = splits[int(rng.integers(len(splits)))]

    def terms(count: int) -> list[list[int]]:
        choices = rng.choice(ell * m, size=count, replace=False)
        return [[int(value // m), int(value % m)] for value in choices]

    return {
        "source": f"expanded-css-sparse seed={seed} trial={trial}",
        "ell": ell,
        "m": m,
        "A_terms": terms(a_count),
        "B_terms": terms(b_count),
    }


def candidate_key(claim: dict) -> tuple:
    return (
        int(claim["ell"]),
        int(claim["m"]),
        tuple(sorted(map(tuple, claim["A_terms"]))),
        tuple(sorted(map(tuple, claim["B_terms"]))),
    )


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shapes", type=parse_shapes, default=((6, 6), (9, 6), (12, 6)))
    parser.add_argument("--term-splits", type=parse_term_splits, default=DEFAULT_SPLITS)
    parser.add_argument("--trials", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260728)
    parser.add_argument("--timeout-per-logical", type=float, default=20)
    parser.add_argument("--total-timeout-per-code", type=float, default=300)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--output", type=Path,
        default=project / "results" / "expanded_ansatz_search.jsonl",
    )
    parser.add_argument(
        "--certificate-output", type=Path,
        default=project / "results" / "expanded_ansatz_certificate.json",
    )
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    seen: set[tuple] = set()
    stats = {
        "sampled": 0,
        "static_pass": 0,
        "basis_bound_pass": 0,
        "milp_attempted": 0,
        "exact": 0,
        "wins": 0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.certificate_output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with args.output.open("w") as stream:
        for trial in range(args.trials):
            claim = sample_css_claim(
                rng, args.shapes, args.term_splits, seed=args.seed, trial=trial,
            )
            key = candidate_key(claim)
            if key in seen:
                continue
            seen.add(key)
            stats["sampled"] += 1
            try:
                code = build_bb_code(
                    claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
                )
                hx, hz, lx, lz = (
                    np.asarray(value, dtype=np.uint8) & 1
                    for value in get_code_matrices(code)
                )
            except (TypeError, ValueError):
                continue
            n, k = int(code.num_qudits), int(code.dimension)
            if k <= 0 or len(lx) != k or len(lz) != k:
                continue
            support = np.vstack((hx, hz))
            connected, components = _connected(support)
            max_weight = int(support.sum(axis=1).max(initial=0))
            max_degree = int(support.sum(axis=0).max(initial=0))
            if not connected or max_weight > 6 or max_degree > 6:
                continue
            stats["static_pass"] += 1
            required_distance = minimum_winning_distance(n, k)
            basis_bound = min(
                int(row.sum()) for row in np.vstack((lx, lz))
            )
            if basis_bound < required_distance:
                continue
            stats["basis_bound_pass"] += 1
            stats["milp_attempted"] += 1
            directions = []
            exact = True
            code_started = time.monotonic()
            for logical_type, index, check_name, checks, target in _direction_specs(code):
                remaining = args.total_timeout_per_code - (
                    time.monotonic() - code_started
                )
                if remaining <= 0:
                    exact = False
                    break
                result = solve_css_direction(
                    checks, target,
                    timeout=min(args.timeout_per_logical, remaining),
                )
                direction = {
                    **result,
                    "logical_type": logical_type,
                    "logical_index": index,
                    "check_matrix": check_name,
                    "target_logical": pack_vector(target),
                }
                failures = verify_css_witness(direction, checks, target)
                direction["witness_verified"] = not failures
                direction["witness_failures"] = failures
                directions.append(direction)
                if result["objective"] is not None and result["objective"] < required_distance:
                    exact = False
                    break
                if not result["success"] or result["mip_gap"] != 0.0:
                    exact = False
                    break
            distance = min(
                (int(item["objective"]) for item in directions
                 if item["objective"] is not None),
                default=0,
            )
            exact = exact and len(directions) == 2 * k
            if exact:
                stats["exact"] += 1
            novelty = (
                check_code_novelty(code, code_type="css")
                if exact and distance >= required_distance
                else None
            )
            record = {
                "trial": trial,
                "ansatz": "css-sparse-bb",
                "claim": claim,
                "n": n,
                "k": k,
                "required_distance": required_distance,
                "basis_bound": basis_bound,
                "distance": distance,
                "exact": exact,
                "fom": k * distance * distance / n if distance else 0.0,
                "max_row_weight": max_weight,
                "max_qubit_degree": max_degree,
                "tanner_components": components,
                "novelty": novelty,
                "witnesses_self_contained": bool(directions) and all(
                    item.get("witness_verified") is True for item in directions
                ),
                "directions": directions,
            }
            stream.write(json.dumps(record) + "\n")
            stream.flush()
            if exact and record["fom"] > 12 and novelty and novelty["novel"]:
                stats["wins"] += 1
                matrix_claim = {
                    "source": claim["source"],
                    "H_X": pack_matrix(hx),
                    "H_Z": pack_matrix(hz),
                }
                certificate = build_certificate(
                    matrix_claim,
                    known_answer_artifact=args.known_answer_artifact,
                    timeout_per_logical=args.timeout_per_logical,
                    total_timeout=args.total_timeout_per_code,
                )
                verification = verify_certificate(
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
        "ansatz": {
            "family": "css-sparse-bb",
            "shapes": args.shapes,
            "term_splits": args.term_splits,
        },
        "stats": stats,
        "output": str(args.output),
    }, indent=2))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
