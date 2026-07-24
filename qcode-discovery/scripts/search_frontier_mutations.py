#!/usr/bin/env python3
"""Mutate certified-frontier near misses and retain replayable MILP witnesses."""

from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    _direction_specs,
    pack_vector,
    solve_css_direction,
    verify_css_witness,
)
from evaluation.distance_milp import get_code_matrices
from evaluation.final_gate import _connected, minimum_winning_distance
from evaluation.registry import check_code_novelty


FRONTIER_SEEDS = (
    {
        "label": "near-miss-193",
        "ell": 12, "m": 12,
        "A_terms": [[3, 0], [2, 0], [0, 7]],
        "B_terms": [[0, 3], [3, 1], [2, 0]],
    },
    {
        "label": "near-miss-2085",
        "ell": 12, "m": 12,
        "A_terms": [[1, 1], [0, 2], [1, 8]],
        "B_terms": [[0, 3], [3, 2], [2, 0]],
    },
    {
        "label": "d16-trial-641",
        "ell": 12, "m": 12,
        "A_terms": [[1, 1], [2, 3], [1, 8]],
        "B_terms": [[0, 3], [3, 2], [1, 1]],
    },
    {
        "label": "d16-trial-2788",
        "ell": 12, "m": 12,
        "A_terms": [[3, 0], [2, 0], [8, 11]],
        "B_terms": [[0, 3], [3, 1], [2, 0]],
    },
    {
        "label": "pareto-72-12-6",
        "ell": 6, "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
    },
    {
        "label": "pareto-90-8-10",
        "ell": 15, "m": 3,
        "A_terms": [[9, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 0], [2, 0], [7, 0]],
    },
    {
        "label": "pareto-108-8-10",
        "ell": 9, "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
    },
    {
        "label": "pareto-108-d10-trial-110",
        "ell": 9, "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [4, 0], [2, 0]],
    },
    {
        # Historical BP-OSD/MILP incumbent [[360,12,<=24]].  The registry
        # contains this representative, so only structurally novel mutations
        # can advance.  Its challenge threshold is d>=19, leaving more search
        # margin than the exact small-n Pareto seeds.
        "label": "frontier-360-12-24",
        "ell": 30, "m": 6,
        "A_terms": [[9, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [25, 0], [26, 0]],
    },
)


def candidate_key(claim: dict[str, Any]) -> tuple:
    return (
        int(claim["ell"]), int(claim["m"]),
        tuple(sorted(map(tuple, claim["A_terms"]))),
        tuple(sorted(map(tuple, claim["B_terms"]))),
    )


def mutate_seed(
    rng: np.random.Generator,
    seed: dict[str, Any],
    *,
    radius: int,
    max_edits: int,
) -> dict[str, Any]:
    ell, m = int(seed["ell"]), int(seed["m"])
    a_terms = [list(term) for term in seed["A_terms"]]
    b_terms = [list(term) for term in seed["B_terms"]]
    blocks = (a_terms, b_terms)
    for _ in range(int(rng.integers(1, max_edits + 1))):
        block = blocks[int(rng.integers(2))]
        index = int(rng.integers(len(block)))
        dx = int(rng.integers(-radius, radius + 1))
        dy = int(rng.integers(-radius, radius + 1))
        if dx == 0 and dy == 0:
            dx = 1
        block[index] = [
            (block[index][0] + dx) % ell,
            (block[index][1] + dy) % m,
        ]
    return {
        "ell": ell, "m": m,
        "A_terms": a_terms, "B_terms": b_terms,
        "parent": seed["label"],
    }


def build_pool(
    *,
    trials: int,
    seed_value: int,
    radius: int,
    max_edits: int,
    min_k: int,
    parents: tuple[str, ...] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    rng = np.random.default_rng(seed_value)
    seeds = tuple(
        seed for seed in FRONTIER_SEEDS
        if parents is None or seed["label"] in parents
    )
    if not seeds:
        raise ValueError("parent filter selected no frontier seeds")
    seed_keys = {candidate_key(seed) for seed in seeds}
    seen = set(seed_keys)
    seen_digests: set[str] = set()
    pool: list[dict[str, Any]] = []
    stats = {
        "sampled": 0, "unique": 0, "positive_k": 0,
        "static_pass": 0, "basis_pass": 0, "novel": 0,
    }
    for trial in range(trials):
        claim = mutate_seed(
            rng, seeds[trial % len(seeds)],
            radius=radius, max_edits=max_edits,
        )
        if (
            len(set(map(tuple, claim["A_terms"]))) != len(claim["A_terms"])
            or len(set(map(tuple, claim["B_terms"]))) != len(claim["B_terms"])
        ):
            continue
        stats["sampled"] += 1
        key = candidate_key(claim)
        if key in seen:
            continue
        seen.add(key)
        stats["unique"] += 1
        try:
            code = build_bb_code(
                claim["ell"], claim["m"],
                claim["A_terms"], claim["B_terms"],
            )
        except (TypeError, ValueError):
            continue
        n, k = int(code.num_qudits), int(code.dimension)
        if k < min_k:
            continue
        stats["positive_k"] += 1
        hx, hz = (
            np.asarray(value, dtype=np.uint8) & 1
            for value in (code.matrix_x, code.matrix_z)
        )
        support = np.vstack((hx, hz))
        connected, components = _connected(support)
        if (
            not connected
            or int(support.sum(axis=1).max(initial=0)) > 6
            or int(support.sum(axis=0).max(initial=0)) > 6
        ):
            continue
        stats["static_pass"] += 1
        novelty = check_code_novelty(code, code_type="css")
        if novelty.get("novel") is not True:
            continue
        digest = str(novelty.get("canonical_digest"))
        if digest in seen_digests:
            continue
        seen_digests.add(digest)

        # Logical-basis construction is substantially more expensive than the
        # static and novelty gates, especially at n=360.  Delay it until known
        # and within-run equivalent candidates have already been discarded.
        _, _, lx, lz = get_code_matrices(code)
        required = minimum_winning_distance(n, k)
        basis_bound = min(
            int(row.sum()) for row in np.vstack((lx, lz)) if row.any()
        )
        if basis_bound < required:
            continue
        stats["basis_pass"] += 1
        stats["novel"] += 1
        pool.append({
            "trial": trial,
            "source": (
                f"frontier-mutation seed={seed_value} trial={trial} "
                f"parent={claim['parent']}"
            ),
            **claim,
            "n": n, "k": k,
            "required_distance": required,
            "basis_bound": basis_bound,
            "tanner_components": components,
            "novelty": novelty,
        })
    pool.sort(
        key=lambda row: (
            int(row["k"]),
            float(row["basis_bound"]) / int(row["required_distance"]),
        ),
        reverse=True,
    )
    return pool, stats


def screen_first_direction(payload: tuple[dict[str, Any], float]) -> dict[str, Any]:
    claim, timeout = payload
    code = build_bb_code(
        claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
    )
    logical_type, index, check_name, checks, target = _direction_specs(code)[0]
    result = solve_css_direction(checks, target, timeout=timeout)
    evidence = {
        **result,
        "logical_type": logical_type,
        "logical_index": index,
        "check_matrix": check_name,
        "target_logical": pack_vector(target),
    }
    failures = verify_css_witness(evidence, checks, target)
    evidence["witness_verified"] = not failures
    evidence["witness_failures"] = failures
    objective = evidence.get("objective")
    return {
        **claim,
        "screen": "first-logical-direction",
        "rejected": (
            objective is not None
            and int(objective) < int(claim["required_distance"])
            and not failures
        ),
        "unresolved": (
            objective is None
            or int(objective) >= int(claim["required_distance"])
        ),
        "direction": evidence,
    }


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w") as stream:
        for row in rows:
            stream.write(json.dumps(row) + "\n")
    temporary.replace(path)


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260730)
    parser.add_argument("--radius", type=int, default=1)
    parser.add_argument("--max-edits", type=int, default=2)
    parser.add_argument("--min-k", type=int, default=12)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument(
        "--parents",
        help="Comma-separated FRONTIER_SEEDS labels; default uses every seed",
    )
    parser.add_argument(
        "--pool-output", type=Path,
        default=project / "results" / "frontier_mutation_pool.jsonl",
    )
    parser.add_argument(
        "--output", type=Path,
        default=project / "results" / "frontier_mutation_screen.jsonl",
    )
    args = parser.parse_args()
    if args.radius < 1 or args.max_edits < 1:
        parser.error("radius and max-edits must be positive")
    if not 1 <= args.workers <= 8:
        parser.error("workers must be between 1 and 8")
    parents = (
        tuple(item.strip() for item in args.parents.split(",") if item.strip())
        if args.parents else None
    )
    started = time.monotonic()
    pool, stats = build_pool(
        trials=args.trials, seed_value=args.seed,
        radius=args.radius, max_edits=args.max_edits,
        min_k=args.min_k,
        parents=parents,
    )
    write_jsonl(args.pool_output, pool)
    selected = pool[:args.limit] if args.limit else pool
    results: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        futures = [
            executor.submit(screen_first_direction, (claim, args.timeout))
            for claim in selected
        ]
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            write_jsonl(args.output, results)
            print(json.dumps({
                "trial": result["trial"], "k": result["k"],
                "required": result["required_distance"],
                "objective": result["direction"]["objective"],
                "rejected": result["rejected"],
                "unresolved": result["unresolved"],
            }), flush=True)
    results.sort(key=lambda row: int(row["trial"]))
    write_jsonl(args.output, results)
    summary = {
        "status": "UNRESOLVED" if any(row["unresolved"] for row in results) else "NO_WIN",
        "elapsed_s": time.monotonic() - started,
        "pool_stats": stats,
        "screened": len(results),
        "rejected": sum(row["rejected"] for row in results),
        "unresolved": sum(row["unresolved"] for row in results),
        "pool_output": str(args.pool_output),
        "output": str(args.output),
    }
    print(json.dumps(summary, indent=2))
    return 2 if summary["unresolved"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
