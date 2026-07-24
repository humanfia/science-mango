#!/usr/bin/env python3
"""Screen a CSS frontier candidate with two global XOR CP-SAT sectors."""

from __future__ import annotations

import hashlib
import argparse
import json
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate import (
    solve_css_sector_xor,
    verify_css_sector_witness,
)
from evaluation.distance_milp import get_code_matrices
from scripts.screen_frontier_candidate import build_candidate_code, load_candidate

def verify_bb_translation_symmetry(candidate: dict[str, Any]) -> dict[str, Any]:
    """Verify the two torus translations and their two qubit orbits."""
    code = build_candidate_code(candidate)
    hx, hz, _, _ = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    ell, m = int(candidate["ell"]), int(candidate["m"])
    block_size = ell * m
    n = hx.shape[1]

    def canonical_rows(matrix: np.ndarray) -> list[bytes]:
        return sorted(bytes(row) for row in np.packbits(matrix, axis=1))

    grid = np.arange(block_size).reshape(ell, m)
    generators = []
    for axis, order in ((0, ell), (1, m)):
        within_block = np.roll(grid, 1, axis=axis).ravel()
        permutation = np.concatenate((within_block, block_size + within_block))
        hx_preserved = canonical_rows(hx) == canonical_rows(hx[:, permutation])
        hz_preserved = canonical_rows(hz) == canonical_rows(hz[:, permutation])
        generators.append({
            "axis": "x" if axis == 0 else "y",
            "order": order,
            "hx_row_set_preserved": hx_preserved,
            "hz_row_set_preserved": hz_preserved,
            "permutation_sha256": hashlib.sha256(
                permutation.astype("<u4").tobytes()
            ).hexdigest(),
        })
    verified = bool(
        n == 2 * block_size
        and ell > 0 and m > 0
        and all(
            item["hx_row_set_preserved"] and item["hz_row_set_preserved"]
            for item in generators
        )
    )
    return {
        "method": "bb-torus-translation-row-set-v1",
        "verified": verified,
        "shape": [ell, m],
        "block_size": block_size,
        "orbit_representatives": [0, block_size],
        "orbit_sizes": [block_size, block_size],
        "generators": generators,
    }




def solve_sector(
    payload: tuple[dict[str, Any], str, float, int | None, int, int, tuple[int, ...]],
) -> dict[str, Any]:
    candidate, sector, timeout, max_weight, workers, seed, anchors = payload
    code = build_candidate_code(candidate)
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    checks, targets = (hx, lx) if sector == "Z" else (hz, lz)
    evidence = solve_css_sector_xor(
        checks,
        targets,
        timeout=timeout,
        max_weight=max_weight,
        workers=workers,
        seed=seed,
        anchor_indices=anchors,
    )
    failures = (
        verify_css_sector_witness(evidence, checks, targets)
        if evidence.get("operator") is not None else []
    )
    return {
        **evidence,
        "sector": sector,
        "logical_count": len(targets),
        "witness_verified": evidence.get("operator") is not None and not failures,
        "witness_failures": failures,
    }


def classify_xor_results(
    sectors: list[dict[str, Any]],
    *,
    required_distance: int,
    threshold_only: bool,
    symmetry_coverage_verified: bool = False,
) -> str:
    if any(
        item.get("witness_verified") is True
        and item.get("objective") is not None
        and int(item["objective"]) < required_distance
        for item in sectors
    ):
        return "REJECTED"
    if {item.get("sector") for item in sectors} != {"X", "Z"}:
        return "UNRESOLVED"
    anchored = any(item.get("anchor_indices") for item in sectors)
    if anchored and not symmetry_coverage_verified:
        return "UNRESOLVED"
    if threshold_only and all(
        item.get("threshold_infeasible") is True
        and int(item.get("max_weight", -1)) == required_distance - 1
        for item in sectors
    ):
        return "THRESHOLD_PROVEN"
    if not threshold_only and all(
        item.get("exact") is True
        and item.get("witness_verified") is True
        and int(item.get("objective", 0)) >= required_distance
        for item in sectors
    ):
        return "EXACT_PROVEN"
    return "UNRESOLVED"


def write_artifact(
    path: Path,
    candidate: dict[str, Any],
    sectors: list[dict[str, Any]],
    *,
    threshold_only: bool,
    translation_symmetry: dict[str, Any],
) -> dict[str, Any]:
    ordered_sectors = sorted(sectors, key=lambda item: str(item["sector"]))
    required = int(candidate["required_distance"])
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-frontier-xor-sector-screen",
        "status": classify_xor_results(
            sectors,
            required_distance=required,
            threshold_only=threshold_only,
            symmetry_coverage_verified=translation_symmetry.get("verified") is True,
        ),
        "candidate": candidate,
        "required_distance": required,
        "threshold_only": threshold_only,
        "completed_sectors": len(sectors),
        "translation_symmetry": translation_symmetry,
        "sectors": ordered_sectors,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(artifact, indent=2) + "\n")
    temporary.replace(path)
    return artifact


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("screen_results", type=Path)
    parser.add_argument("--trial", type=int, required=True)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--exact", action="store_true")
    parser.add_argument(
        "--parallel-sectors",
        action="store_true",
        help="solve X/Z concurrently, splitting workers between them",
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("workers must be between 1 and 8")
    candidate = load_candidate(args.screen_results, args.trial)
    if candidate.get("C_terms") or candidate.get("D_terms"):
        parser.error("XOR sector screen currently supports CSS candidates")
    translation_symmetry = verify_bb_translation_symmetry(candidate)
    if translation_symmetry.get("verified") is not True:
        parser.error("BB translation symmetry audit failed")
    anchors = tuple(translation_symmetry["orbit_representatives"])
    threshold_only = not args.exact
    max_weight = int(candidate["required_distance"]) - 1 if threshold_only else None
    sectors: list[dict[str, Any]] = []

    def record(result: dict[str, Any]) -> None:
        sectors.append(result)
        artifact = write_artifact(
            args.output,
            candidate,
            sectors,
            threshold_only=threshold_only,
            translation_symmetry=translation_symmetry,
        )
        print(
            json.dumps({
                "sector": result["sector"],
                "status": result["status_name"],
                "objective": result.get("objective"),
                "best_bound": result.get("best_objective_bound"),
                "gate": artifact["status"],
            }),
            flush=True,
        )

    if args.parallel_sectors:
        solver_workers = max(1, args.workers // 2)
        with ProcessPoolExecutor(max_workers=2) as executor:
            futures = [
                executor.submit(
                    solve_sector,
                    (
                        candidate, sector, args.timeout, max_weight,
                        solver_workers, args.seed, anchors,
                    ),
                )
                for sector in ("X", "Z")
            ]
            for future in as_completed(futures):
                record(future.result())
    else:
        for sector in ("X", "Z"):
            record(solve_sector((
                candidate, sector, args.timeout, max_weight,
                args.workers, args.seed, anchors,
            )))
    artifact = write_artifact(
        args.output,
        candidate,
        sectors,
        threshold_only=threshold_only,
        translation_symmetry=translation_symmetry,
    )
    print(json.dumps({
        "status": artifact["status"],
        "completed_sectors": artifact["completed_sectors"],
        "output": str(args.output),
    }, indent=2))
    return {
        "THRESHOLD_PROVEN": 0,
        "EXACT_PROVEN": 0,
        "REJECTED": 1,
    }.get(artifact["status"], 2)


if __name__ == "__main__":
    raise SystemExit(main())
