#!/usr/bin/env python3
"""Screen a CSS frontier candidate with two global XOR CP-SAT sectors."""

from __future__ import annotations

import hashlib
import argparse
import json
import math
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
from evaluation.geometry import (
    candidate_geometry,
    geometry_basis,
    geometry_identity,
    reduce_coordinate,
)
from scripts.screen_frontier_candidate import build_candidate_code, load_candidate


TERMINAL_STATUSES = {"THRESHOLD_PROVEN", "EXACT_PROVEN", "REJECTED"}

def verify_bb_translation_symmetry(candidate: dict[str, Any]) -> dict[str, Any]:
    """Verify the two torus translations and their two qubit orbits."""
    code = build_candidate_code(candidate)
    hx, hz, _, _ = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    ell, m = int(candidate["ell"]), int(candidate["m"])
    geometry = candidate_geometry(candidate)
    identity = geometry_identity(ell, m, geometry)
    block_size = ell * m
    n = hx.shape[1]

    def canonical_rows(matrix: np.ndarray) -> list[bytes]:
        return sorted(bytes(row) for row in np.packbits(matrix, axis=1))

    # Preserve the exact legacy report for the rectangular quotient.  These
    # reports are persisted in Stage-3 checkpoints, so adding even informative
    # fields here would invalidate otherwise sound q=0 work.
    if geometry is None:
        grid = np.arange(block_size).reshape(ell, m)
        generators = []
        for axis, order in ((0, ell), (1, m)):
            within_block = np.roll(grid, 1, axis=axis).ravel()
            permutation = np.concatenate(
                (within_block, block_size + within_block)
            )
            hx_preserved = canonical_rows(hx) == canonical_rows(
                hx[:, permutation]
            )
            hz_preserved = canonical_rows(hz) == canonical_rows(
                hz[:, permutation]
            )
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
                item["hx_row_set_preserved"]
                and item["hz_row_set_preserved"]
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

    generators = []
    twist = int(geometry["twist"])
    specifications = (
        ("x", 1, 0, ell * m // math.gcd(m, twist)),
        ("y", 0, 1, m),
    )

    def inverse_translation_index(
        x_coord: int, y_coord: int, dx: int, dy: int,
    ) -> int:
        reduced_x, reduced_y = reduce_coordinate(
            ell,
            m,
            x_coord - dx,
            y_coord - dy,
            geometry,
        )
        return reduced_x * m + reduced_y

    for axis, dx, dy, order in specifications:
        # ``matrix[:, permutation]`` applies the inverse translation to
        # columns.  Reduce it in the actual quotient; an x-wrap on a twisted
        # torus also shifts y and therefore cannot be represented by np.roll.
        within_block = np.asarray([
            inverse_translation_index(x_coord, y_coord, dx, dy)
            for x_coord in range(ell)
            for y_coord in range(m)
        ], dtype=np.int64)
        permutation = np.concatenate((within_block, block_size + within_block))
        hx_preserved = canonical_rows(hx) == canonical_rows(hx[:, permutation])
        hz_preserved = canonical_rows(hz) == canonical_rows(hz[:, permutation])
        generators.append({
            "axis": axis,
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
        "method": "bb-quotient-translation-row-set-v2",
        "verified": verified,
        "shape": [ell, m],
        "geometry": identity,
        "relation_basis": [list(vector) for vector in geometry_basis(
            ell, m, geometry,
        )],
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
        item.get("formulation") == "css-sector-xor-cpsat-v1"
        and item.get("solver") == "ortools-cp-sat"
        and item.get("status_name") == "INFEASIBLE"
        and item.get("success") is False
        and item.get("threshold_infeasible") is True
        and int(item.get("max_weight", -1)) == required_distance - 1
        and item.get("operator") is None
        and item.get("objective") is None
        for item in sectors
    ):
        return "THRESHOLD_PROVEN"
    if not threshold_only and all(
        item.get("formulation") == "css-sector-xor-cpsat-v1"
        and item.get("solver") == "ortools-cp-sat"
        and item.get("status_name") == "OPTIMAL"
        and item.get("exact") is True
        and item.get("witness_verified") is True
        and int(item.get("objective", 0)) >= required_distance
        and item.get("operator") is not None
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
    cache_binding: dict[str, Any] | None = None,
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
    if cache_binding is not None:
        artifact["cache_binding"] = cache_binding
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(artifact, indent=2) + "\n")
    temporary.replace(path)
    return artifact


def load_replayable_sectors(
    path: Path,
    candidate: dict[str, Any],
    *,
    threshold_only: bool,
    translation_symmetry: dict[str, Any],
    expected_cache_binding: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Recover completed sector proofs while discarding timed-out work.

    Feasible witnesses are replayed against the reconstructed code. A bounded
    INFEASIBLE result is retained only when its stored threshold and solver
    status match this run. Final publication certificates still rerun their
    independent exact-distance gate; this checkpoint is campaign state, not a
    substitute for that certificate.
    """
    if not path.exists():
        return []
    try:
        artifact = json.loads(path.read_text())
    except (OSError, TypeError, ValueError):
        return []
    if (
        artifact.get("candidate") != candidate
        or artifact.get("threshold_only") is not threshold_only
        or artifact.get("translation_symmetry") != translation_symmetry
        or (
            expected_cache_binding is not None
            and artifact.get("cache_binding") != expected_cache_binding
        )
    ):
        return []

    code = build_candidate_code(candidate)
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    required = int(candidate["required_distance"])
    recovered: dict[str, dict[str, Any]] = {}
    for raw in artifact.get("sectors", []):
        stored = dict(raw)
        sector = stored.get("sector")
        if sector not in {"X", "Z"}:
            continue
        checks, targets = (hx, lx) if sector == "Z" else (hz, lz)
        if stored.get("operator") is not None:
            failures = verify_css_sector_witness(stored, checks, targets)
            stored["witness_verified"] = not failures
            stored["witness_failures"] = failures
            objective = stored.get("objective")
            low_witness = (
                not failures
                and objective is not None
                and int(objective) < required
            )
            exact_sector = (
                not threshold_only
                and not failures
                and stored.get("exact") is True
            )
            if low_witness or exact_sector:
                stored["resumed_replay_verified"] = True
                recovered[str(sector)] = stored
            continue
        bounded_proof = (
            threshold_only
            and stored.get("threshold_infeasible") is True
            and stored.get("status_name") == "INFEASIBLE"
            and int(stored.get("max_weight", -1)) == required - 1
        )
        if bounded_proof:
            stored["resumed_solver_proof"] = True
            recovered[str(sector)] = stored
    return [recovered[name] for name in ("X", "Z") if name in recovered]


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
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="resume replayable completed sectors from the output artifact",
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
    sectors = (
        load_replayable_sectors(
            args.output,
            candidate,
            threshold_only=threshold_only,
            translation_symmetry=translation_symmetry,
        )
        if args.resume else []
    )

    resumed_artifact = (
        write_artifact(
            args.output,
            candidate,
            sectors,
            threshold_only=threshold_only,
            translation_symmetry=translation_symmetry,
        )
        if sectors else None
    )
    if resumed_artifact and resumed_artifact["status"] in TERMINAL_STATUSES:
        print(json.dumps({
            "status": resumed_artifact["status"],
            "resumed": True,
            "completed_sectors": resumed_artifact["completed_sectors"],
            "output": str(args.output),
        }, indent=2))
        return {
            "THRESHOLD_PROVEN": 0,
            "EXACT_PROVEN": 0,
            "REJECTED": 1,
        }[resumed_artifact["status"]]

    def record(result: dict[str, Any]) -> None:
        sectors[:] = [
            item for item in sectors
            if item.get("sector") != result.get("sector")
        ]
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

    completed = {str(item.get("sector")) for item in sectors}
    pending = [sector for sector in ("X", "Z") if sector not in completed]
    if args.parallel_sectors and len(pending) > 1:
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
                for sector in pending
            ]
            for future in as_completed(futures):
                record(future.result())
    else:
        for sector in pending:
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
