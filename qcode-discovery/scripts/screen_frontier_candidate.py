#!/usr/bin/env python3
"""Screen every logical direction of one frontier candidate with saved witnesses."""

from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    _direction_specs,
    pack_vector,
    solve_css_below_threshold,
    solve_css_direction,
    verify_css_witness,
)
from evaluation.noncss_certificate import (
    solve_symplectic_direction,
    verify_symplectic_witness,
)
from evaluation.pbb_code import (
    build_pbb_code,
    get_symplectic_logicals,
)


def load_candidate(path: Path, trial: int) -> dict[str, Any]:
    matches = [
        json.loads(line) for line in path.read_text().splitlines()
        if line.strip() and int(json.loads(line).get("trial", -1)) == trial
    ]
    if len(matches) != 1:
        raise ValueError(f"expected one trial={trial} candidate, found {len(matches)}")
    return matches[0]


def build_candidate_code(claim: dict[str, Any]):
    if claim.get("C_terms") or claim.get("D_terms"):
        return build_pbb_code(**{
            name: claim[name]
            for name in (
                "ell", "m", "A_terms", "B_terms", "C_terms", "D_terms",
            )
        })
    return build_bb_code(
        claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
    )


_WORKER_CLAIM: dict[str, Any] | None = None
_WORKER_CODE = None
_WORKER_SPECS = None


def initialize_worker(claim: dict[str, Any]) -> None:
    """Build the candidate and its logical basis once in each worker."""
    global _WORKER_CLAIM, _WORKER_CODE, _WORKER_SPECS
    _WORKER_CLAIM = claim
    _WORKER_CODE = build_candidate_code(claim)
    _WORKER_SPECS = (
        None if claim.get("C_terms") or claim.get("D_terms")
        else _direction_specs(_WORKER_CODE)
    )


def solve_position(
    payload: tuple[int, float, int | None],
) -> dict[str, Any]:
    position, timeout, max_weight = payload
    if _WORKER_CLAIM is None or _WORKER_CODE is None:
        raise RuntimeError("frontier worker was not initialized")
    claim, code = _WORKER_CLAIM, _WORKER_CODE
    if claim.get("C_terms") or claim.get("D_terms"):
        stabilizer = np.asarray(code.matrix, dtype=np.uint8) & 1
        target = get_symplectic_logicals(code)[position]
        result = solve_symplectic_direction(
            stabilizer, target, timeout=timeout,
        )
        evidence = {
            **result,
            "position": position,
            "logical_index": position,
            "target_logical": pack_vector(target),
        }
        failures = verify_symplectic_witness(
            evidence, stabilizer, target,
        )
        evidence["witness_verified"] = not failures
        evidence["witness_failures"] = failures
        return evidence
    if _WORKER_SPECS is None:
        raise RuntimeError("CSS logical directions were not initialized")
    logical_type, index, check_name, checks, target = _WORKER_SPECS[position]
    result = (
        solve_css_direction(checks, target, timeout=timeout)
        if max_weight is None else solve_css_below_threshold(
            checks, target, max_weight=max_weight, timeout=timeout,
        )
    )
    evidence = {
        **result,
        "position": position,
        "logical_type": logical_type,
        "logical_index": index,
        "check_matrix": check_name,
        "target_logical": pack_vector(target),
    }
    failures = (
        verify_css_witness(evidence, checks, target) if result["operator"] else []
    )
    evidence["witness_verified"] = result["operator"] is not None and not failures
    evidence["witness_failures"] = failures
    return evidence


def classify_results(
    directions: list[dict[str, Any]],
    *,
    required_distance: int,
    expected_directions: int,
) -> str:
    if any(
        item.get("witness_verified") is True
        and item.get("objective") is not None
        and int(item["objective"]) < required_distance
        for item in directions
    ):
        return "REJECTED"
    if len(directions) == expected_directions and all(
        item.get("threshold_infeasible") is True
        and int(item.get("max_weight", -1)) == required_distance - 1
        and item.get("operator") is None
        for item in directions
    ):
        return "THRESHOLD_PROVEN"
    proven = [
        item for item in directions
        if item.get("success") is True
        and item.get("mip_gap") == 0.0
        and item.get("objective") is not None
        and int(item["objective"]) >= required_distance
        and item.get("witness_verified") is True
    ]
    if len(directions) == expected_directions and len(proven) == expected_directions:
        return "THRESHOLD_PROVEN"
    return "UNRESOLVED"


def order_direction_positions(
    candidate: dict[str, Any], code: Any,
) -> list[int]:
    """Try low-weight basis representatives first for faster rejection."""
    if candidate.get("C_terms") or candidate.get("D_terms"):
        targets = get_symplectic_logicals(code)
    else:
        targets = [spec[-1] for spec in _direction_specs(code)]
    return sorted(
        range(len(targets)),
        key=lambda position: (int(np.asarray(targets[position]).sum()), position),
    )


def load_replayable_rejection(
    path: Path,
    candidate: dict[str, Any],
    code: Any,
) -> dict[str, Any] | None:
    """Reuse only an algebraically replayed low witness, never solver claims."""
    if not path.exists():
        return None
    try:
        artifact = json.loads(path.read_text())
    except (OSError, TypeError, ValueError):
        return None
    if artifact.get("candidate") != candidate:
        return None
    required = int(candidate["required_distance"])
    css_specs = (
        None
        if candidate.get("C_terms") or candidate.get("D_terms")
        else _direction_specs(code)
    )
    for stored in artifact.get("directions", []):
        try:
            position = int(stored["position"])
            objective = int(stored["objective"])
        except (KeyError, TypeError, ValueError):
            continue
        if objective >= required or stored.get("operator") is None:
            continue
        evidence = dict(stored)
        if css_specs is None:
            targets = get_symplectic_logicals(code)
            if not 0 <= position < len(targets):
                continue
            failures = verify_symplectic_witness(
                evidence,
                np.asarray(code.matrix, dtype=np.uint8) & 1,
                targets[position],
            )
        else:
            if not 0 <= position < len(css_specs):
                continue
            failures = verify_css_witness(
                evidence, css_specs[position][-2], css_specs[position][-1],
            )
        if not failures:
            evidence["witness_verified"] = True
            evidence["witness_failures"] = []
            evidence["resumed_verified_witness"] = True
            return evidence
    return None


def write_artifact(
    path: Path,
    candidate: dict[str, Any],
    directions: list[dict[str, Any]],
    *,
    expected_directions: int,
) -> dict[str, Any]:
    directions.sort(key=lambda item: int(item["position"]))
    required = int(candidate["required_distance"])
    status = classify_results(
        directions,
        required_distance=required,
        expected_directions=expected_directions,
    )
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-frontier-threshold-screen",
        "status": status,
        "candidate": candidate,
        "required_distance": required,
        "expected_directions": expected_directions,
        "completed_directions": len(directions),
        "low_witnesses": sum(
            item.get("witness_verified") is True
            and item.get("objective") is not None
            and int(item["objective"]) < required
            for item in directions
        ),
        "directions": directions,
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
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--threshold-only", action="store_true")
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="reuse only replay-verified low witnesses from the output artifact",
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("workers must be between 1 and 8")
    candidate = load_candidate(args.screen_results, args.trial)
    if args.threshold_only and (candidate.get("C_terms") or candidate.get("D_terms")):
        parser.error("threshold-only mode currently supports CSS candidates")
    max_weight = int(candidate["required_distance"]) - 1 if args.threshold_only else None
    code = build_candidate_code(candidate)
    position_order = order_direction_positions(candidate, code)
    expected = len(position_order)
    directions: list[dict[str, Any]] = []
    if args.resume:
        saved_rejection = load_replayable_rejection(args.output, candidate, code)
        if saved_rejection is not None:
            directions.append(saved_rejection)
            artifact = write_artifact(
                args.output, candidate, directions,
                expected_directions=expected,
            )
            print(json.dumps({
                "status": artifact["status"],
                "resumed_verified_witness": True,
                "position": saved_rejection["position"],
                "objective": saved_rejection["objective"],
                "output": str(args.output),
            }, indent=2))
            return 1
    positions = iter(position_order)
    executor = ProcessPoolExecutor(
        max_workers=args.workers,
        initializer=initialize_worker,
        initargs=(candidate,),
    )
    active = {}
    try:
        for _ in range(min(args.workers, expected)):
            position = next(positions)
            future = executor.submit(
                solve_position, (position, args.timeout, max_weight),
            )
            active[future] = position
        rejected = False
        while active and not rejected:
            done, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in done:
                position = active.pop(future)
                evidence = future.result()
                directions.append(evidence)
                artifact = write_artifact(
                    args.output, candidate, directions,
                    expected_directions=expected,
                )
                print(json.dumps({
                    "position": position,
                    "objective": evidence.get("objective"),
                    "success": evidence.get("success"),
                    "dual": evidence.get("mip_dual_bound"),
                    "status": artifact["status"],
                }), flush=True)
                rejected = artifact["status"] == "REJECTED"
                if not rejected:
                    try:
                        next_position = next(positions)
                    except StopIteration:
                        continue
                    next_future = executor.submit(
                        solve_position, (next_position, args.timeout, max_weight),
                    )
                    active[next_future] = next_position
        for future in active:
            future.cancel()
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
    artifact = write_artifact(
        args.output, candidate, directions,
        expected_directions=expected,
    )
    print(json.dumps({
        "status": artifact["status"],
        "completed": artifact["completed_directions"],
        "expected": expected,
        "low_witnesses": artifact["low_witnesses"],
        "output": str(args.output),
    }, indent=2))
    return {"THRESHOLD_PROVEN": 0, "REJECTED": 1}.get(artifact["status"], 2)


if __name__ == "__main__":
    raise SystemExit(main())
