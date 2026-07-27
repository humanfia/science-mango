#!/usr/bin/env python3
"""Screen every logical direction of one frontier candidate with saved witnesses."""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import uuid
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate import (
    FORMULATION as CSS_EXACT_FORMULATION,
    _direction_specs,
    pack_vector,
    solve_css_below_threshold,
    solve_css_direction,
    verify_direction_evidence,
    verify_css_witness,
)
from evaluation.final_gate import minimum_winning_distance
from evaluation.noncss_certificate import (
    FORMULATION as SYMPLECTIC_EXACT_FORMULATION,
    solve_symplectic_direction,
    verify_symplectic_direction,
    verify_symplectic_witness,
)
from evaluation.pbb_code import (
    build_pbb_code,
    get_symplectic_logicals,
)

STAGE3_GATE = "qldpc-frontier-threshold-screen"
STAGE3_SCHEMA_VERSION = 2
CSS_THRESHOLD_FORMULATION = "css-logical-threshold-feasibility-v1"


def _require_integer(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{label} must be an integer")
    return value


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Durably replace one JSON object without exposing partial state."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w") as stream:
            json.dump(dict(value), stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            descriptor = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


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


def validate_candidate_parameters(
    candidate: Mapping[str, Any], code: Any,
) -> dict[str, int]:
    """Rebuild and bind the claimed n/k/threshold before any solver work."""
    values: dict[str, int] = {}
    for name in ("n", "k", "required_distance"):
        try:
            values[name] = _require_integer(
                candidate.get(name), f"candidate {name}",
            )
        except ValueError as exc:
            raise ValueError(f"candidate requires integer {name}") from exc
    rebuilt_n = int(code.num_qudits)
    rebuilt_k = int(code.dimension)
    if values["n"] != rebuilt_n:
        raise ValueError(
            f"candidate n={values['n']} does not match rebuilt n={rebuilt_n}",
        )
    if values["k"] != rebuilt_k:
        raise ValueError(
            f"candidate k={values['k']} does not match rebuilt k={rebuilt_k}",
        )
    if rebuilt_n <= 0 or rebuilt_k <= 0:
        raise ValueError("candidate must rebuild to positive n and k")
    required = values["required_distance"]
    expected_required = minimum_winning_distance(rebuilt_n, rebuilt_k)
    if required != expected_required:
        raise ValueError(
            f"required_distance={required} does not match challenge threshold "
            f"{expected_required} for rebuilt [[{rebuilt_n},{rebuilt_k}]]",
        )
    if candidate.get("C_terms") or candidate.get("D_terms"):
        actual_directions = len(get_symplectic_logicals(code))
    else:
        actual_directions = len(_direction_specs(code))
    expected = 2 * rebuilt_k
    if expected <= 0 or actual_directions != expected:
        raise ValueError(
            "reconstructed logical basis does not contain exactly 2k "
            f"directions ({actual_directions} != {expected})",
        )
    return {
        "n": rebuilt_n,
        "k": rebuilt_k,
        "required_distance": required,
        "expected_directions": expected,
    }


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
            "formulation": SYMPLECTIC_EXACT_FORMULATION,
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
        solve_css_direction(
            checks, target, timeout=timeout, solver_workers=1,
        )
        if max_weight is None else solve_css_below_threshold(
            checks, target, max_weight=max_weight, timeout=timeout,
            solver_workers=1,
        )
    )
    evidence = {
        **result,
        "formulation": (
            CSS_EXACT_FORMULATION
            if max_weight is None else CSS_THRESHOLD_FORMULATION
        ),
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
    if expected_directions <= 0 or required_distance <= 0:
        return "UNRESOLVED"
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


def _replay_stored_direction(
    raw: Mapping[str, Any],
    candidate: Mapping[str, Any],
    code: Any,
    *,
    threshold_only: bool,
) -> dict[str, Any] | None:
    """Revalidate one terminal direction against its reconstructed basis."""
    try:
        stored = dict(raw)
        position = _require_integer(stored["position"], "stored position")
        logical_index = _require_integer(
            stored["logical_index"], "stored logical_index",
        )
        objective = stored.get("objective")
        if objective is not None:
            objective = _require_integer(objective, "stored objective")
    except (KeyError, TypeError, ValueError):
        return None
    required = int(candidate["required_distance"])
    noncss = bool(candidate.get("C_terms") or candidate.get("D_terms"))
    if noncss:
        targets = get_symplectic_logicals(code)
        if not 0 <= position < len(targets):
            return None
        target = targets[position]
        if (
            logical_index != position
            or stored.get("target_logical") != pack_vector(target)
            or stored.get("formulation") != SYMPLECTIC_EXACT_FORMULATION
            or threshold_only
        ):
            return None
        verifier = lambda evidence: verify_symplectic_witness(
            evidence,
            np.asarray(code.matrix, dtype=np.uint8) & 1,
            target,
        )
        exact_verifier = lambda evidence: verify_symplectic_direction(
            evidence,
            np.asarray(code.matrix, dtype=np.uint8) & 1,
            target,
        )
    else:
        specs = _direction_specs(code)
        if not 0 <= position < len(specs):
            return None
        logical_type, index, check_name, checks, target = specs[position]
        expected_formulation = (
            CSS_THRESHOLD_FORMULATION
            if threshold_only else CSS_EXACT_FORMULATION
        )
        if (
            stored.get("logical_type") != logical_type
            or logical_index != index
            or stored.get("check_matrix") != check_name
            or stored.get("target_logical") != pack_vector(target)
            or stored.get("formulation") != expected_formulation
        ):
            return None
        verifier = lambda evidence: verify_css_witness(
            evidence, checks, target,
        )
        exact_verifier = lambda evidence: verify_direction_evidence(
            evidence, checks, target,
        )
        try:
            solver_workers = _require_integer(
                stored.get("solver_workers"), "stored solver_workers",
            )
        except ValueError:
            return None
        if (
            stored.get("solver") != "scipy.optimize.milp"
            or stored.get("backend") != "HiGHS"
            or solver_workers != 1
        ):
            return None

    if threshold_only:
        try:
            stored_max_weight = _require_integer(
                stored.get("max_weight"), "stored max_weight",
            )
        except ValueError:
            return None
        if stored_max_weight != required - 1:
            return None
    if not threshold_only and stored.get("max_weight") is not None:
        return None

    if stored.get("operator") is not None:
        failures = verifier(stored)
        stored["witness_verified"] = not failures
        stored["witness_failures"] = failures
        if failures or objective is None:
            return None
        if objective < required:
            stored["resumed_replay_verified"] = True
            return stored
        if not threshold_only and not exact_verifier(stored):
            stored["resumed_zero_gap_exact"] = True
            return stored
        return None

    bounded_proof = bool(
        threshold_only
        and not noncss
        and stored.get("threshold_infeasible") is True
        and isinstance(stored.get("status"), int)
        and not isinstance(stored.get("status"), bool)
        and stored.get("status") == 2
        and stored.get("success") is False
        and stored.get("operator") is None
        and stored.get("objective") is None
        and stored.get("formulation") == CSS_THRESHOLD_FORMULATION
        and stored_max_weight == required - 1
    )
    if bounded_proof:
        stored["resumed_solver_proof"] = True
        return stored
    return None


def replayable_directions_from_artifact(
    artifact: Mapping[str, Any],
    candidate: Mapping[str, Any],
    code: Any,
    *,
    threshold_only: bool,
    strict: bool = False,
) -> list[dict[str, Any]]:
    """Recover only bound terminal directions; UNKNOWN work is discarded."""
    geometry = validate_candidate_parameters(candidate, code)
    raw_directions = artifact.get("directions")
    envelope_valid = bool(
        artifact.get("schema_version") == STAGE3_SCHEMA_VERSION
        and artifact.get("gate") == STAGE3_GATE
        and artifact.get("candidate") == candidate
        and artifact.get("threshold_only") is threshold_only
        and artifact.get("required_distance") == geometry["required_distance"]
        and artifact.get("expected_directions") == geometry["expected_directions"]
        and artifact.get("reconstructed_parameters") == geometry
        and isinstance(raw_directions, list)
        and artifact.get("completed_directions") == len(raw_directions)
    )
    if not envelope_valid:
        if strict:
            raise ValueError("Stage 3 artifact envelope/configuration mismatch")
        return []

    recovered: dict[int, dict[str, Any]] = {}
    invalid = 0
    for raw in raw_directions:
        if not isinstance(raw, Mapping):
            invalid += 1
            continue
        evidence = _replay_stored_direction(
            raw, candidate, code, threshold_only=threshold_only,
        )
        if evidence is None:
            invalid += 1
            continue
        position = int(evidence["position"])
        if position in recovered:
            invalid += 1
            continue
        recovered[position] = evidence
    values = [recovered[position] for position in sorted(recovered)]
    if strict and (
        invalid
        or len(values) != geometry["expected_directions"]
        or set(recovered) != set(range(geometry["expected_directions"]))
    ):
        raise ValueError(
            "Stage 3 artifact is incomplete or contains non-replayable directions",
        )
    return values


def load_replayable_directions(
    path: Path,
    candidate: dict[str, Any],
    code: Any,
    *,
    threshold_only: bool,
) -> list[dict[str, Any]]:
    """Load durable terminal directions while dropping UNKNOWN/timeouts."""
    if not path.exists():
        return []
    try:
        artifact = json.loads(path.read_text())
    except (OSError, TypeError, ValueError):
        return []
    if not isinstance(artifact, Mapping):
        return []
    return replayable_directions_from_artifact(
        artifact, candidate, code, threshold_only=threshold_only,
    )


def claim_from_threshold_artifact(
    artifact: Mapping[str, Any],
) -> dict[str, Any]:
    """Safely unwrap a complete Stage 3 proof for the Stage 4 CLI."""
    if artifact.get("status") != "THRESHOLD_PROVEN":
        raise ValueError("Stage 3 artifact status must be THRESHOLD_PROVEN")
    candidate = artifact.get("candidate")
    if not isinstance(candidate, Mapping):
        raise ValueError("Stage 3 artifact candidate must be an object")
    threshold_only = artifact.get("threshold_only")
    if not isinstance(threshold_only, bool):
        raise ValueError("Stage 3 artifact threshold_only flag is invalid")
    claim = dict(candidate)
    code = build_candidate_code(claim)
    directions = replayable_directions_from_artifact(
        artifact,
        claim,
        code,
        threshold_only=threshold_only,
        strict=True,
    )
    geometry = validate_candidate_parameters(claim, code)
    if classify_results(
        directions,
        required_distance=geometry["required_distance"],
        expected_directions=geometry["expected_directions"],
    ) != "THRESHOLD_PROVEN":
        raise ValueError("Stage 3 directions do not prove the threshold")
    return claim


def write_artifact(
    path: Path,
    candidate: dict[str, Any],
    directions: list[dict[str, Any]],
    *,
    expected_directions: int,
    threshold_only: bool,
    reconstructed_parameters: Mapping[str, int],
) -> dict[str, Any]:
    ordered = sorted(directions, key=lambda item: int(item["position"]))
    required = int(candidate["required_distance"])
    status = classify_results(
        ordered,
        required_distance=required,
        expected_directions=expected_directions,
    )
    artifact = {
        "schema_version": STAGE3_SCHEMA_VERSION,
        "gate": STAGE3_GATE,
        "status": status,
        "candidate": candidate,
        "required_distance": required,
        "threshold_only": threshold_only,
        "reconstructed_parameters": dict(reconstructed_parameters),
        "expected_directions": expected_directions,
        "completed_directions": len(ordered),
        "low_witnesses": sum(
            item.get("witness_verified") is True
            and item.get("objective") is not None
            and int(item["objective"]) < required
            for item in ordered
        ),
        "directions": ordered,
    }
    _atomic_write_json(path, artifact)
    return artifact


def screen_candidate(
    candidate: dict[str, Any],
    *,
    output: Path,
    timeout: float = 120,
    workers: int = 4,
    threshold_only: bool = False,
    resume: bool = True,
    progress: Callable[[Mapping[str, Any]], None] | None = None,
) -> dict[str, Any]:
    """Run one resumable direction audit and return its durable artifact."""
    if not 1 <= workers <= 8:
        raise ValueError("workers must be between 1 and 8")
    timeout = float(timeout)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("timeout must be a positive finite number")
    if threshold_only and (
        candidate.get("C_terms") or candidate.get("D_terms")
    ):
        raise ValueError("threshold-only mode currently supports CSS candidates")
    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    position_order = order_direction_positions(candidate, code)
    expected = geometry["expected_directions"]
    if len(position_order) != expected:
        raise ValueError("ordered direction count does not match rebuilt 2k")
    max_weight = geometry["required_distance"] - 1 if threshold_only else None
    directions = (
        load_replayable_directions(
            output, candidate, code, threshold_only=threshold_only,
        )
        if resume else []
    )
    artifact = write_artifact(
        output,
        candidate,
        directions,
        expected_directions=expected,
        threshold_only=threshold_only,
        reconstructed_parameters=geometry,
    )
    if artifact["status"] in {"REJECTED", "THRESHOLD_PROVEN"}:
        return artifact
    completed = {int(item["position"]) for item in directions}
    positions = iter(
        position for position in position_order if position not in completed
    )
    executor = ProcessPoolExecutor(
        max_workers=workers,
        initializer=initialize_worker,
        initargs=(candidate,),
    )
    active: dict[Any, int] = {}
    try:
        for _ in range(min(workers, expected - len(completed))):
            position = next(positions)
            future = executor.submit(
                solve_position, (position, timeout, max_weight),
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
                    output,
                    candidate,
                    directions,
                    expected_directions=expected,
                    threshold_only=threshold_only,
                    reconstructed_parameters=geometry,
                )
                if progress is not None:
                    progress({
                        "position": position,
                        "objective": evidence.get("objective"),
                        "success": evidence.get("success"),
                        "dual": evidence.get("mip_dual_bound"),
                        "status": artifact["status"],
                    })
                rejected = artifact["status"] == "REJECTED"
                if not rejected:
                    try:
                        next_position = next(positions)
                    except StopIteration:
                        continue
                    next_future = executor.submit(
                        solve_position, (next_position, timeout, max_weight),
                    )
                    active[next_future] = next_position
        for future in active:
            future.cancel()
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
    return write_artifact(
        output,
        candidate,
        directions,
        expected_directions=expected,
        threshold_only=threshold_only,
        reconstructed_parameters=geometry,
    )


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
        help="resume replay-validated terminal directions; discard UNKNOWN",
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    candidate = load_candidate(args.screen_results, args.trial)
    try:
        artifact = screen_candidate(
            candidate,
            output=args.output,
            timeout=args.timeout,
            workers=args.workers,
            threshold_only=args.threshold_only,
            resume=args.resume,
            progress=lambda update: print(json.dumps(update), flush=True),
        )
    except (KeyError, TypeError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps({
        "status": artifact["status"],
        "completed": artifact["completed_directions"],
        "expected": artifact["expected_directions"],
        "low_witnesses": artifact["low_witnesses"],
        "output": str(args.output),
    }, indent=2))
    return {"THRESHOLD_PROVEN": 0, "REJECTED": 1}.get(artifact["status"], 2)


if __name__ == "__main__":
    raise SystemExit(main())
