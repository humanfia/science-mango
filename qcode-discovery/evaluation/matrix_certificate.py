"""Replayable exact certificate for an arbitrary binary CSS matrix pair."""

from __future__ import annotations

import importlib.metadata
import math
import platform
import time
from pathlib import Path
from typing import Any

import numpy as np

from evaluation.certificate import (
    FORMULATION,
    _certificate_sha256,
    _direction_specs,
    _file_sha256,
    _highs_version,
    _validate_solver_workers,
    pack_vector,
    solve_css_direction,
    unpack_vector,
    verify_direction_evidence,
)
from evaluation.final_gate import (
    _connected,
    _matrix_sha256,
    classify_win,
    validate_known_answer_artifact,
)
from evaluation.matrix_io import build_css_from_matrices, css_parameters, pack_matrix
from evaluation.registry import check_code_novelty

SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qldpc-css-matrix-exact"


def _version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def _static_gate(
    code,
    hx: np.ndarray,
    hz: np.ndarray,
    *,
    distance: int,
    exact: bool,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    baseline = validate_known_answer_artifact(known_answer_artifact)
    n, k = css_parameters(hx, hz)
    stacked = np.vstack((hx, hz))
    connected, components = _connected(stacked)
    novelty = check_code_novelty(code, code_type="css")
    win = classify_win(n, k, distance)
    checks = {
        "known_answer_gate": baseline["passed"],
        "css_commutation": not np.any((hx @ hz.T) & 1),
        "positive_dimension": k > 0,
        "weight_and_degree_at_most_6": (
            int(stacked.sum(axis=1).max(initial=0)) <= 6
            and int(stacked.sum(axis=0).max(initial=0)) <= 6
        ),
        "connected_tanner_graph": connected,
        "all_2k_milp_directions_optimal": exact,
        "expanded_registry_novel": novelty["novel"],
        "challenge_win": win["passed"],
    }
    return {
        "accepted": all(checks.values()),
        "checks": checks,
        "failures": [name for name, passed in checks.items() if not passed],
        "known_answer": baseline,
        "structural_novelty": novelty,
        "win": win,
        "candidate": {
            "n": n,
            "k": k,
            "d": distance,
            "fom": win["fom"],
            "tanner_components": components,
            "matrix_sha256": {
                "hx": _matrix_sha256(hx),
                "hz": _matrix_sha256(hz),
            },
        },
    }


def build_matrix_css_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
) -> dict[str, Any]:
    hx_value = claim.get("H_X", claim.get("hx"))
    hz_value = claim.get("H_Z", claim.get("hz"))
    if hx_value is None or hz_value is None:
        raise ValueError("generic CSS claim requires H_X and H_Z")
    code, hx, hz = build_css_from_matrices(hx_value, hz_value)
    n, k = css_parameters(hx, hz)
    if k <= 0:
        raise ValueError("generic CSS claim must encode at least one logical qubit")

    directions: list[dict[str, Any]] = []
    started = time.monotonic()
    for logical_type, index, check_name, checks, target in _direction_specs(code):
        remaining = total_timeout - (time.monotonic() - started)
        if remaining <= 0:
            break
        evidence = solve_css_direction(
            checks,
            target,
            timeout=min(float(timeout_per_logical), remaining),
        )
        evidence.update(
            {
                "logical_type": logical_type,
                "logical_index": index,
                "check_matrix": check_name,
                "target_logical": pack_vector(target),
            }
        )
        directions.append(evidence)

    exact = len(directions) == 2 * k and all(
        not verify_direction_evidence(
            item,
            hx if item["check_matrix"] == "hx" else hz,
            unpack_vector(item["target_logical"]),
        )
        for item in directions
    )
    objectives = [
        int(item["objective"])
        for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    gate = _static_gate(
        code,
        hx,
        hz,
        distance=distance,
        exact=exact,
        known_answer_artifact=known_answer_artifact,
    )
    best = min(
        (item for item in directions if item.get("objective") is not None),
        key=lambda item: int(item["objective"]),
        default=None,
    )
    certificate = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": CERTIFICATE_TYPE,
        "formulation": FORMULATION,
        "claim": {
            "source": claim.get("source"),
            "H_X": pack_matrix(hx),
            "H_Z": pack_matrix(hz),
            "n": n,
            "k": k,
            "d": distance,
            "fom": gate["win"]["fom"],
        },
        "matrix_sha256": {
            "hx": _matrix_sha256(hx),
            "hz": _matrix_sha256(hz),
        },
        "known_answer": {"artifact_sha256": _file_sha256(known_answer_artifact)},
        "solver": {
            "interface": "scipy.optimize.milp",
            "backend": "HiGHS",
            "scipy_version": _version("scipy"),
            "highs_version": _highs_version(),
            "presolve": True,
            "timeout_per_logical_s": timeout_per_logical,
            "total_timeout_s": total_timeout,
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": _version("numpy"),
            "qldpc": _version("qldpc"),
        },
        "milp": {
            "exact": exact,
            "expected_directions": 2 * k,
            "completed_directions": len(directions),
            "distance": distance,
            "elapsed_s": time.monotonic() - started,
            "directions": directions,
        },
        "upper_witness": None
        if best is None
        else {
            "logical_type": best["logical_type"],
            "logical_index": best["logical_index"],
            "weight": best["objective"],
            "operator": best["operator"],
            "target_logical": best["target_logical"],
        },
        "final_gate": gate,
        "passed": bool(exact and gate["accepted"]),
    }
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def verify_matrix_css_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
    total_timeout: float | None = None,
    solver_workers: int = 1,
) -> dict[str, Any]:
    workers = _validate_solver_workers(solver_workers)
    if timeout_per_logical is not None:
        timeout_per_logical = float(timeout_per_logical)
        if not math.isfinite(timeout_per_logical) or timeout_per_logical <= 0:
            raise ValueError("timeout_per_logical must be a positive finite number")
    if total_timeout is not None:
        total_timeout = float(total_timeout)
        if not math.isfinite(total_timeout) or total_timeout <= 0:
            raise ValueError("total_timeout must be a positive finite number")
    verify_started = time.monotonic()
    failures: list[str] = []
    checks = {
        "schema": (
            certificate.get("schema_version") == SCHEMA_VERSION
            and certificate.get("certificate_type") == CERTIFICATE_TYPE
            and certificate.get("formulation") == FORMULATION
        ),
        "certificate_sha256": (
            certificate.get("certificate_sha256") == _certificate_sha256(certificate)
        ),
    }
    try:
        claim = certificate["claim"]
        code, hx, hz = build_css_from_matrices(claim["H_X"], claim["H_Z"])
        n, k = css_parameters(hx, hz)
        checks["known_answer_sha256"] = certificate["known_answer"][
            "artifact_sha256"
        ] == _file_sha256(known_answer_artifact)
        checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
            "hx": _matrix_sha256(hx),
            "hz": _matrix_sha256(hz),
        }
        specs = _direction_specs(code)
        directions = certificate["milp"]["directions"]
    except (KeyError, TypeError, ValueError, OSError) as exc:
        return {
            "passed": False,
            "replay_complete": True,
            "checks": checks,
            "failures": [f"certificate reconstruction failed: {exc}"],
        }

    checks["claim_parameters"] = (
        int(claim.get("n", -1)) == n and int(claim.get("k", -1)) == k
    )
    checks["direction_count"] = len(directions) == len(specs) == 2 * k
    direction_failures: list[str] = []
    replay_complete = True
    for position, (logical_type, index, check_name, matrix, target) in enumerate(specs):
        if position >= len(directions):
            direction_failures.append(f"{logical_type}[{index}]: missing")
            continue
        evidence = directions[position]
        local = []
        if (
            evidence.get("logical_type") != logical_type
            or int(evidence.get("logical_index", -1)) != index
            or evidence.get("check_matrix") != check_name
        ):
            local.append("identity/order mismatch")
        local.extend(verify_direction_evidence(evidence, matrix, target))
        if rerun_milp:
            remaining = None
            if total_timeout is not None:
                remaining = total_timeout - (time.monotonic() - verify_started)
            if remaining is not None and remaining <= 0:
                local.append("rerun total timeout exhausted")
                replay_complete = False
                rerun = None
            else:
                raw_timeout = timeout_per_logical
                if raw_timeout is None:
                    raw_timeout = certificate.get("solver", {}).get(
                        "timeout_per_logical_s", 300
                    )
                try:
                    timeout = float(raw_timeout)
                except (TypeError, ValueError, OverflowError):
                    timeout = math.nan
                if not math.isfinite(timeout) or timeout <= 0:
                    local.append("invalid rerun timeout")
                    replay_complete = False
                    rerun = None
                else:
                    effective_timeout = timeout
                    if remaining is not None:
                        effective_timeout = min(timeout, remaining)
                    rerun = solve_css_direction(
                        matrix,
                        target,
                        timeout=effective_timeout,
                        solver_workers=workers,
                    )
                    rerun.update(
                        {
                            "logical_type": logical_type,
                            "logical_index": index,
                            "check_matrix": check_name,
                            "target_logical": pack_vector(target),
                        }
                    )
            rerun_valid = (
                rerun is not None
                and not verify_direction_evidence(rerun, matrix, target)
                and rerun.get("objective") == evidence.get("objective")
            )
            if rerun is not None and not rerun_valid:
                replay_complete = False
                local.append("rerun optimum mismatch")
        if local:
            direction_failures.append(f"{logical_type}[{index}]: " + "; ".join(local))
    checks["stored_direction_evidence"] = not direction_failures
    checks["milp_rerun"] = rerun_milp and not direction_failures
    objectives = [
        int(item["objective"])
        for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    checks["distance_recomputed"] = (
        distance > 0
        and certificate["milp"].get("distance") == distance
        and int(claim.get("d", -1)) == distance
    )
    gate = _static_gate(
        code,
        hx,
        hz,
        distance=distance,
        exact=all(
            (
                checks["direction_count"],
                checks["stored_direction_evidence"],
                checks["milp_rerun"],
            )
        ),
        known_answer_artifact=known_answer_artifact,
    )
    checks["final_gate"] = gate["accepted"]
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    failures.extend(name for name, passed in checks.items() if not passed)
    failures.extend(direction_failures)
    return {
        "passed": not failures,
        "replay_complete": replay_complete,
        "checks": checks,
        "failures": failures,
        "distance": distance,
        "directions_verified": len(specs) - len(direction_failures),
        "directions_total": len(specs),
        "final_gate": gate,
    }
