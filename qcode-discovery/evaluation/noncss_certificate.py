"""Replayable exact MILP certificates for PBB and generic non-CSS codes."""

from __future__ import annotations

import importlib.metadata
import math
import platform
import time
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from evaluation.certificate import (
    _certificate_sha256,
    _file_sha256,
    _highs_version,
    pack_vector,
    unpack_vector,
)
from evaluation.final_gate import (
    _connected,
    _matrix_sha256,
    classify_win,
    validate_known_answer_artifact,
)
from evaluation.matrix_io import (
    build_noncss_from_matrix,
    noncss_parameters,
    pack_matrix,
)
from evaluation.pbb_code import (
    build_pbb_code,
    get_symplectic_logicals,
    symplectic_weight,
)
from evaluation.registry import check_code_novelty


SCHEMA_VERSION = 1
FORMULATION = "symplectic-logical-anticommutation-milp-v1"
PBB_TYPE = "qldpc-pbb-noncss-exact"
MATRIX_TYPE = "qldpc-noncss-matrix-exact"


def _version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def solve_symplectic_direction(
    stabilizer: np.ndarray,
    target_logical: np.ndarray,
    *,
    timeout: float,
) -> dict[str, Any]:
    checks = np.asarray(stabilizer, dtype=np.uint8) & 1
    target = np.asarray(target_logical, dtype=np.uint8).reshape(-1) & 1
    num_checks, two_n = checks.shape
    if two_n % 2 or target.size != two_n:
        raise ValueError("invalid symplectic dimensions")
    n = two_n // 2
    num_vars = 3 * n + num_checks + 1
    objective = np.zeros(num_vars)
    objective[2 * n:3 * n] = 1
    rows: list[np.ndarray] = []
    lower: list[float] = []
    upper: list[float] = []
    for index in range(n):
        row_x = np.zeros(num_vars)
        row_x[2 * n + index], row_x[index] = 1, -1
        rows.append(row_x)
        lower.append(0)
        upper.append(np.inf)
        row_z = np.zeros(num_vars)
        row_z[2 * n + index], row_z[n + index] = 1, -1
        rows.append(row_z)
        lower.append(0)
        upper.append(np.inf)
    for index, check in enumerate(checks):
        row = np.zeros(num_vars)
        row[:n] = check[n:]
        row[n:2 * n] = check[:n]
        row[3 * n + index] = -2
        rows.append(row)
        lower.append(0)
        upper.append(0)
    row = np.zeros(num_vars)
    row[:n] = target[n:]
    row[n:2 * n] = target[:n]
    row[-1] = -2
    rows.append(row)
    lower.append(1)
    upper.append(1)

    variable_lower = np.zeros(num_vars)
    variable_upper = np.ones(num_vars)
    for index, check in enumerate(checks):
        variable_upper[3 * n + index] = np.ceil(check.sum() / 2)
    variable_upper[-1] = np.ceil(target.sum() / 2)
    options: dict[str, Any] = {"presolve": True}
    if 0 < timeout < 1e9:
        options["time_limit"] = float(timeout)
    started = time.monotonic()
    solved = milp(
        c=objective,
        constraints=LinearConstraint(np.asarray(rows), lower, upper),
        integrality=np.ones(num_vars),
        bounds=Bounds(variable_lower, variable_upper),
        options=options,
    )
    operator = None
    if solved.x is not None:
        operator = pack_vector(np.rint(solved.x[:2 * n]).astype(np.uint8))

    def number(name: str, *, integer: bool = False):
        value = getattr(solved, name, None)
        if value is None or not np.isfinite(value):
            return None
        return int(round(value)) if integer else float(value)

    return {
        "success": bool(solved.success),
        "status": int(solved.status),
        "message": str(solved.message),
        "objective": number("fun", integer=True),
        "mip_dual_bound": number("mip_dual_bound"),
        "mip_gap": number("mip_gap"),
        "mip_node_count": number("mip_node_count", integer=True),
        "elapsed_s": time.monotonic() - started,
        "operator": operator,
    }


def verify_symplectic_direction(
    evidence: dict[str, Any],
    stabilizer: np.ndarray,
    target_logical: np.ndarray,
) -> list[str]:
    try:
        stored_target = unpack_vector(evidence["target_logical"])
        operator = unpack_vector(evidence["operator"])
    except (KeyError, TypeError, ValueError) as exc:
        return [f"invalid packed vector: {exc}"]
    checks = np.asarray(stabilizer, dtype=np.uint8) & 1
    target = np.asarray(target_logical, dtype=np.uint8).reshape(-1) & 1
    n = checks.shape[1] // 2
    failures: list[str] = []
    if not np.array_equal(stored_target, target):
        failures.append("target logical does not match reconstructed basis")
    if operator.size != 2 * n:
        return failures + ["operator width mismatch"]
    syndrome = (checks[:, :n] @ operator[n:] + checks[:, n:] @ operator[:n]) & 1
    if np.any(syndrome):
        failures.append("operator has nonzero stabilizer syndrome")
    anticommutator = int(
        (np.dot(target[:n], operator[n:]) + np.dot(target[n:], operator[:n])) & 1
    )
    if anticommutator != 1:
        failures.append("operator does not anticommute with target logical")
    objective = evidence.get("objective")
    if objective is None or int(objective) != symplectic_weight(operator):
        failures.append("objective does not equal symplectic witness weight")
    if not (
        evidence.get("success") is True
        and int(evidence.get("status", -1)) == 0
        and float(evidence.get("mip_gap", math.inf)) == 0.0
        and math.isclose(
            float(evidence.get("mip_dual_bound", math.inf)),
            float(objective), rel_tol=0.0, abs_tol=1e-7,
        )
    ):
        failures.append("stored solver result is not a zero-gap optimum")
    return failures


def _build_from_claim(claim: dict[str, Any]):
    if claim.get("symplectic_stabilizer") is not None:
        code, stabilizer = build_noncss_from_matrix(claim["symplectic_stabilizer"])
        return code, stabilizer, None, MATRIX_TYPE
    required = ("ell", "m", "A_terms", "B_terms", "C_terms", "D_terms")
    if any(name not in claim for name in required):
        raise ValueError("PBB claim requires ell,m,A_terms,B_terms,C_terms,D_terms")
    construction = {
        "ell": int(claim["ell"]),
        "m": int(claim["m"]),
        "A_terms": claim["A_terms"],
        "B_terms": claim["B_terms"],
        "C_terms": claim["C_terms"],
        "D_terms": claim["D_terms"],
    }
    code = build_pbb_code(**construction)
    if not construction["C_terms"] and not construction["D_terms"]:
        raise ValueError("non-CSS certificate requires a perturbation")
    stabilizer = np.asarray(code.matrix, dtype=np.uint8) & 1
    return code, stabilizer, construction, PBB_TYPE


def _static_gate(
    code,
    stabilizer: np.ndarray,
    *,
    distance: int,
    exact: bool,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    baseline = validate_known_answer_artifact(known_answer_artifact)
    n, k = noncss_parameters(stabilizer)
    x_part, z_part = stabilizer[:, :n], stabilizer[:, n:]
    support = (x_part | z_part).astype(np.uint8)
    connected, components = _connected(support)
    novelty = check_code_novelty(code, code_type="noncss")
    win = classify_win(n, k, distance)
    checks = {
        "known_answer_gate": baseline["passed"],
        "symplectic_commutation": not np.any(
            (x_part @ z_part.T + z_part @ x_part.T) & 1
        ),
        "positive_dimension": k > 0,
        "weight_and_degree_at_most_6": (
            int(support.sum(axis=1).max(initial=0)) <= 6
            and int(support.sum(axis=0).max(initial=0)) <= 6
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
            "max_row_weight": int(support.sum(axis=1).max(initial=0)),
            "max_qubit_degree": int(support.sum(axis=0).max(initial=0)),
            "matrix_sha256": {"symplectic": _matrix_sha256(stabilizer)},
        },
    }


def build_noncss_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
) -> dict[str, Any]:
    code, stabilizer, construction, certificate_type = _build_from_claim(claim)
    n, k = noncss_parameters(stabilizer)
    if k <= 0:
        raise ValueError("non-CSS claim must encode at least one logical qubit")
    support = stabilizer[:, :n] | stabilizer[:, n:]
    connected, _ = _connected(support)
    static_eligible = bool(
        connected
        and int(support.sum(axis=1).max(initial=0)) <= 6
        and int(support.sum(axis=0).max(initial=0)) <= 6
    )
    logicals = get_symplectic_logicals(code)
    if logicals.shape != (2 * k, 2 * n):
        raise ValueError("failed to reconstruct a complete 2k logical basis")
    directions: list[dict[str, Any]] = []
    started = time.monotonic()
    # Static challenge failures are terminal; do not spend hours on MILP.
    targets = logicals if static_eligible else np.zeros((0, 2 * n), dtype=np.uint8)
    for index, target in enumerate(targets):
        remaining = total_timeout - (time.monotonic() - started)
        if remaining <= 0:
            break
        evidence = solve_symplectic_direction(
            stabilizer, target,
            timeout=min(float(timeout_per_logical), remaining),
        )
        evidence.update({
            "logical_index": index,
            "target_logical": pack_vector(target),
        })
        directions.append(evidence)
    exact = len(directions) == 2 * k and all(
        not verify_symplectic_direction(item, stabilizer, logicals[index])
        for index, item in enumerate(directions)
    )
    objectives = [
        int(item["objective"]) for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    gate = _static_gate(
        code, stabilizer,
        distance=distance,
        exact=exact,
        known_answer_artifact=known_answer_artifact,
    )
    best = min(
        (item for item in directions if item.get("objective") is not None),
        key=lambda item: int(item["objective"]),
        default=None,
    )
    normalized_claim = {
        "source": claim.get("source"),
        "construction": construction,
        "symplectic_stabilizer": pack_matrix(stabilizer),
        "n": n,
        "k": k,
        "d": distance,
        "fom": gate["win"]["fom"],
    }
    certificate = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": certificate_type,
        "formulation": FORMULATION,
        "claim": normalized_claim,
        "matrix_sha256": {"symplectic": _matrix_sha256(stabilizer)},
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
        "upper_witness": None if best is None else {
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


def _rebuild_certificate_code(certificate: dict[str, Any]):
    claim = certificate["claim"]
    stored_code, stored_stabilizer = build_noncss_from_matrix(
        claim["symplectic_stabilizer"]
    )
    construction = claim.get("construction")
    if construction is None:
        return stored_code, stored_stabilizer
    rebuilt = build_pbb_code(**construction)
    rebuilt_matrix = np.asarray(rebuilt.matrix, dtype=np.uint8) & 1
    if not np.array_equal(rebuilt_matrix, stored_stabilizer):
        raise ValueError("PBB polynomial construction does not match bound matrix")
    return rebuilt, rebuilt_matrix


def verify_noncss_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
) -> dict[str, Any]:
    checks = {
        "schema": (
            certificate.get("schema_version") == SCHEMA_VERSION
            and certificate.get("certificate_type") in {PBB_TYPE, MATRIX_TYPE}
            and certificate.get("formulation") == FORMULATION
        ),
        "certificate_sha256": (
            certificate.get("certificate_sha256") == _certificate_sha256(certificate)
        ),
    }
    try:
        code, stabilizer = _rebuild_certificate_code(certificate)
        n, k = noncss_parameters(stabilizer)
        logicals = get_symplectic_logicals(code)
        directions = certificate["milp"]["directions"]
        checks["known_answer_sha256"] = (
            certificate["known_answer"]["artifact_sha256"]
            == _file_sha256(known_answer_artifact)
        )
        checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
            "symplectic": _matrix_sha256(stabilizer),
        }
    except (KeyError, TypeError, ValueError, OSError) as exc:
        return {
            "passed": False,
            "checks": checks,
            "failures": [f"certificate reconstruction failed: {exc}"],
        }
    claim = certificate["claim"]
    checks["claim_parameters"] = (
        int(claim.get("n", -1)) == n and int(claim.get("k", -1)) == k
    )
    checks["direction_count"] = (
        logicals.shape == (2 * k, 2 * n) and len(directions) == 2 * k
    )
    direction_failures: list[str] = []
    for index, target in enumerate(logicals):
        if index >= len(directions):
            direction_failures.append(f"logical[{index}]: missing")
            continue
        evidence = directions[index]
        local = []
        if int(evidence.get("logical_index", -1)) != index:
            local.append("identity/order mismatch")
        local.extend(verify_symplectic_direction(evidence, stabilizer, target))
        if rerun_milp:
            timeout = timeout_per_logical
            if timeout is None:
                timeout = float(certificate["solver"]["timeout_per_logical_s"])
            rerun = solve_symplectic_direction(stabilizer, target, timeout=timeout)
            if not (
                rerun["success"] is True
                and rerun["mip_gap"] == 0.0
                and rerun["objective"] == evidence.get("objective")
            ):
                local.append("rerun optimum mismatch")
        if local:
            direction_failures.append(f"logical[{index}]: " + "; ".join(local))
    checks["stored_direction_evidence"] = not direction_failures
    checks["milp_rerun"] = rerun_milp and not direction_failures
    objectives = [
        int(item["objective"]) for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    checks["distance_recomputed"] = (
        distance > 0
        and certificate["milp"].get("distance") == distance
        and int(claim.get("d", -1)) == distance
    )
    gate = _static_gate(
        code, stabilizer,
        distance=distance,
        exact=all((
            checks["direction_count"],
            checks["stored_direction_evidence"],
            checks["milp_rerun"],
        )),
        known_answer_artifact=known_answer_artifact,
    )
    checks["final_gate"] = gate["accepted"]
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    failures = [name for name, passed in checks.items() if not passed]
    failures.extend(direction_failures)
    return {
        "passed": not failures,
        "checks": checks,
        "failures": failures,
        "distance": distance,
        "directions_verified": len(logicals) - len(direction_failures),
        "directions_total": len(logicals),
        "final_gate": gate,
    }
