"""Build and independently verify exact CSS BB challenge certificates.

The certificate contains structured evidence for every one of the ``2k``
MILP minimizations, including the concrete feasible operator, target logical,
objective, dual bound, MIP gap, node count, solver status, and elapsed time.
Verification never trusts those summaries: it reconstructs the code, checks
every stored vector algebraically, and (by default) reruns all MILPs.
"""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import math
import platform
import time
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from evaluation.bb_code import build_bb_code
from evaluation.challenge_gate import evaluate_challenge_gate
from evaluation.distance_milp import get_code_matrices
from evaluation.final_gate import _matrix_sha256, _rank_f2
from evaluation.registry import check_code_novelty


SCHEMA_VERSION = 1
FORMULATION = "css-logical-anticommutation-milp-v1"


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def _highs_version() -> str | None:
    try:
        from scipy.optimize._highspy import _core
        return (
            f"{_core.HIGHS_VERSION_MAJOR}."
            f"{_core.HIGHS_VERSION_MINOR}."
            f"{_core.HIGHS_VERSION_PATCH}"
        )
    except (ImportError, AttributeError):
        return None


def _json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path | str) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _certificate_sha256(certificate: dict[str, Any]) -> str:
    unsigned = dict(certificate)
    unsigned.pop("certificate_sha256", None)
    return _json_sha256(unsigned)


def pack_vector(vector: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(vector, dtype=np.uint8).reshape(-1) & 1
    packed = np.packbits(binary, bitorder="little").tobytes()
    return {
        "length": int(binary.size),
        "weight": int(binary.sum()),
        "packed_hex": packed.hex(),
        "sha256": hashlib.sha256(
            f"{binary.size}:".encode() + packed
        ).hexdigest(),
    }


def unpack_vector(record: dict[str, Any]) -> np.ndarray:
    length = int(record["length"])
    packed = bytes.fromhex(record["packed_hex"])
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little",
    )[:length].astype(np.uint8)
    if pack_vector(vector) != record:
        raise ValueError("packed vector metadata/hash mismatch")
    return vector


def solve_css_direction(
    check_matrix: np.ndarray,
    target_logical: np.ndarray,
    *,
    timeout: float,
) -> dict[str, Any]:
    """Solve one certificate MILP and retain its concrete optimizer."""
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    logical = np.asarray(target_logical, dtype=np.uint8).reshape(-1) & 1
    num_checks, n = checks.shape
    if logical.size != n:
        raise ValueError("logical/check width mismatch")

    num_vars = n + num_checks + 1
    objective = np.zeros(num_vars)
    objective[:n] = 1
    matrix = np.zeros((num_checks + 1, num_vars))
    matrix[:num_checks, :n] = checks
    matrix[:num_checks, n:n + num_checks] = -2 * np.eye(num_checks)
    matrix[num_checks, :n] = logical
    matrix[num_checks, -1] = -2
    rhs = np.zeros(num_checks + 1)
    rhs[-1] = 1

    lower = np.zeros(num_vars)
    upper = np.ones(num_vars)
    upper[n:n + num_checks] = np.ceil(checks.sum(axis=1) / 2)
    upper[-1] = np.ceil(logical.sum() / 2)
    options: dict[str, Any] = {"presolve": True}
    if 0 < timeout < 1e9:
        options["time_limit"] = float(timeout)

    started = time.monotonic()
    solved = milp(
        c=objective,
        constraints=LinearConstraint(matrix, rhs, rhs),
        integrality=np.ones(num_vars),
        bounds=Bounds(lower, upper),
        options=options,
    )
    elapsed = time.monotonic() - started
    operator = None
    if solved.x is not None:
        rounded = np.rint(solved.x[:n]).astype(np.uint8)
        operator = pack_vector(rounded)

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
        "elapsed_s": elapsed,
        "operator": operator,
    }


def verify_css_witness(
    evidence: dict[str, Any],
    check_matrix: np.ndarray,
    target_logical: np.ndarray,
) -> list[str]:
    """Check a stored CSS operator algebraically, without trusting solver status."""
    try:
        operator = unpack_vector(evidence["operator"])
    except (KeyError, TypeError, ValueError) as exc:
        return [f"invalid packed vector: {exc}"]
    target = np.asarray(target_logical, dtype=np.uint8).reshape(-1) & 1
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    failures: list[str] = []
    if operator.size != checks.shape[1]:
        return ["operator width mismatch"]
    if np.any((checks @ operator) & 1):
        failures.append("operator has nonzero stabilizer syndrome")
    if int(np.dot(target, operator) & 1) != 1:
        failures.append("operator does not anticommute with target logical")
    objective = evidence.get("objective")
    if objective is None or int(objective) != int(operator.sum()):
        failures.append("objective does not equal operator weight")
    return failures


def verify_direction_evidence(
    evidence: dict[str, Any],
    check_matrix: np.ndarray,
    target_logical: np.ndarray,
) -> list[str]:
    failures = verify_css_witness(evidence, check_matrix, target_logical)
    try:
        stored_target = unpack_vector(evidence["target_logical"])
    except (KeyError, TypeError, ValueError) as exc:
        failures.append(f"invalid target logical: {exc}")
        stored_target = None
    target = np.asarray(target_logical, dtype=np.uint8).reshape(-1) & 1
    if stored_target is not None and not np.array_equal(stored_target, target):
        failures.append("target logical does not match reconstructed basis")
    objective = evidence.get("objective")
    if not (
        evidence.get("success") is True
        and int(evidence.get("status", -1)) == 0
        and objective is not None
        and float(evidence.get("mip_gap", math.inf)) == 0.0
        and math.isclose(
            float(evidence.get("mip_dual_bound", math.inf)),
            float(objective), rel_tol=0.0, abs_tol=1e-7,
        )
    ):
        failures.append("stored solver result is not a zero-gap optimum")
    return failures


def _direction_specs(code) -> list[tuple[str, int, str, np.ndarray, np.ndarray]]:
    hx, hz, lx, lz = get_code_matrices(code)
    hx = np.asarray(hx, dtype=np.uint8) & 1
    hz = np.asarray(hz, dtype=np.uint8) & 1
    lx = np.asarray(lx, dtype=np.uint8) & 1
    lz = np.asarray(lz, dtype=np.uint8) & 1
    specs = [
        ("Z", index, "hx", hx, lx[index])
        for index in range(len(lx))
    ]
    specs += [
        ("X", index, "hz", hz, lz[index])
        for index in range(len(lz))
    ]
    return specs


def build_css_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
) -> dict[str, Any]:
    """Recompute a claim and produce full per-direction solver evidence."""
    if claim.get("C_terms") or claim.get("D_terms"):
        raise ValueError("CSS certificate builder does not accept PBB/non-CSS claims")
    ell, m = int(claim["ell"]), int(claim["m"])
    a_terms, b_terms = claim["A_terms"], claim["B_terms"]
    code = build_bb_code(ell, m, a_terms, b_terms)
    hx, hz, _, _ = get_code_matrices(code)
    hx = np.asarray(hx, dtype=np.uint8) & 1
    hz = np.asarray(hz, dtype=np.uint8) & 1
    n = int(code.num_qudits)
    k = n - _rank_f2(hx) - _rank_f2(hz)

    directions = []
    started = time.monotonic()
    for logical_type, index, check_name, checks, target in _direction_specs(code):
        remaining = total_timeout - (time.monotonic() - started)
        if remaining <= 0:
            break
        evidence = solve_css_direction(
            checks, target,
            timeout=min(float(timeout_per_logical), remaining),
        )
        evidence.update({
            "logical_type": logical_type,
            "logical_index": index,
            "check_matrix": check_name,
            "target_logical": pack_vector(target),
        })
        directions.append(evidence)

    expected_count = 2 * k
    all_optimal = (
        len(directions) == expected_count
        and all(not verify_direction_evidence(
            item,
            hx if item["check_matrix"] == "hx" else hz,
            unpack_vector(item["target_logical"]),
        ) for item in directions)
    )
    z_values = [
        int(item["objective"]) for item in directions
        if item["logical_type"] == "Z" and item["objective"] is not None
    ]
    x_values = [
        int(item["objective"]) for item in directions
        if item["logical_type"] == "X" and item["objective"] is not None
    ]
    d_z = min(z_values) if z_values else 0
    d_x = min(x_values) if x_values else 0
    distance = min(d_z, d_x) if d_z and d_x else 0
    novelty = check_code_novelty(code, code_type="css")
    normalized_claim = {
        **claim,
        "ell": ell,
        "m": m,
        "n": n,
        "k": k,
        "d": distance,
        "fom": k * distance * distance / n if distance else 0.0,
        "d_is_exact": all_optimal,
        "milp_attempted": True,
        "milp_details": {
            "exact": all_optimal,
            "total_logicals": expected_count,
            "num_logicals_checked": len(directions),
            "logicals_optimal": sum(
                item["success"] is True and item["mip_gap"] == 0.0
                for item in directions
            ),
            "logicals_incumbent": sum(
                item["operator"] is not None and not item["success"]
                for item in directions
            ),
        },
        "structural_novelty": novelty,
    }
    final_gate = evaluate_challenge_gate(
        normalized_claim,
        known_answer_artifact=known_answer_artifact,
    )
    best = min(
        (item for item in directions if item["objective"] is not None),
        key=lambda item: int(item["objective"]),
        default=None,
    )
    certificate = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": "qldpc-css-bb-exact",
        "formulation": FORMULATION,
        "claim": normalized_claim,
        "matrix_sha256": {
            "hx": _matrix_sha256(hx),
            "hz": _matrix_sha256(hz),
        },
        "known_answer": {
            "artifact_sha256": _file_sha256(known_answer_artifact),
        },
        "solver": {
            "interface": "scipy.optimize.milp",
            "backend": "HiGHS",
            "scipy_version": _package_version("scipy"),
            "highs_version": _highs_version(),
            "presolve": True,
            "timeout_per_logical_s": timeout_per_logical,
            "total_timeout_s": total_timeout,
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": _package_version("numpy"),
            "qldpc": _package_version("qldpc"),
        },
        "milp": {
            "exact": all_optimal,
            "expected_directions": expected_count,
            "completed_directions": len(directions),
            "d_x": d_x,
            "d_z": d_z,
            "distance": distance,
            "elapsed_s": time.monotonic() - started,
            "directions": directions,
        },
        "upper_witness": None if best is None else {
            "logical_type": best["logical_type"],
            "logical_index": best["logical_index"],
            "weight": best["objective"],
            "operator": best["operator"],
            "target_logical": best["target_logical"],
        },
        "final_gate": final_gate,
        "passed": bool(all_optimal and final_gate.get("accepted")),
    }
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def verify_css_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
) -> dict[str, Any]:
    """Verify integrity, static evidence, and optionally every MILP optimum."""
    failures: list[str] = []
    checks: dict[str, bool] = {}
    checks["schema"] = (
        certificate.get("schema_version") == SCHEMA_VERSION
        and certificate.get("certificate_type") == "qldpc-css-bb-exact"
        and certificate.get("formulation") == FORMULATION
    )
    checks["certificate_sha256"] = (
        certificate.get("certificate_sha256") == _certificate_sha256(certificate)
    )
    try:
        checks["known_answer_sha256"] = (
            certificate["known_answer"]["artifact_sha256"]
            == _file_sha256(known_answer_artifact)
        )
        claim = certificate["claim"]
        code = build_bb_code(
            int(claim["ell"]), int(claim["m"]),
            claim["A_terms"], claim["B_terms"],
        )
        hx, hz, _, _ = get_code_matrices(code)
        hx = np.asarray(hx, dtype=np.uint8) & 1
        hz = np.asarray(hz, dtype=np.uint8) & 1
        checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
            "hx": _matrix_sha256(hx), "hz": _matrix_sha256(hz),
        }
        specs = _direction_specs(code)
        directions = certificate["milp"]["directions"]
    except (KeyError, TypeError, ValueError, OSError) as exc:
        failures.append(f"certificate reconstruction failed: {exc}")
        return {"passed": False, "checks": checks, "failures": failures}

    checks["direction_count"] = len(directions) == len(specs) == 2 * int(code.dimension)
    direction_failures: list[dict[str, Any]] = []
    rerun_matches = True
    for position, spec in enumerate(specs):
        logical_type, index, check_name, checks_matrix, target = spec
        if position >= len(directions):
            direction_failures.append({"position": position, "failures": ["missing"]})
            rerun_matches = False
            continue
        evidence = directions[position]
        local = []
        if (
            evidence.get("logical_type") != logical_type
            or int(evidence.get("logical_index", -1)) != index
            or evidence.get("check_matrix") != check_name
        ):
            local.append("direction identity/order mismatch")
        local.extend(verify_direction_evidence(evidence, checks_matrix, target))
        if rerun_milp:
            timeout = timeout_per_logical
            if timeout is None:
                timeout = float(
                    certificate.get("solver", {}).get("timeout_per_logical_s", 300)
                )
            rerun = solve_css_direction(checks_matrix, target, timeout=timeout)
            if not (
                rerun["success"] is True
                and rerun["mip_gap"] == 0.0
                and rerun["objective"] == evidence.get("objective")
            ):
                local.append(
                    "rerun optimum mismatch: "
                    f"stored={evidence.get('objective')} rerun={rerun.get('objective')}"
                )
                rerun_matches = False
        if local:
            direction_failures.append({
                "logical_type": logical_type,
                "logical_index": index,
                "failures": local,
            })

    checks["stored_direction_evidence"] = not direction_failures
    checks["milp_rerun"] = rerun_matches if rerun_milp else False
    objectives = [
        int(item["objective"]) for item in directions
        if item.get("objective") is not None
    ]
    stored_distance = certificate.get("milp", {}).get("distance")
    checks["distance_recomputed"] = bool(
        objectives and stored_distance == min(objectives)
        and int(claim.get("d", -1)) == min(objectives)
    )
    gate = evaluate_challenge_gate(
        claim,
        known_answer_artifact=known_answer_artifact,
    )
    checks["final_gate"] = gate.get("accepted") is True
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    for name, passed in checks.items():
        if not passed:
            failures.append(name)
    failures.extend(
        f"{item.get('logical_type', '?')}[{item.get('logical_index', item['position'] if 'position' in item else '?')}]: "
        + "; ".join(item["failures"])
        for item in direction_failures
    )
    return {
        "passed": not failures,
        "checks": checks,
        "failures": failures,
        "distance": stored_distance,
        "directions_verified": len(specs) - len(direction_failures),
        "directions_total": len(specs),
        "final_gate": gate,
    }
