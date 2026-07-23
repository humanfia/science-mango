"""Fail-closed final acceptance gate for the qLDPC challenge.

Discovery records are untrusted inputs.  This module rebuilds every CSS BB
candidate, recomputes its static parameters, reruns the structural-novelty
audit, and accepts a challenge claim only when:

* the frozen known-answer artifact passed all three required baselines;
* the candidate is a valid, connected CSS code with check weight and qubit
  degree at most six;
* its reported ``n`` and ``k`` agree with independent recomputation;
* all ``2k`` MILP logical directions were solved to proven optimality;
* it is structurally novel against the known CSS registry; and
* it beats the scalar threshold or one of the stated Pareto fronts.

Missing or malformed evidence is always a rejection, never a warning.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.distance_milp import get_code_matrices
from evaluation.registry import check_code_novelty
from evaluation.structural_dedup import check_css_structural_novelty


FOM_THRESHOLD = 12.0
REQUIRED_BASELINES = {
    "[[72,12,6]]": (72, 12, 6),
    "[[90,8,10]]": (90, 8, 10),
    "[[144,12,12]]": (144, 12, 12),
}
KNOWN_PARETO_REFERENCES = (
    (72, 12, 6),
    (90, 8, 10),
    (108, 8, 10),
    (144, 12, 12),
    (288, 12, 18),
)


def _rank_f2(matrix: np.ndarray) -> int:
    work = np.asarray(matrix, dtype=np.uint8).copy() & 1
    rows, cols = work.shape
    rank = 0
    for col in range(cols):
        pivots = np.flatnonzero(work[rank:, col])
        if not pivots.size:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            work[[rank, pivot]] = work[[pivot, rank]]
        other = np.flatnonzero(work[:, col])
        other = other[other != rank]
        if other.size:
            work[other] ^= work[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def _matrix_sha256(matrix: np.ndarray) -> str:
    binary = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def _connected(checks: np.ndarray) -> tuple[bool, int]:
    matrix = np.asarray(checks, dtype=np.uint8) & 1
    num_checks, num_qubits = matrix.shape
    adjacency = [[] for _ in range(num_checks + num_qubits)]
    for check_idx, qubit_idx in np.argwhere(matrix):
        left = int(check_idx)
        right = num_checks + int(qubit_idx)
        adjacency[left].append(right)
        adjacency[right].append(left)
    unseen = set(range(len(adjacency)))
    components = 0
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            node = stack.pop()
            for neighbor in adjacency[node]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
    return components == 1, components


def validate_known_answer_artifact(path: Path | str) -> dict[str, Any]:
    """Validate the baseline artifact without trusting its top-level flag."""
    path = Path(path)
    failures: list[str] = []
    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "passed": False,
            "path": str(path),
            "failures": [f"known-answer artifact unavailable or invalid: {exc}"],
        }

    if artifact.get("schema_version") != 1:
        failures.append("known-answer schema_version must be 1")
    if artifact.get("gate") != "qldpc-known-answer-baselines":
        failures.append("unexpected known-answer gate identifier")
    records = artifact.get("baselines")
    if not isinstance(records, list):
        records = []
        failures.append("known-answer baselines must be a list")

    by_label = {
        row.get("label"): row for row in records if isinstance(row, dict)
    }
    if set(by_label) != set(REQUIRED_BASELINES):
        failures.append("known-answer artifact must contain exactly the three required baselines")
    for label, expected in REQUIRED_BASELINES.items():
        row = by_label.get(label)
        if not row:
            continue
        observed = row.get("observed") or {}
        if tuple(observed.get(name) for name in ("n", "k", "d")) != expected:
            failures.append(f"{label}: observed parameters do not match {expected}")
        checks = row.get("checks")
        if (
            row.get("status") != "passed"
            or not isinstance(checks, dict)
            or not checks
            or not all(value is True for value in checks.values())
        ):
            failures.append(f"{label}: one or more baseline checks failed")
        milp = row.get("milp") or {}
        total = 2 * expected[1]
        if not (
            milp.get("exact") is True
            and int(milp.get("total_logicals", 0)) == total
            and int(milp.get("num_logicals_checked", 0)) == total
            and int(milp.get("logicals_optimal", 0)) == total
            and int(milp.get("logicals_incumbent", 0)) == 0
        ):
            failures.append(f"{label}: MILP did not prove all 2k directions optimal")

    if artifact.get("passed") is not True:
        failures.append("known-answer top-level result is not passed")
    summary = artifact.get("summary") or {}
    if summary.get("passed") != 3 or summary.get("total") != 3:
        failures.append("known-answer summary is not 3/3")
    return {
        "passed": not failures,
        "path": str(path.resolve()),
        "generated_at": artifact.get("generated_at"),
        "failures": failures,
    }


def _exact_milp_check(row: dict[str, Any], k: int) -> bool:
    details = row.get("milp_details")
    total = 2 * k
    return bool(
        row.get("milp_attempted") is True
        and row.get("d_is_exact") is True
        and isinstance(details, dict)
        and details.get("exact") is True
        and int(details.get("total_logicals", 0)) == total
        and int(details.get("num_logicals_checked", 0)) == total
        and int(details.get("logicals_optimal", 0)) == total
        and int(details.get("logicals_incumbent", 0)) == 0
    )


def classify_win(n: int, k: int, d: int) -> dict[str, Any]:
    """Apply the scalar and explicit fixed-coordinate Pareto win rules."""
    fom = k * d * d / n if n > 0 else 0.0
    reasons: list[str] = []
    if fom > FOM_THRESHOLD:
        reasons.append("fom_strictly_above_12")
    for ref_n, ref_k, ref_d in KNOWN_PARETO_REFERENCES:
        ref_fom = ref_k * ref_d * ref_d / ref_n
        label = f"[[{ref_n},{ref_k},{ref_d}]]"
        if math.isclose(fom, ref_fom, rel_tol=0.0, abs_tol=1e-12) and n < ref_n:
            reasons.append(f"same_fom_smaller_n_than_{label}")
        if n == ref_n and d == ref_d and k > ref_k:
            reasons.append(f"higher_k_than_{label}_with_n_d_fixed")
        if n == ref_n and k == ref_k and d > ref_d:
            reasons.append(f"higher_d_than_{label}_with_n_k_fixed")
    return {"passed": bool(reasons), "fom": fom, "reasons": reasons}


def evaluate_final_gate(
    row: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    """Rebuild and evaluate one CSS BB discovery record."""
    baseline = validate_known_answer_artifact(known_answer_artifact)
    checks: dict[str, bool] = {"known_answer_gate": baseline["passed"]}
    failures = list(baseline["failures"])
    result: dict[str, Any] = {
        "schema_version": 1,
        "gate": "qldpc-challenge-final",
        "accepted": False,
        "checks": checks,
        "failures": failures,
        "known_answer": baseline,
    }

    try:
        ell, m = int(row["ell"]), int(row["m"])
        a_terms, b_terms = row["A_terms"], row["B_terms"]
        validate_terms(ell, m, a_terms, "A")
        validate_terms(ell, m, b_terms, "B")
        code = build_bb_code(ell, m, a_terms, b_terms)
    except (KeyError, TypeError, ValueError) as exc:
        checks["candidate_rebuild"] = False
        failures.append(f"candidate cannot be rebuilt: {exc}")
        return result

    checks["candidate_rebuild"] = True
    hx, hz, _, _ = get_code_matrices(code)
    hx = np.asarray(hx, dtype=np.uint8) & 1
    hz = np.asarray(hz, dtype=np.uint8) & 1
    stacked = np.vstack((hx, hz))
    n = int(code.num_qudits)
    rank_hx, rank_hz = _rank_f2(hx), _rank_f2(hz)
    k = n - rank_hx - rank_hz
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    connected, components = _connected(stacked)

    checks.update({
        "css_commutation": int(np.count_nonzero((hx @ hz.T) & 1)) == 0,
        "weight_and_degree_at_most_6": max_row_weight <= 6 and max_qubit_degree <= 6,
        "connected_tanner_graph": connected,
        "reported_n_matches": int(row.get("n", -1)) == n,
        "reported_k_matches": int(row.get("k", -1)) == k,
        "qldpc_k_crosscheck": int(code.dimension) == k,
    })

    d = int(row.get("d", 0) or 0)
    checks["positive_reported_distance"] = d > 0
    checks["all_2k_milp_directions_optimal"] = _exact_milp_check(row, k)

    reported_audit = row.get("structural_novelty")
    recomputed_audit = check_css_structural_novelty(ell, m, a_terms, b_terms)
    expanded_audit = check_code_novelty(code, code_type="css")
    checks["structural_audit_present"] = bool(
        isinstance(reported_audit, dict)
        and reported_audit.get("checked") is True
        and reported_audit.get("novel") is True
    )
    checks["structural_audit_reproduced"] = bool(
        recomputed_audit.get("novel") is True
        and isinstance(reported_audit, dict)
        and reported_audit.get("canonical_digest") == recomputed_audit.get("canonical_digest")
    )
    checks["expanded_registry_novel"] = bool(
        expanded_audit.get("novel") is True
        and isinstance(reported_audit, dict)
        and reported_audit.get("registry_sha256") == expanded_audit.get("registry_sha256")
    )

    win = classify_win(n, k, d)
    checks["challenge_win"] = win["passed"]
    reported_fom = row.get("fom")
    checks["reported_fom_matches"] = bool(
        isinstance(reported_fom, (int, float))
        and math.isclose(float(reported_fom), win["fom"], rel_tol=0.0, abs_tol=1e-9)
    )

    for name, passed in checks.items():
        if not passed and name != "known_answer_gate":
            failures.append(name)
    result.update({
        "accepted": not failures,
        "candidate": {
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
            "n": n,
            "k": k,
            "d": d,
            "fom": win["fom"],
            "rank_hx": rank_hx,
            "rank_hz": rank_hz,
            "max_row_weight": max_row_weight,
            "max_qubit_degree": max_qubit_degree,
            "tanner_components": components,
            "matrix_sha256": {
                "hx": _matrix_sha256(hx),
                "hz": _matrix_sha256(hz),
            },
        },
        "structural_novelty": recomputed_audit,
        "expanded_structural_novelty": expanded_audit,
        "win": win,
    })
    return result
