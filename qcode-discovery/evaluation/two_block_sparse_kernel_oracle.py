"""Proof-safe single-block short-logical oracle for two-block CSS codes.

For a CSS sector with commutation matrix ``H`` and logical detector ``L``, a
logical operator supported only on coordinate block ``I`` is exactly a vector

``x in ker(H[:, I])`` with ``L[:, I] x != 0``.

This module solves those sparse-kernel problems for both CSS sectors and both
coordinate blocks before the unrestricted Stage-3 search.  A SAT result is a
full-code logical witness and therefore safely rejects a candidate.  Four
UNSAT results prove only that no *single-block* witness exists through the
requested weight.  They never become a lower bound on the unrestricted code
distance, where a logical may span both blocks.
"""

from __future__ import annotations

import hashlib
import json
import math
import time
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.css_logical_detector import verify_css_logical_detectors
from evaluation.distance_sat import css_sector_matrices
from evaluation import low_weight_oracle as _sector_oracle


TWO_BLOCK_SPARSE_KERNEL_KIND = "qcode-css-two-block-sparse-kernel-oracle"
TWO_BLOCK_SPARSE_KERNEL_SCHEMA_VERSION = 1
TWO_BLOCK_SPARSE_KERNEL_METHOD = "restricted-column-kernel-logical-sat-v1"
TWO_BLOCK_SPARSE_KERNEL_OUTCOMES = frozenset(
    {"SAT", "NO_SINGLE_BLOCK_WITNESS", "UNKNOWN"}
)
_QUERY_ORDER = (("X", "A"), ("X", "B"), ("Z", "A"), ("Z", "B"))
_KERNEL_COMPONENT = {
    ("X", "A"): "B^T",
    ("X", "B"): "A^T",
    ("Z", "A"): "A",
    ("Z", "B"): "B",
}

try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode("ascii"))
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _dependency_source_sha256() -> str:
    try:
        digest = hashlib.sha256(Path(_sector_oracle.__file__).read_bytes()).hexdigest()
    except (OSError, TypeError) as exc:
        raise RuntimeError("cannot fingerprint low_weight_oracle.py") from exc
    return digest


def _validated_problem(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    block_size: int | None,
    max_weight: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, int, int]:
    matrices = tuple(
        np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
        for value in (hx, hz, lx, lz)
    )
    matrix_x, matrix_z, logical_x, logical_z = matrices
    if any(value.ndim != 2 for value in matrices):
        raise ValueError("CSS checks and logical detectors must be matrices")
    n = int(matrix_x.shape[1])
    if n < 2 or any(value.shape[1] != n for value in matrices[1:]):
        raise ValueError("CSS matrices have incompatible column dimensions")
    if isinstance(block_size, bool):
        raise ValueError("block_size must be an integer")
    selected_block_size = n // 2 if block_size is None else int(block_size)
    if selected_block_size < 1 or n != 2 * selected_block_size:
        raise ValueError("candidate is not an equal-size two-block CSS code")
    if isinstance(max_weight, bool) or not isinstance(
        max_weight, (int, np.integer)
    ):
        raise ValueError("max_weight must be an integer")
    threshold = int(max_weight)
    if threshold < 0:
        raise ValueError("max_weight must be nonnegative")
    return (*matrices, selected_block_size, threshold)


def _binding(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    block_size: int,
    max_weight: int,
) -> dict[str, Any]:
    if _SOURCE_SHA256 is None:
        raise RuntimeError("cannot fingerprint two_block_sparse_kernel_oracle.py")
    n = int(hx.shape[1])
    result = {
        "method": TWO_BLOCK_SPARSE_KERNEL_METHOD,
        "source_sha256": _SOURCE_SHA256,
        "low_weight_oracle_source_sha256": _dependency_source_sha256(),
        "n": n,
        "block_size": block_size,
        "block_layout": {
            "A": [0, block_size],
            "B": [block_size, n],
        },
        "max_weight": max_weight,
        "matrix_sha256": {
            "hx": _array_sha256("hx", hx),
            "hz": _array_sha256("hz", hz),
            "lx": _array_sha256("lx", lx),
            "lz": _array_sha256("lz", lz),
        },
    }
    result["binding_sha256"] = _canonical_sha256(result)
    return result


def _query_problem(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    sector: str,
    block: str,
    block_size: int,
) -> tuple[np.ndarray, np.ndarray, int]:
    checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
    start = 0 if block == "A" else block_size
    stop = start + block_size
    return (
        np.ascontiguousarray(checks[:, start:stop]),
        np.ascontiguousarray(logicals[:, start:stop]),
        start,
    )


def _query_plan(block_size: int) -> list[dict[str, Any]]:
    """Describe the four exact A/B sparse-kernel predicates."""

    return [
        {
            "query_id": f"{sector}:{block}",
            "sector": sector,
            "coordinate_block": block,
            "coordinate_range": (
                [0, block_size]
                if block == "A"
                else [block_size, 2 * block_size]
            ),
            "kernel_component": _KERNEL_COMPONENT[(sector, block)],
        }
        for sector, block in _QUERY_ORDER
    ]


def _lift_witness(
    witness: Mapping[str, Any],
    *,
    query_id: str,
    block: str,
    start: int,
    n: int,
    checks: np.ndarray,
    logicals: np.ndarray,
    max_weight: int,
) -> dict[str, Any]:
    bits = witness.get("bits")
    block_size = n // 2
    if (
        not isinstance(bits, list)
        or len(bits) != block_size
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
    ):
        raise ValueError("restricted witness bits are invalid")
    vector = np.zeros(n, dtype=np.uint8)
    vector[start : start + block_size] = np.asarray(bits, dtype=np.uint8)
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    weight = int(vector.sum())
    if (
        not 1 <= weight <= max_weight
        or np.any((checks @ vector) & 1)
        or not any(syndrome)
    ):
        raise ValueError("restricted witness does not lift to a full CSS logical")
    return {
        "query_id": query_id,
        "side": witness.get("side"),
        "index": next(index for index, bit in enumerate(syndrome) if bit),
        "block": block,
        "block_index": 0 if block == "A" else 1,
        "kernel_component": _KERNEL_COMPONENT[(str(witness.get("side")), block)],
        "weight": weight,
        "bits": vector.astype(int).tolist(),
        "logical_syndrome": syndrome,
        "support": [int(index) for index in np.flatnonzero(vector)],
        "block_support": [int(index) for index in np.flatnonzero(bits)],
    }


def _seal(evidence: dict[str, Any]) -> dict[str, Any]:
    unsigned = dict(evidence)
    unsigned.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = _canonical_sha256(unsigned)
    return evidence


def evaluate_two_block_sparse_kernel_oracle(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    block_size: int | None = None,
    hard_timeout_s: float = 30.0,
    terminal_queries: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Search both CSS sectors for logicals confined to block A or B."""

    matrix_x, matrix_z, logical_x, logical_z, block, threshold = (
        _validated_problem(
            hx,
            hz,
            lx,
            lz,
            block_size=block_size,
            max_weight=max_weight,
        )
    )
    timeout = float(hard_timeout_s)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("hard_timeout_s must be positive and finite")
    started = time.monotonic()
    detector = verify_css_logical_detectors(
        matrix_x, matrix_z, logical_x, logical_z
    )
    binding = _binding(
        matrix_x,
        matrix_z,
        logical_x,
        logical_z,
        block_size=block,
        max_weight=threshold,
    )
    queries: dict[str, dict[str, Any]] = {}
    witness: dict[str, Any] | None = None
    message: str | None = None

    if detector.get("verified") is True:
        reusable = terminal_queries if isinstance(terminal_queries, Mapping) else {}
        for sector, block_name in _QUERY_ORDER:
            query_id = f"{sector}:{block_name}"
            checks, logicals, start = _query_problem(
                matrix_x,
                matrix_z,
                logical_x,
                logical_z,
                sector=sector,
                block=block_name,
                block_size=block,
            )
            cached = reusable.get(query_id)
            if (
                isinstance(cached, Mapping)
                and cached.get("outcome") in {"SAT", "UNSAT"}
                and not _sector_oracle.verify_low_weight_sector_evidence(
                    cached,
                    checks,
                    logicals,
                    max_weight=threshold,
                    sector=sector,
                )
            ):
                query = json.loads(json.dumps(cached, allow_nan=False))
            else:
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    message = "single-block oracle wall budget was exhausted"
                    break
                query = _sector_oracle.evaluate_low_weight_sector(
                    checks,
                    logicals,
                    max_weight=threshold,
                    sector=sector,
                    hard_timeout_s=remaining,
                )
            queries[query_id] = query
            if query.get("outcome") == "SAT":
                full_checks, full_logicals = css_sector_matrices(
                    matrix_x, matrix_z, logical_x, logical_z, sector
                )
                witness = _lift_witness(
                    query["witness"],
                    query_id=query_id,
                    block=block_name,
                    start=start,
                    n=int(matrix_x.shape[1]),
                    checks=full_checks,
                    logicals=full_logicals,
                    max_weight=threshold,
                )
                break
    else:
        message = "CSS logical detector completeness replay failed"

    all_unsat = len(queries) == len(_QUERY_ORDER) and all(
        queries[f"{sector}:{block_name}"].get("outcome") == "UNSAT"
        for sector, block_name in _QUERY_ORDER
    )
    if witness is not None:
        outcome = "SAT"
    elif all_unsat:
        outcome = "NO_SINGLE_BLOCK_WITNESS"
    else:
        outcome = "UNKNOWN"
        message = message or "one or more single-block queries are unresolved"
    terminal = outcome != "UNKNOWN"
    return _seal({
        "schema_version": TWO_BLOCK_SPARSE_KERNEL_SCHEMA_VERSION,
        "kind": TWO_BLOCK_SPARSE_KERNEL_KIND,
        "method": TWO_BLOCK_SPARSE_KERNEL_METHOD,
        "source_sha256": _SOURCE_SHA256,
        "outcome": outcome,
        "decision_complete": terminal,
        "retryable": not terminal,
        "scope": "single-coordinate-block-support-only",
        "max_weight": threshold,
        "distance_lower_bound": None,
        "distance_upper_bound": (
            witness["weight"] if witness is not None else None
        ),
        "single_block_minimum_weight_lower_bound": (
            threshold + 1 if all_unsat else None
        ),
        "witness": witness,
        "query_plan": _query_plan(block),
        "queries": queries,
        "binding": binding,
        "logical_detector": detector,
        "message": message,
        "elapsed_s": time.monotonic() - started,
    })


def verify_two_block_sparse_kernel_oracle(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    block_size: int | None = None,
    require_current_source: bool = True,
    replay_mitm_unsat: bool = True,
) -> list[str]:
    """Replay a single-block artifact without trusting its summaries."""

    if not isinstance(evidence, Mapping):
        return ["single-block oracle evidence is not an object"]
    threshold = evidence.get("max_weight")
    try:
        matrix_x, matrix_z, logical_x, logical_z, block, max_weight = (
            _validated_problem(
                hx,
                hz,
                lx,
                lz,
                block_size=block_size,
                max_weight=threshold,
            )
        )
    except (TypeError, ValueError) as exc:
        return [f"single-block oracle matrices are invalid: {exc}"]
    failures: list[str] = []
    unsigned = dict(evidence)
    evidence_sha256 = unsigned.pop("evidence_sha256", None)
    try:
        if evidence_sha256 != _canonical_sha256(unsigned):
            failures.append("single-block oracle evidence self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("single-block oracle evidence is not strict JSON")

    outcome = evidence.get("outcome")
    terminal = outcome in {"SAT", "NO_SINGLE_BLOCK_WITNESS"}
    if not (
        evidence.get("schema_version")
        == TWO_BLOCK_SPARSE_KERNEL_SCHEMA_VERSION
        and evidence.get("kind") == TWO_BLOCK_SPARSE_KERNEL_KIND
        and evidence.get("method") == TWO_BLOCK_SPARSE_KERNEL_METHOD
        and outcome in TWO_BLOCK_SPARSE_KERNEL_OUTCOMES
        and evidence.get("decision_complete") is terminal
        and evidence.get("retryable") is (not terminal)
        and evidence.get("scope") == "single-coordinate-block-support-only"
        and evidence.get("distance_lower_bound") is None
    ):
        failures.append("single-block oracle schema or decision semantics are invalid")
        if outcome not in TWO_BLOCK_SPARSE_KERNEL_OUTCOMES:
            return failures
    declared_source = evidence.get("source_sha256")
    if (
        not isinstance(declared_source, str)
        or len(declared_source) != 64
        or any(character not in "0123456789abcdef" for character in declared_source)
    ):
        failures.append("single-block oracle source binding is invalid")
    elif require_current_source and declared_source != _SOURCE_SHA256:
        failures.append("single-block oracle source binding mismatch")
    if evidence.get("query_plan") != _query_plan(block):
        failures.append("single-block sparse-kernel query plan is invalid")
    if not require_current_source and outcome != "SAT":
        failures.append(
            "historical-source relaxation is restricted to SAT upper-bound witnesses"
        )
    expected_binding = _binding(
        matrix_x,
        matrix_z,
        logical_x,
        logical_z,
        block_size=block,
        max_weight=max_weight,
    )
    if evidence.get("binding") != expected_binding:
        failures.append("single-block oracle matrix/source binding mismatch")
    detector = verify_css_logical_detectors(
        matrix_x, matrix_z, logical_x, logical_z
    )
    if evidence.get("logical_detector") != detector:
        failures.append("single-block oracle logical detector report does not replay")
    if terminal and detector.get("verified") is not True:
        failures.append("terminal single-block evidence has invalid detectors")

    queries = evidence.get("queries")
    if not isinstance(queries, Mapping):
        failures.append("single-block query evidence is missing")
        return failures
    expected_ids = [f"{sector}:{name}" for sector, name in _QUERY_ORDER]
    observed_ids = list(queries)
    if observed_ids != expected_ids[: len(observed_ids)]:
        failures.append("single-block queries are not a canonical prefix")

    sat_witnesses: list[dict[str, Any]] = []
    query_outcomes: dict[str, str] = {}
    for sector, block_name in _QUERY_ORDER:
        query_id = f"{sector}:{block_name}"
        if query_id not in queries:
            continue
        query = queries[query_id]
        checks, logicals, start = _query_problem(
            matrix_x,
            matrix_z,
            logical_x,
            logical_z,
            sector=sector,
            block=block_name,
            block_size=block,
        )
        query_failures = _sector_oracle.verify_low_weight_sector_evidence(
            query,
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
            require_current_source=require_current_source,
            replay_mitm_unsat=replay_mitm_unsat,
        )
        failures.extend(f"{query_id}: {failure}" for failure in query_failures)
        if isinstance(query, Mapping):
            query_outcomes[query_id] = str(query.get("outcome"))
            if query.get("outcome") == "SAT" and not query_failures:
                full_checks, full_logicals = css_sector_matrices(
                    matrix_x, matrix_z, logical_x, logical_z, sector
                )
                try:
                    sat_witnesses.append(
                        _lift_witness(
                            query["witness"],
                            query_id=query_id,
                            block=block_name,
                            start=start,
                            n=int(matrix_x.shape[1]),
                            checks=full_checks,
                            logicals=full_logicals,
                            max_weight=max_weight,
                        )
                    )
                except (KeyError, TypeError, ValueError) as exc:
                    failures.append(f"{query_id}: full witness lift failed: {exc}")

    all_unsat = query_outcomes == {
        query_id: "UNSAT" for query_id in expected_ids
    }
    if outcome == "SAT":
        if (
            len(sat_witnesses) != 1
            or evidence.get("witness") != sat_witnesses[0]
            or evidence.get("distance_upper_bound")
            != sat_witnesses[0]["weight"]
            or evidence.get("single_block_minimum_weight_lower_bound") is not None
        ):
            failures.append("single-block SAT summary does not replay")
    elif outcome == "NO_SINGLE_BLOCK_WITNESS":
        if (
            not all_unsat
            or evidence.get("witness") is not None
            or evidence.get("distance_upper_bound") is not None
            or evidence.get("single_block_minimum_weight_lower_bound")
            != max_weight + 1
        ):
            failures.append("single-block no-witness summary is inconsistent")
    elif (
        sat_witnesses
        or all_unsat
        or evidence.get("witness") is not None
        or evidence.get("distance_upper_bound") is not None
        or evidence.get("single_block_minimum_weight_lower_bound") is not None
    ):
        failures.append("single-block UNKNOWN summary is inconsistent")
    return failures


__all__ = [
    "TWO_BLOCK_SPARSE_KERNEL_KIND",
    "TWO_BLOCK_SPARSE_KERNEL_METHOD",
    "TWO_BLOCK_SPARSE_KERNEL_OUTCOMES",
    "TWO_BLOCK_SPARSE_KERNEL_SCHEMA_VERSION",
    "evaluate_two_block_sparse_kernel_oracle",
    "verify_two_block_sparse_kernel_oracle",
]
