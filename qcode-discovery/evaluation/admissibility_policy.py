"""Versioned hardware-admissibility policies for qLDPC candidates.

The scalar target policy answers only the mathematical question
``k*d**2/n >= threshold``.  Physical check locality is an orthogonal contract:
each published CSS stabilizer is measured as one original row of ``H_X`` or
``H_Z``, without row reduction, and may touch at most six data qubits.

Reports are always recomputed from binary matrices.  Candidate-supplied
weight fields are never authoritative.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping

import numpy as np


CSS_W6_ADMISSIBILITY_MODE = (
    "css-stabilizer-check-row-weight-at-most-6-v1"
)
CSS_W6_MAX_CHECK_ROW_WEIGHT = 6
CSS_EXISTING_MAX_COMBINED_QUBIT_DEGREE = 6


def _canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    payload = dict(value) if isinstance(value, Mapping) else value
    if omit is not None and isinstance(payload, dict):
        payload.pop(omit, None)
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def css_w6_admissibility_binding() -> dict[str, Any]:
    """Return the canonical, self-hashed CSS check-locality contract."""

    binding: dict[str, Any] = {
        "schema_version": 1,
        "mode": CSS_W6_ADMISSIBILITY_MODE,
        "code_type": "css",
        "matrix_scope": ["H_X", "H_Z"],
        "metric": "binary-hamming-support-per-row",
        "maximum": CSS_W6_MAX_CHECK_ROW_WEIGHT,
        "matrix_authority": "fresh-rebuild-from-construction",
        "reported_weight_fields_authoritative": False,
        "row_reduction_allowed": False,
    }
    binding["binding_sha256"] = _canonical_sha256(binding)
    return binding


def validate_css_w6_admissibility_binding(value: Any) -> dict[str, Any]:
    """Validate an exact policy descriptor; aliases fail closed."""

    expected = css_w6_admissibility_binding()
    if not isinstance(value, Mapping) or dict(value) != expected:
        raise ValueError("CSS weight-6 admissibility binding is missing or stale")
    return expected


def _binary_matrix(value: Any, label: str) -> np.ndarray:
    raw = np.asarray(value)
    if raw.ndim != 2:
        raise ValueError(f"{label} must be a two-dimensional binary matrix")
    if np.any((raw != 0) & (raw != 1)):
        raise ValueError(f"{label} contains non-binary entries")
    return np.ascontiguousarray(raw, dtype=np.uint8)


def _matrix_sha256(matrix: np.ndarray) -> str:
    binary = np.ascontiguousarray(matrix, dtype=np.uint8)
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def evaluate_css_w6_admissibility(hx: Any, hz: Any) -> dict[str, Any]:
    """Recompute check weights and the existing degree-six LDPC gate."""

    binary_hx = _binary_matrix(hx, "H_X")
    binary_hz = _binary_matrix(hz, "H_Z")
    if binary_hx.shape[1] != binary_hz.shape[1]:
        raise ValueError("H_X and H_Z must act on the same number of qubits")
    max_x = int(binary_hx.sum(axis=1).max(initial=0))
    max_z = int(binary_hz.sum(axis=1).max(initial=0))
    max_check = max(max_x, max_z)
    stacked = np.vstack((binary_hx, binary_hz))
    max_degree = int(stacked.sum(axis=0).max(initial=0))
    binding = css_w6_admissibility_binding()
    report: dict[str, Any] = {
        "schema_version": 1,
        "policy_binding_sha256": binding["binding_sha256"],
        "matrix_shape": {
            "H_X": list(binary_hx.shape),
            "H_Z": list(binary_hz.shape),
        },
        "matrix_sha256": {
            "H_X": _matrix_sha256(binary_hx),
            "H_Z": _matrix_sha256(binary_hz),
        },
        "max_x_check_weight": max_x,
        "max_z_check_weight": max_z,
        "max_check_row_weight": max_check,
        "all_x_rows_within_limit": max_x <= CSS_W6_MAX_CHECK_ROW_WEIGHT,
        "all_z_rows_within_limit": max_z <= CSS_W6_MAX_CHECK_ROW_WEIGHT,
        # This is the repository's pre-existing stronger LDPC safeguard.  It
        # is reported separately and is not conflated with the user's row-
        # weight policy above.
        "additional_existing_gate": {
            "mode": "combined-qubit-check-degree-at-most-6-v1",
            "maximum": CSS_EXISTING_MAX_COMBINED_QUBIT_DEGREE,
            "observed": max_degree,
            "passed": (
                max_degree <= CSS_EXISTING_MAX_COMBINED_QUBIT_DEGREE
            ),
        },
    }
    report["passed"] = bool(
        report["all_x_rows_within_limit"]
        and report["all_z_rows_within_limit"]
        and report["additional_existing_gate"]["passed"]
    )
    report["report_sha256"] = _canonical_sha256(report)
    return report


def require_css_w6_admissibility(hx: Any, hz: Any) -> dict[str, Any]:
    """Return a fresh report or reject before any distance solver starts."""

    report = evaluate_css_w6_admissibility(hx, hz)
    if not report["all_x_rows_within_limit"] or not report[
        "all_z_rows_within_limit"
    ]:
        raise ValueError(
            "CSS stabilizer check row weight exceeds the hardware limit 6 "
            f"(X={report['max_x_check_weight']}, "
            f"Z={report['max_z_check_weight']})"
        )
    degree = report["additional_existing_gate"]
    if degree["passed"] is not True:
        raise ValueError(
            "CSS combined qubit check degree exceeds the existing LDPC "
            f"limit 6 (observed={degree['observed']})"
        )
    return report


__all__ = [
    "CSS_EXISTING_MAX_COMBINED_QUBIT_DEGREE",
    "CSS_W6_ADMISSIBILITY_MODE",
    "CSS_W6_MAX_CHECK_ROW_WEIGHT",
    "css_w6_admissibility_binding",
    "evaluate_css_w6_admissibility",
    "require_css_w6_admissibility",
    "validate_css_w6_admissibility_binding",
]
