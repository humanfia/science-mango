"""Replayable completeness checks for CSS logical detector matrices."""

from __future__ import annotations

import hashlib
import json
from typing import Any

import numpy as np


CSS_LOGICAL_DETECTOR_METHOD = "css-logical-detector-dimension-replay-v1"


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _rank_f2(matrix: np.ndarray) -> int:
    """Return matrix rank over GF(2) without numeric-field ambiguity."""

    value = np.asarray(matrix, dtype=np.uint8).copy() & 1
    if value.ndim != 2:
        raise ValueError("GF(2) rank input must be a matrix")
    rows, columns = value.shape
    rank = 0
    for column in range(columns):
        pivots = np.flatnonzero(value[rank:, column])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            value[[rank, pivot]] = value[[pivot, rank]]
        for row in range(rows):
            if row != rank and value[row, column]:
                value[row] ^= value[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def verify_css_logical_detectors(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> dict[str, Any]:
    """Prove nonzero detector syndrome means a nontrivial CSS operator.

    Besides commutation and canonical X/Z logical duality, the dimension
    replay checks that the kernel of each detector inside the commuting space
    is exactly the opposite stabilizer row space. This is the prerequisite
    that lets a complete low-weight detector query imply a distance bound.
    """

    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in (hx, hz, lx, lz)
    )
    matrices = (hx, hz, lx, lz)
    valid_shapes = bool(
        all(value.ndim == 2 for value in matrices)
        and hx.shape[1] > 0
        and all(value.shape[1] == hx.shape[1] for value in matrices)
    )
    if not valid_shapes:
        report = {
            "method": CSS_LOGICAL_DETECTOR_METHOD,
            "verified": False,
            "n": None,
            "k": None,
            "css_commutation": False,
            "logical_duality": False,
            "sectors": {},
        }
        report["report_sha256"] = _canonical_sha256(report)
        return report

    n = int(hx.shape[1])
    k = n - _rank_f2(hx) - _rank_f2(hz)
    sectors: dict[str, dict[str, Any]] = {}
    specifications = {
        "X": (hz, lz, hx),
        "Z": (hx, lx, hz),
    }
    for sector, (checks, logicals, trivial) in specifications.items():
        stacked_rank = _rank_f2(np.vstack((checks, logicals)))
        trivial_rank = _rank_f2(trivial)
        inclusion = bool(
            not np.any((checks @ trivial.T) & 1)
            and not np.any((logicals @ trivial.T) & 1)
        )
        kernel_dimension = n - stacked_rank
        sectors[sector] = {
            "verified": bool(
                logicals.shape == (k, n)
                and inclusion
                and kernel_dimension == trivial_rank
            ),
            "logical_count": int(logicals.shape[0]),
            "trivial_rank": trivial_rank,
            "detector_kernel_dimension": kernel_dimension,
            "trivial_space_in_detector_kernel": inclusion,
        }
    css_commutation = bool(not np.any((hx @ hz.T) & 1))
    duality = bool(
        lx.shape == lz.shape == (k, n)
        and np.array_equal((lx @ lz.T) & 1, np.eye(k, dtype=np.uint8))
    )
    report = {
        "method": CSS_LOGICAL_DETECTOR_METHOD,
        "verified": bool(
            k > 0
            and css_commutation
            and duality
            and all(item["verified"] for item in sectors.values())
        ),
        "n": n,
        "k": k,
        "css_commutation": css_commutation,
        "logical_duality": duality,
        "sectors": sectors,
    }
    report["report_sha256"] = _canonical_sha256(report)
    return report


__all__ = ["CSS_LOGICAL_DETECTOR_METHOD", "verify_css_logical_detectors"]
