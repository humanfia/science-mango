"""Replayable X/Z-sector isometry for CSS bivariate-bicycle codes.

For a BB code on ``Z_ell x Z_m`` the CSS checks have the form

``H_X = [A | B]`` and ``H_Z = [B^T | A^T]``.

Let ``J`` invert the group coordinate and let ``Q`` apply ``J`` while
swapping the two qubit blocks.  Then ``Q`` is an involutive coordinate
permutation and maps the row space of ``H_X`` onto the row space of ``H_Z``
(and conversely).  It therefore maps X and Z logical sectors bijectively
while preserving Hamming weight.  A complete distance proof may audit one
sector only when this module has replayed that matrix identity.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any

import numpy as np


BB_XZ_ISOMETRY_METHOD = "bb-xz-inversion-block-swap-rowspace-v1"
BB_XZ_ISOMETRY_SCHEMA_VERSION = 1


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _matrix_sha256(matrix: np.ndarray) -> str:
    value = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(json.dumps(list(value.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(value.tobytes(order="C"))
    return digest.hexdigest()


def _rank_f2(matrix: np.ndarray) -> int:
    value = np.asarray(matrix, dtype=np.uint8).copy() & 1
    if value.ndim != 2:
        raise ValueError("binary rank input must be a matrix")
    rows, columns = value.shape
    rank = 0
    for column in range(columns):
        pivots = np.flatnonzero(value[rank:, column])
        if not len(pivots):
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            value[[rank, pivot]] = value[[pivot, rank]]
        other = np.flatnonzero(value[:, column])
        other = other[other != rank]
        if len(other):
            value[other] ^= value[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def bb_xz_inversion_block_swap_permutation(ell: int, m: int) -> np.ndarray:
    """Return the BB qubit permutation ``Q`` in NumPy column-index form."""

    ell_value = int(ell)
    m_value = int(m)
    if ell_value <= 0 or m_value <= 0:
        raise ValueError("BB lattice dimensions must be positive")
    block_size = ell_value * m_value
    grid = np.arange(block_size, dtype=np.int64).reshape(ell_value, m_value)
    inversion = grid[
        np.mod(-np.arange(ell_value), ell_value)[:, None],
        np.mod(-np.arange(m_value), m_value)[None, :],
    ].ravel()
    return np.concatenate((block_size + inversion, inversion))


def verify_bb_xz_sector_isometry(
    hx: np.ndarray,
    hz: np.ndarray,
    *,
    ell: int,
    m: int,
) -> dict[str, Any]:
    """Rebuild and verify the weight-preserving BB X/Z-sector isometry.

    The report contains only hashes and replayable geometry.  Consumers must
    call this function again on reconstructed matrices instead of trusting the
    stored ``verified`` flag.
    """

    matrix_x = np.asarray(hx, dtype=np.uint8) & 1
    matrix_z = np.asarray(hz, dtype=np.uint8) & 1
    ell_value = int(ell)
    m_value = int(m)
    permutation = bb_xz_inversion_block_swap_permutation(ell_value, m_value)
    n = int(permutation.size)
    shapes_valid = bool(
        matrix_x.ndim == 2
        and matrix_z.ndim == 2
        and matrix_x.shape[1:] == (n,)
        and matrix_z.shape[1:] == (n,)
    )
    bijective = bool(
        len(np.unique(permutation)) == n
        and int(permutation.min(initial=0)) == 0
        and int(permutation.max(initial=-1)) == n - 1
    )
    involutive = bool(
        bijective
        and np.array_equal(permutation[permutation], np.arange(n))
    )

    hx_rank = hz_rank = hx_to_hz_rank = hz_to_hx_rank = -1
    hx_to_hz = hz_to_hx = css_commutation = False
    mapped_x_hash = mapped_z_hash = None
    if shapes_valid and bijective:
        mapped_x = matrix_x[:, permutation]
        mapped_z = matrix_z[:, permutation]
        hx_rank = _rank_f2(matrix_x)
        hz_rank = _rank_f2(matrix_z)
        hx_to_hz_rank = _rank_f2(np.vstack((mapped_x, matrix_z)))
        hz_to_hx_rank = _rank_f2(np.vstack((mapped_z, matrix_x)))
        hx_to_hz = bool(hx_to_hz_rank == hx_rank == hz_rank)
        hz_to_hx = bool(hz_to_hx_rank == hx_rank == hz_rank)
        css_commutation = not bool(np.any((matrix_x @ matrix_z.T) & 1))
        mapped_x_hash = _matrix_sha256(mapped_x)
        mapped_z_hash = _matrix_sha256(mapped_z)

    report: dict[str, Any] = {
        "schema_version": BB_XZ_ISOMETRY_SCHEMA_VERSION,
        "method": BB_XZ_ISOMETRY_METHOD,
        "verified": bool(
            shapes_valid
            and bijective
            and involutive
            and css_commutation
            and hx_to_hz
            and hz_to_hx
        ),
        "shape": [ell_value, m_value],
        "block_size": ell_value * m_value,
        "n": n,
        "matrix_shape_x": list(matrix_x.shape),
        "matrix_shape_z": list(matrix_z.shape),
        "matrix_sha256_x": _matrix_sha256(matrix_x),
        "matrix_sha256_z": _matrix_sha256(matrix_z),
        "mapped_matrix_sha256_x": mapped_x_hash,
        "mapped_matrix_sha256_z": mapped_z_hash,
        "permutation_sha256": hashlib.sha256(
            np.asarray(permutation, dtype="<u4").tobytes()
        ).hexdigest(),
        "permutation_bijective": bijective,
        "permutation_involutive": involutive,
        "css_commutation": css_commutation,
        "rank_x": hx_rank,
        "rank_z": hz_rank,
        "mapped_x_plus_z_rank": hx_to_hz_rank,
        "mapped_z_plus_x_rank": hz_to_hx_rank,
        "x_rowspace_maps_to_z": hx_to_hz,
        "z_rowspace_maps_to_x": hz_to_hx,
        "weight_preserving": bijective,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
    }
    report["report_sha256"] = _canonical_sha256(report)
    return report


__all__ = [
    "BB_XZ_ISOMETRY_METHOD",
    "BB_XZ_ISOMETRY_SCHEMA_VERSION",
    "bb_xz_inversion_block_swap_permutation",
    "verify_bb_xz_sector_isometry",
]
