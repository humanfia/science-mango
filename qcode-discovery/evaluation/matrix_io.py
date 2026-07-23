"""Canonical, self-contained binary matrix encoding for code certificates."""

from __future__ import annotations

from typing import Any

import numpy as np
from qldpc.codes import CSSCode, QuditCode

from evaluation.certificate import pack_vector, unpack_vector
from evaluation.final_gate import _rank_f2


def parse_binary_matrix(value: Any, *, name: str) -> np.ndarray:
    """Parse a matrix from rows, bit strings, or the packed certificate form."""
    if isinstance(value, dict):
        rows = int(value.get("rows", -1))
        cols = int(value.get("cols", -1))
        packed = value.get("data")
        if rows < 0 or cols <= 0 or not isinstance(packed, list) or len(packed) != rows:
            raise ValueError(f"{name}: malformed packed matrix")
        matrix = np.vstack([unpack_vector(row) for row in packed]) if rows else np.zeros((0, cols), dtype=np.uint8)
        if matrix.shape != (rows, cols):
            raise ValueError(f"{name}: packed dimensions do not match")
        return matrix
    if isinstance(value, list) and value and all(isinstance(row, str) for row in value):
        widths = {len(row) for row in value}
        if len(widths) != 1 or any(set(row) - {"0", "1"} for row in value):
            raise ValueError(f"{name}: bit-string rows must be rectangular and binary")
        return np.asarray([[int(bit) for bit in row] for row in value], dtype=np.uint8)
    matrix = np.asarray(value)
    if matrix.ndim != 2 or matrix.shape[1] == 0:
        raise ValueError(f"{name}: expected a non-empty-width two-dimensional matrix")
    if not np.all((matrix == 0) | (matrix == 1)):
        raise ValueError(f"{name}: entries must be binary")
    return matrix.astype(np.uint8)


def pack_matrix(matrix: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(matrix, dtype=np.uint8) & 1
    if binary.ndim != 2:
        raise ValueError("matrix must be two-dimensional")
    return {
        "rows": int(binary.shape[0]),
        "cols": int(binary.shape[1]),
        "data": [pack_vector(row) for row in binary],
    }


def build_css_from_matrices(hx_value: Any, hz_value: Any) -> tuple[CSSCode, np.ndarray, np.ndarray]:
    hx = parse_binary_matrix(hx_value, name="H_X")
    hz = parse_binary_matrix(hz_value, name="H_Z")
    if hx.shape[1] != hz.shape[1]:
        raise ValueError("H_X and H_Z widths differ")
    if np.any((hx @ hz.T) & 1):
        raise ValueError("H_X H_Z^T is nonzero: CSS checks do not commute")
    return CSSCode(hx, hz, field=2), hx, hz


def build_noncss_from_matrix(stabilizer_value: Any) -> tuple[QuditCode, np.ndarray]:
    stabilizer = parse_binary_matrix(stabilizer_value, name="symplectic_stabilizer")
    if stabilizer.shape[1] % 2:
        raise ValueError("symplectic stabilizer width must be 2n")
    n = stabilizer.shape[1] // 2
    x_part, z_part = stabilizer[:, :n], stabilizer[:, n:]
    if np.any((x_part @ z_part.T + z_part @ x_part.T) & 1):
        raise ValueError("symplectic stabilizer generators do not commute")
    return QuditCode(stabilizer, field=2), stabilizer


def css_parameters(hx: np.ndarray, hz: np.ndarray) -> tuple[int, int]:
    n = int(hx.shape[1])
    return n, n - _rank_f2(hx) - _rank_f2(hz)


def noncss_parameters(stabilizer: np.ndarray) -> tuple[int, int]:
    n = int(stabilizer.shape[1] // 2)
    return n, n - _rank_f2(stabilizer)
