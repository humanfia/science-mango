"""Exact X/Z-sector isometry for the paper ``[[400,16]]`` Dic5 code.

The construction is the central-product quotient

``Q = (Dic5 x Dic5) / <r1^5 r2^5>``

from arXiv:2608.08996v1.  This module independently rebuilds its two CSS
matrices and an algebraically defined coordinate permutation.  The
permutation is not an involution (it has order ten), but it swaps the X and Z
normalizer quotients bijectively and preserves Hamming weight.  Therefore one
terminal lower-distance decision for either sector covers both sectors.

Permutation convention
----------------------

All permutations below map an old index to its new index.  For a binary row
vector ``word``, its push-forward is the vector ``image`` satisfying
``image[qubit_old_to_new] = word``.  The exact matrix identities are

``H_Z[x_row_to_z_row, qubit_old_to_new] == H_X`` and
``H_X[z_row_to_x_row, qubit_old_to_new] == H_Z``.

They prove, without sampling or a solver, that the push-forward maps
``ker(H_Z) / row(H_X)`` onto ``ker(H_X) / row(H_Z)`` and conversely.
"""

from __future__ import annotations

import hashlib
import json
from itertools import product
from typing import Any, Sequence

import numpy as np


PAPER400_DIC5_XZ_ISOMETRY_METHOD = (
    "paper400-dic5-algebraic-block-swap-quotient-isometry-v1"
)
PAPER400_DIC5_XZ_ISOMETRY_SCHEMA_VERSION = 1

EXPECTED_MATRIX_SHA256 = {
    "H_X": "80a86c5d5d68c52bca21cc67074dc0f6766e3cf1832959e9b78be35228cd97c2",
    "H_Z": "d2224a102f1b96e9215280f32fc550467f7ea92ecb3b9c8633fc5269b9e8a7f3",
}
EXPECTED_PERMUTATION_SHA256 = {
    "qubit_old_to_new": (
        "a24e4474da89f73d5896f3e06f8bca0782fcb92f292b3c9506d93cf69f28d80b"
    ),
    "x_row_to_z_row": (
        "71a47878f5ac8fb385b37a03baee45545879a6131383d8dc589a3dc842bca116"
    ),
    "z_row_to_x_row": (
        "3aa0f2cef964d98efa85c655545deee131c4402faa02ae6997d70be2ed96a11d"
    ),
}
EXPECTED_LOGICAL_MAP_SHA256 = {
    "X_to_Z": "33fea1d64df3e92bda41a421aa25647dc386698c59d8068887b273c25287681f",
    "Z_to_X": "c28b66e940bf31f876adf758a64ee0fde82d70d4d650401c434e1fee3434156a",
}

GroupElement = tuple[int, int, int, int]
IDENTITY: GroupElement = (0, 0, 0, 0)
DIAGONAL_CENTER: GroupElement = (5, 0, 5, 0)
R1: GroupElement = (1, 0, 0, 0)
S1: GroupElement = (0, 1, 0, 0)
R2: GroupElement = (0, 0, 1, 0)
S2: GroupElement = (0, 0, 0, 1)
RAW_GROUP = tuple(product(range(10), range(2), range(10), range(2)))


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _dic_mul(
    left: tuple[int, int],
    right: tuple[int, int],
) -> tuple[int, int]:
    a, b = left
    c, d = right
    return ((a + (-c if b else c) + (5 if b and d else 0)) % 10, b ^ d)


def _mul(left: GroupElement, right: GroupElement) -> GroupElement:
    return _dic_mul(left[:2], right[:2]) + _dic_mul(left[2:], right[2:])


def _power(value: GroupElement, exponent: int) -> GroupElement:
    result = IDENTITY
    for _ in range(int(exponent)):
        result = _mul(result, value)
    return result


def _canonical_coset(value: GroupElement) -> GroupElement:
    return min(value, _mul(value, DIAGONAL_CENTER))


QUOTIENT_REPS = tuple(sorted({_canonical_coset(value) for value in RAW_GROUP}))
QUOTIENT_INDEX = {value: index for index, value in enumerate(QUOTIENT_REPS)}


def _word(*values: GroupElement) -> GroupElement:
    result = IDENTITY
    for value in values:
        result = _mul(result, value)
    return _canonical_coset(result)


def _hom_image(
    generator_images: Sequence[GroupElement],
    value: GroupElement,
) -> GroupElement:
    """Evaluate a quotient-group homomorphism on the canonical normal word."""

    result = IDENTITY
    for image, exponent in zip(generator_images, value, strict=True):
        result = _word(result, _power(image, exponent))
    return result


def _construction_terms() -> tuple[tuple[GroupElement, ...], tuple[GroupElement, ...]]:
    a_terms = (
        _word(S1, R2, S2),
        _word(_power(R1, 9), _power(R2, 2), S2),
        _word(_power(R1, 2), S1, _power(R2, 3), S2),
    )
    b_terms = (
        _word(_power(R1, 8)),
        _word(_power(R1, 2), R2),
        _word(R2, S2),
    )
    return a_terms, b_terms


def _action_matrix(terms: Sequence[GroupElement], side: str) -> np.ndarray:
    matrix = np.zeros((200, 200), dtype=np.uint8)
    for row, value in enumerate(QUOTIENT_REPS):
        for term in terms:
            image = _canonical_coset(
                _mul(term, value) if side == "left" else _mul(value, term)
            )
            matrix[row, QUOTIENT_INDEX[image]] ^= 1
    return matrix


def _matrix_sha256(matrix: np.ndarray) -> str:
    binary = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def _permutation_sha256(permutation: Sequence[int]) -> str:
    return hashlib.sha256(
        np.asarray(permutation, dtype="<u4").tobytes()
    ).hexdigest()


def _rank_f2(matrix: np.ndarray) -> int:
    value = np.asarray(matrix, dtype=np.uint8).copy() & 1
    rank = 0
    for column in range(value.shape[1]):
        pivots = np.flatnonzero(value[rank:, column])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        value[[rank, pivot]] = value[[pivot, rank]]
        other = np.flatnonzero(value[:, column])
        other = other[other != rank]
        value[other] ^= value[rank]
        rank += 1
        if rank == value.shape[0]:
            break
    return rank


def build_paper400_dic5_matrices() -> tuple[np.ndarray, np.ndarray]:
    """Rebuild ``H_X=[L(A)|R(B)]`` and ``H_Z=[R(B)^T|L(A)^T]``."""

    if len(QUOTIENT_REPS) != 200:
        raise RuntimeError("Dic5 central-product quotient order changed")
    a_terms, b_terms = _construction_terms()
    a_left = _action_matrix(a_terms, "left")
    b_right = _action_matrix(b_terms, "right")
    hx = np.ascontiguousarray(np.hstack((a_left, b_right)), dtype=np.uint8)
    hz = np.ascontiguousarray(np.hstack((b_right.T, a_left.T)), dtype=np.uint8)
    return hx, hz


def _isometry_formula() -> dict[str, Any]:
    """Return the complete generator-image formula for the isometry."""

    phi4 = (
        R1,
        _word(_power(R1, 2), S1, _power(R2, 5)),
        R2,
        _word(_power(R2, 4), S2),
    )
    phi6 = (
        R1,
        _word(_power(R1, 2), S1, _power(R2, 5)),
        R2,
        _word(_power(R2, 6), S2),
    )
    formula: dict[str, Any] = {
        "schema_version": 1,
        "normal_form": "r1^a s1^b r2^c s2^d",
        "quotient_representative": "lexicographic min of {g,g(r1^5r2^5)}",
        "phi4_generator_images_R1_S1_R2_S2": [list(item) for item in phi4],
        "phi6_generator_images_R1_S1_R2_S2": [list(item) for item in phi6],
        "qubit_block0_to_block1": "g -> phi4(g)",
        "qubit_block1_to_block0": "g -> (3,0,5,0)*phi6(g)",
        "x_row_to_z_row": "g -> (3,0,6,0)*phi4(g)",
        "z_row_to_x_row": "g -> (0,0,9,0)*phi6(g)",
    }
    formula["formula_sha256"] = _canonical_sha256(formula)
    return formula


def paper400_dic5_xz_isometry_permutations(
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return old-to-new qubit, X-row-to-Z-row, and Z-row-to-X-row maps."""

    formula = _isometry_formula()
    phi4 = tuple(
        tuple(item)
        for item in formula["phi4_generator_images_R1_S1_R2_S2"]
    )
    phi6 = tuple(
        tuple(item)
        for item in formula["phi6_generator_images_R1_S1_R2_S2"]
    )
    qubits = np.empty(400, dtype=np.int64)
    x_rows = np.empty(200, dtype=np.int64)
    z_rows = np.empty(200, dtype=np.int64)
    for index, value in enumerate(QUOTIENT_REPS):
        image4 = _hom_image(phi4, value)
        image6 = _hom_image(phi6, value)
        qubits[index] = 200 + QUOTIENT_INDEX[image4]
        qubits[200 + index] = QUOTIENT_INDEX[_word((3, 0, 5, 0), image6)]
        x_rows[index] = QUOTIENT_INDEX[_word((3, 0, 6, 0), image4)]
        z_rows[index] = QUOTIENT_INDEX[_word((0, 0, 9, 0), image6)]
    return qubits, x_rows, z_rows


def push_forward_rows(rows: np.ndarray, old_to_new: Sequence[int]) -> np.ndarray:
    """Push binary row vectors along an old-index-to-new-index permutation."""

    value = np.asarray(rows, dtype=np.uint8) & 1
    was_vector = value.ndim == 1
    if was_vector:
        value = value.reshape(1, -1)
    permutation = np.asarray(old_to_new, dtype=np.int64)
    if value.ndim != 2 or value.shape[1] != permutation.size:
        raise ValueError("row width and permutation size differ")
    if not np.array_equal(np.sort(permutation), np.arange(permutation.size)):
        raise ValueError("old_to_new is not a permutation")
    result = np.zeros_like(value)
    result[:, permutation] = value
    return result[0] if was_vector else result


def _permutation_order_and_cycles(permutation: np.ndarray) -> tuple[int, dict[str, int]]:
    seen: set[int] = set()
    lengths: list[int] = []
    for start in range(permutation.size):
        if start in seen:
            continue
        current = start
        length = 0
        while current not in seen:
            seen.add(current)
            current = int(permutation[current])
            length += 1
        lengths.append(length)
    order = 1
    distribution: dict[str, int] = {}
    for length in lengths:
        order = int(np.lcm(order, length))
        key = str(length)
        distribution[key] = distribution.get(key, 0) + 1
    return order, distribution


def _logical_map_report(
    lx: np.ndarray,
    lz: np.ndarray,
    qubits: np.ndarray,
) -> dict[str, Any]:
    x_basis = np.asarray(lx, dtype=np.uint8) & 1
    z_basis = np.asarray(lz, dtype=np.uint8) & 1
    if x_basis.shape != (16, 400) or z_basis.shape != (16, 400):
        raise ValueError("the paper code logical bases must both have shape (16,400)")
    x_to_z = np.zeros((16, 16), dtype=np.uint8)
    z_to_x = np.zeros((16, 16), dtype=np.uint8)
    pushed_x = push_forward_rows(x_basis, qubits)
    pushed_z = push_forward_rows(z_basis, qubits)
    for index in range(16):
        x_to_z[:, index] = (x_basis @ pushed_x[index]) & 1
        z_to_x[:, index] = (z_basis @ pushed_z[index]) & 1
    hashes = {
        "X_to_Z": _matrix_sha256(x_to_z),
        "Z_to_X": _matrix_sha256(z_to_x),
    }
    report: dict[str, Any] = {
        "schema_version": 1,
        "basis_convention": (
            "L_X@L_Z^T=I; X representatives=L_X/detector=L_Z; "
            "Z representatives=L_Z/detector=L_X"
        ),
        "logical_duality": bool(
            np.array_equal(
                (x_basis @ z_basis.T) & 1,
                np.eye(16, dtype=np.uint8),
            )
        ),
        "X_to_Z_rank": _rank_f2(x_to_z),
        "Z_to_X_rank": _rank_f2(z_to_x),
        "logical_map_sha256": hashes,
        "expected_logical_map_sha256": EXPECTED_LOGICAL_MAP_SHA256,
        "hashes_match": hashes == EXPECTED_LOGICAL_MAP_SHA256,
        "dot_product_compatibility": bool(
            np.array_equal(
                (x_to_z.T @ z_to_x) & 1,
                np.eye(16, dtype=np.uint8),
            )
        ),
    }
    report["verified"] = bool(
        report["logical_duality"]
        and report["X_to_Z_rank"] == report["Z_to_X_rank"] == 16
        and report["hashes_match"]
        and report["dot_product_compatibility"]
    )
    report["report_sha256"] = _canonical_sha256(report)
    return report


def verify_paper400_dic5_xz_isometry(
    hx: np.ndarray | None = None,
    hz: np.ndarray | None = None,
    *,
    lx: np.ndarray | None = None,
    lz: np.ndarray | None = None,
) -> dict[str, Any]:
    """Rebuild and replay the complete quotient isometry certificate."""

    rebuilt_x, rebuilt_z = build_paper400_dic5_matrices()
    matrix_x = rebuilt_x if hx is None else np.asarray(hx, dtype=np.uint8) & 1
    matrix_z = rebuilt_z if hz is None else np.asarray(hz, dtype=np.uint8) & 1
    qubits, x_rows, z_rows = paper400_dic5_xz_isometry_permutations()
    formula = _isometry_formula()

    shape_valid = matrix_x.shape == matrix_z.shape == (200, 400)
    qubit_bijective = np.array_equal(np.sort(qubits), np.arange(400))
    x_rows_bijective = np.array_equal(np.sort(x_rows), np.arange(200))
    z_rows_bijective = np.array_equal(np.sort(z_rows), np.arange(200))
    hashes = {
        "qubit_old_to_new": _permutation_sha256(qubits),
        "x_row_to_z_row": _permutation_sha256(x_rows),
        "z_row_to_x_row": _permutation_sha256(z_rows),
    }
    mapping_record: dict[str, Any] = {
        "schema_version": 1,
        "convention": "old index -> new index",
        "qubit_old_to_new": qubits.astype(int).tolist(),
        "x_row_to_z_row": x_rows.astype(int).tolist(),
        "z_row_to_x_row": z_rows.astype(int).tolist(),
    }
    mapping_sha256 = _canonical_sha256(mapping_record)
    order, cycle_distribution = _permutation_order_and_cycles(qubits)

    matrix_hashes = {
        "H_X": _matrix_sha256(matrix_x),
        "H_Z": _matrix_sha256(matrix_z),
    }
    exact_x_to_z = exact_z_to_x = css_commutation = False
    pushed_x_rows_exact = pushed_z_rows_exact = False
    rank_x = rank_z = -1
    if shape_valid:
        exact_x_to_z = bool(
            np.array_equal(matrix_z[np.ix_(x_rows, qubits)], matrix_x)
        )
        exact_z_to_x = bool(
            np.array_equal(matrix_x[np.ix_(z_rows, qubits)], matrix_z)
        )
        pushed_x_rows_exact = bool(
            np.array_equal(push_forward_rows(matrix_x, qubits), matrix_z[x_rows])
        )
        pushed_z_rows_exact = bool(
            np.array_equal(push_forward_rows(matrix_z, qubits), matrix_x[z_rows])
        )
        css_commutation = not bool(np.any((matrix_x @ matrix_z.T) & 1))
        rank_x = _rank_f2(matrix_x)
        rank_z = _rank_f2(matrix_z)

    logical_supplied = lx is not None or lz is not None
    logical_report = None
    if logical_supplied:
        if lx is None or lz is None:
            raise ValueError("lx and lz must be supplied together")
        logical_report = _logical_map_report(lx, lz, qubits)

    structural_verified = bool(
        shape_valid
        and qubit_bijective
        and x_rows_bijective
        and z_rows_bijective
        and hashes == EXPECTED_PERMUTATION_SHA256
        and matrix_hashes == EXPECTED_MATRIX_SHA256
        and exact_x_to_z
        and exact_z_to_x
        and pushed_x_rows_exact
        and pushed_z_rows_exact
        and css_commutation
        and rank_x == rank_z == 192
    )
    report: dict[str, Any] = {
        "schema_version": PAPER400_DIC5_XZ_ISOMETRY_SCHEMA_VERSION,
        "method": PAPER400_DIC5_XZ_ISOMETRY_METHOD,
        "verified": bool(
            structural_verified
            and (logical_report is None or logical_report["verified"])
        ),
        "source": {
            "authority": "arXiv:2608.08996v1 supplementary construction",
            "url": "https://arxiv.org/html/2608.08996v1",
        },
        "formula": formula,
        "complete_mapping_sha256": mapping_sha256,
        "permutation_sha256": hashes,
        "expected_permutation_sha256": EXPECTED_PERMUTATION_SHA256,
        "permutation_hashes_match": hashes == EXPECTED_PERMUTATION_SHA256,
        "qubit_permutation_bijective": qubit_bijective,
        "x_row_permutation_bijective": x_rows_bijective,
        "z_row_permutation_bijective": z_rows_bijective,
        "qubit_permutation_order": order,
        "qubit_cycle_length_distribution": cycle_distribution,
        "qubit_permutation_involutive": order <= 2,
        "matrix_sha256": matrix_hashes,
        "expected_matrix_sha256": EXPECTED_MATRIX_SHA256,
        "matrix_hashes_match": matrix_hashes == EXPECTED_MATRIX_SHA256,
        "rank_Hx": rank_x,
        "rank_Hz": rank_z,
        "k": 400 - rank_x - rank_z if rank_x >= 0 and rank_z >= 0 else None,
        "css_commutation": css_commutation,
        "exact_identity_Hz_xrows_qubits_equals_Hx": exact_x_to_z,
        "exact_identity_Hx_zrows_qubits_equals_Hz": exact_z_to_x,
        "pushed_Hx_rows_equal_permuted_Hz_rows": pushed_x_rows_exact,
        "pushed_Hz_rows_equal_permuted_Hx_rows": pushed_z_rows_exact,
        "weight_preserving": qubit_bijective,
        "X_normalizer_to_Z_normalizer_bijection": structural_verified,
        "Z_normalizer_to_X_normalizer_bijection": structural_verified,
        "X_stabilizer_to_Z_stabilizer_bijection": structural_verified,
        "Z_stabilizer_to_X_stabilizer_bijection": structural_verified,
        "logical_nontriviality_preserved_both_directions": structural_verified,
        "distance_consequence": "d_X=d_Z",
        "canonical_sector": "Z",
        "covered_sectors": ["X", "Z"],
        "logical_basis_replay": logical_report,
    }
    report["report_sha256"] = _canonical_sha256(report)
    return report


__all__ = [
    "EXPECTED_LOGICAL_MAP_SHA256",
    "EXPECTED_MATRIX_SHA256",
    "EXPECTED_PERMUTATION_SHA256",
    "PAPER400_DIC5_XZ_ISOMETRY_METHOD",
    "PAPER400_DIC5_XZ_ISOMETRY_SCHEMA_VERSION",
    "build_paper400_dic5_matrices",
    "paper400_dic5_xz_isometry_permutations",
    "push_forward_rows",
    "verify_paper400_dic5_xz_isometry",
]
