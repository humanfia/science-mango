"""Typed builder for frozen coset/regular two-block CSS constructions.

For a catalog action with mutually commuting left and right permutation
representations, sparse supports define

``A = sum(left support)``, ``B = sum(right support)``,
``H_X = [A | B]``, and ``H_Z = [B.T | A.T]``.

Only action element identifiers are candidate-controlled.  The permutations
themselves are immutable, source-bound catalog data and never come from an
evolved program or a runtime GAP process.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from hashlib import sha256
from typing import Any

import numpy as np
from qldpc import codes

from evaluation.coset_action_catalog import (
    action_catalog_sha256,
    get_action,
    inverse_permutation,
    list_action_descriptors,
    permutation_for_element,
    resolve_element_ids,
)


CONSTRUCTION_KIND = "coset-two-block-v1"
MAX_TOTAL_SUPPORT = 6
ACTION_CATALOG_SHA256 = action_catalog_sha256()


def _support(value: Any, *, name: str) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise ValueError(f"{name} must be a nonempty sequence of element IDs")
    result = tuple(value)
    if not result:
        raise ValueError(f"{name} must not be empty")
    if any(not isinstance(item, str) or not item for item in result):
        raise ValueError(f"{name} must contain only nonempty strings")
    return result


def normalize_coset_two_block_construction(value: Mapping[str, Any]) -> dict[str, Any]:
    """Validate and canonicalize a source-bound two-block construction."""

    if not isinstance(value, Mapping):
        raise ValueError("coset two-block construction must be a mapping")
    required = {
        "kind",
        "action_id",
        "action_catalog_sha256",
        "left_support",
        "right_support",
    }
    actual = set(value)
    if actual != required:
        raise ValueError(
            "coset two-block construction fields do not match schema; "
            f"missing={sorted(required - actual)}, "
            f"unknown={sorted(actual - required)}"
        )
    if value["kind"] != CONSTRUCTION_KIND:
        raise ValueError(f"unsupported construction kind {value['kind']!r}")
    action_id = value["action_id"]
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("action_id must be a nonempty string")
    get_action(action_id)  # fail closed before inspecting candidate supports
    supplied_sha = value["action_catalog_sha256"]
    if supplied_sha != ACTION_CATALOG_SHA256:
        raise ValueError(
            "construction action_catalog_sha256 does not match the frozen catalog"
        )
    left_input = _support(value["left_support"], name="left_support")
    right_input = _support(value["right_support"], name="right_support")
    if len(left_input) + len(right_input) > MAX_TOTAL_SUPPORT:
        raise ValueError(
            f"total support exceeds the maximum {MAX_TOTAL_SUPPORT}"
        )
    left = resolve_element_ids(action_id, "left", left_input)
    right = resolve_element_ids(action_id, "right", right_input)
    if len(set(left)) != len(left):
        raise ValueError("left_support resolves to duplicate action elements")
    if len(set(right)) != len(right):
        raise ValueError("right_support resolves to duplicate action elements")
    # A/B are sums over F_2, so support ordering has no semantics.  Stable IDs
    # are zero-padded in catalog order and lexical sorting is canonical.
    return {
        "kind": CONSTRUCTION_KIND,
        "action_id": action_id,
        "action_catalog_sha256": ACTION_CATALOG_SHA256,
        "left_support": sorted(left),
        "right_support": sorted(right),
    }


# Compatibility names used by the Stage-1 adapter while it is kept isolated
# from the generic construction dispatcher.
normalize_construction = normalize_coset_two_block_construction
normalize_coset_construction = normalize_coset_two_block_construction


def _permutation_matrix(permutation: tuple[int, ...]) -> np.ndarray:
    degree = len(permutation)
    result = np.zeros((degree, degree), dtype=np.uint8)
    result[np.arange(degree, dtype=np.int64), np.asarray(permutation)] = 1
    return result


def _sum_permutation_matrices(
    action_id: str, side: str, support: Sequence[str], degree: int
) -> np.ndarray:
    result = np.zeros((degree, degree), dtype=np.uint8)
    rows = np.arange(degree, dtype=np.int64)
    for element_id in support:
        permutation = permutation_for_element(action_id, side, element_id)
        result[rows, np.asarray(permutation, dtype=np.int64)] ^= 1
    return result


def matrix_sha256(matrix: np.ndarray) -> str:
    """Hash a binary matrix using ``evaluation.final_gate``'s convention."""

    binary = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    shape = f"{binary.shape[0]}x{binary.shape[1]}:".encode("ascii")
    packed = np.packbits(binary, axis=None, bitorder="little").tobytes()
    return sha256(shape + packed).hexdigest()


def _gf2_product(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return (
        np.asarray(left, dtype=np.uint16)
        @ np.asarray(right, dtype=np.uint16)
    ).astype(np.uint8) & 1


def _build_normalized(construction: Mapping[str, Any]) -> codes.CSSCode:
    action_id = str(construction["action_id"])
    action = get_action(action_id)
    left = tuple(construction["left_support"])
    right = tuple(construction["right_support"])
    matrix_a = _sum_permutation_matrices(
        action_id, "left", left, action.block_size
    )
    matrix_b = _sum_permutation_matrices(
        action_id, "right", right, action.block_size
    )
    if not np.array_equal(
        _gf2_product(matrix_a, matrix_b),
        _gf2_product(matrix_b, matrix_a),
    ):
        raise RuntimeError("selected left/right sums do not commute")
    matrix_x = np.ascontiguousarray(np.hstack((matrix_a, matrix_b)))
    matrix_z = np.ascontiguousarray(np.hstack((matrix_b.T, matrix_a.T)))
    expected_shape = (action.block_size, 2 * action.block_size)
    if matrix_x.shape != expected_shape or matrix_z.shape != expected_shape:
        raise RuntimeError("two-block builder produced an unexpected matrix shape")
    css_product = _gf2_product(matrix_x, matrix_z.T)
    if np.any(css_product):
        raise RuntimeError("two-block builder produced noncommuting CSS checks")

    code = codes.CSSCode(
        matrix_x,
        matrix_z,
        field=2,
        promise_equal_distance_xz=False,
    )
    # Reconstruction metadata only: published distance is deliberately absent.
    # The exact-distance gate must prove distance independently.
    code.construction = dict(construction)
    code.action_id = action_id
    code.action_catalog_sha256 = ACTION_CATALOG_SHA256
    code.matrix_a = matrix_a
    code.matrix_b = matrix_b
    code.matrix_sha256_x = matrix_sha256(matrix_x)
    code.matrix_sha256_z = matrix_sha256(matrix_z)
    x_qubit_degrees = matrix_x.sum(axis=0)
    z_qubit_degrees = matrix_z.sum(axis=0)
    code.coset_two_block_validation = {
        "schema_version": 1,
        "block_size": action.block_size,
        "matrix_shape_x": list(matrix_x.shape),
        "matrix_shape_z": list(matrix_z.shape),
        "matrix_sha256_x": code.matrix_sha256_x,
        "matrix_sha256_z": code.matrix_sha256_z,
        "support_weight_left": len(left),
        "support_weight_right": len(right),
        "support_weight_total": len(left) + len(right),
        "left_right_generator_commutation_verified": True,
        "selected_sums_commute": True,
        "css_commutation_verified": True,
        "max_x_check_weight": int(matrix_x.sum(axis=1).max(initial=0)),
        "max_z_check_weight": int(matrix_z.sum(axis=1).max(initial=0)),
        "max_x_qubit_degree": int(x_qubit_degrees.max(initial=0)),
        "max_z_qubit_degree": int(z_qubit_degrees.max(initial=0)),
        "max_qubit_degree": int(
            (x_qubit_degrees + z_qubit_degrees).max(initial=0)
        ),
    }
    return code


def build_coset_two_block(
    action_id: str,
    left_support: Sequence[str],
    right_support: Sequence[str],
) -> codes.CSSCode:
    """Build a CSS code from a frozen action and sparse element supports."""

    construction = normalize_coset_two_block_construction(
        {
            "kind": CONSTRUCTION_KIND,
            "action_id": action_id,
            "action_catalog_sha256": ACTION_CATALOG_SHA256,
            "left_support": list(left_support),
            "right_support": list(right_support),
        }
    )
    return _build_normalized(construction)


def build_coset_candidate(candidate: Mapping[str, Any]) -> codes.CSSCode:
    """Build from either a Stage-1 candidate or a compact construction."""

    if not isinstance(candidate, Mapping):
        raise ValueError("coset candidate must be a mapping")
    construction_value = candidate.get("construction", candidate)
    if not isinstance(construction_value, Mapping):
        raise ValueError("candidate construction must be a mapping")
    if "kind" in construction_value:
        construction = normalize_coset_two_block_construction(construction_value)
    else:
        required = {"action_id", "left_support", "right_support"}
        missing = required - set(construction_value)
        if missing:
            raise ValueError(f"coset candidate is missing {sorted(missing)}")
        construction = normalize_coset_two_block_construction(
            {
                "kind": CONSTRUCTION_KIND,
                "action_id": construction_value["action_id"],
                "action_catalog_sha256": ACTION_CATALOG_SHA256,
                "left_support": construction_value["left_support"],
                "right_support": construction_value["right_support"],
            }
        )
    return _build_normalized(construction)


def _lift_block_permutation(permutation: tuple[int, ...]) -> list[int]:
    block_size = len(permutation)
    return [*permutation, *(block_size + value for value in permutation)]


def symmetry_generator_proposals(
    construction: Mapping[str, Any],
) -> tuple[dict[str, Any], ...]:
    """Return untrusted action-derived permutation proposals.

    These are *candidates* for matrix automorphisms only.  A later stage must
    replay each proposed row/qubit permutation against the concrete H_X/H_Z
    matrices; no ``verified`` or automorphism claim is made here.
    """

    canonical = normalize_coset_two_block_construction(construction)
    action = get_action(canonical["action_id"])
    proposals: list[dict[str, Any]] = []
    for side_name, action_side in (("left", action.left), ("right", action.right)):
        for element_id in action_side.generator_ids:
            permutation = action_side.id_to_permutation[element_id]
            proposals.append(
                {
                    "id": f"{side_name}:{element_id}",
                    "source_side": side_name,
                    "element_id": element_id,
                    "permutation_convention": "source_to_destination",
                    "block_permutation": list(permutation),
                    "inverse_block_permutation": list(
                        inverse_permutation(permutation)
                    ),
                    "qubit_permutation": _lift_block_permutation(permutation),
                    "x_check_permutation": list(permutation),
                    "z_check_permutation": list(permutation),
                    "verified": False,
                    "verification_required": True,
                }
            )
    return tuple(proposals)


__all__ = [
    "ACTION_CATALOG_SHA256",
    "CONSTRUCTION_KIND",
    "MAX_TOTAL_SUPPORT",
    "action_catalog_sha256",
    "build_coset_candidate",
    "build_coset_two_block",
    "list_action_descriptors",
    "matrix_sha256",
    "normalize_construction",
    "normalize_coset_construction",
    "normalize_coset_two_block_construction",
    "symmetry_generator_proposals",
]
