"""Algebraic fingerprints for replayed negative BB logical witnesses."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from itertools import combinations
from math import gcd
from typing import Any

from evaluation.algebraic_mechanisms import classify_algebraic_mechanism
from evaluation.geometry import candidate_geometry, reduce_coordinate


FINGERPRINT_SCHEMA_VERSION = 1
FINGERPRINT_KIND = "qcode-bb-negative-witness-algebraic-fingerprint"


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _strict_support(value: Any, label: str) -> tuple[tuple[int, int], ...]:
    if not isinstance(value, (list, tuple)):
        raise ValueError(f"{label} must be a support sequence")
    result = []
    for index, term in enumerate(value):
        if (
            not isinstance(term, (list, tuple))
            or len(term) != 2
            or any(type(coordinate) is not int for coordinate in term)
        ):
            raise ValueError(f"{label}[{index}] must be an integer pair")
        result.append((int(term[0]), int(term[1])))
    return tuple(result)


def _element_order(
    delta: tuple[int, int],
    *,
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> int:
    reduced = reduce_coordinate(ell, m, delta[0], delta[1], geometry)
    if reduced == (0, 0):
        return 1
    for multiplier in range(1, ell * m + 1):
        if reduce_coordinate(
            ell,
            m,
            multiplier * reduced[0],
            multiplier * reduced[1],
            geometry,
        ) == (0, 0):
            return multiplier
    raise ValueError("quotient element order exceeded the finite group size")


def _difference_orders(
    points: Sequence[tuple[int, int]],
    *,
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> list[dict[str, Any]]:
    result = {}
    for left, right in combinations(sorted(set(points)), 2):
        delta = reduce_coordinate(
            ell,
            m,
            right[0] - left[0],
            right[1] - left[1],
            geometry,
        )
        result[delta] = _element_order(
            delta,
            ell=ell,
            m=m,
            geometry=geometry,
        )
    return [
        {"difference": list(delta), "element_order": order}
        for delta, order in sorted(result.items())
    ]


def negative_witness_algebraic_fingerprint(
    row: Mapping[str, Any],
    *,
    sector: str,
    weight: int,
    support: Sequence[int],
    witness_sha256: str,
) -> dict[str, Any]:
    """Describe exponent/orbit mechanisms without creating proof credit."""

    ell, m = row.get("ell"), row.get("m")
    if (
        type(ell) is not int
        or type(m) is not int
        or ell < 1
        or m < 1
        or sector not in {"X", "Z"}
        or type(weight) is not int
        or weight < 1
        or not isinstance(witness_sha256, str)
        or len(witness_sha256) != 64
    ):
        raise ValueError("negative witness fingerprint inputs are invalid")
    indices = tuple(int(index) for index in support)
    block_size = ell * m
    if (
        len(indices) != weight
        or len(set(indices)) != len(indices)
        or any(index < 0 or index >= 2 * block_size for index in indices)
    ):
        raise ValueError("negative witness support is invalid")
    support_a = _strict_support(row.get("A_terms"), "A_terms")
    support_b = _strict_support(row.get("B_terms"), "B_terms")
    geometry = candidate_geometry(row)
    twist = 0 if geometry is None else int(geometry["twist"])
    mechanism = classify_algebraic_mechanism(
        support_a,
        support_b,
        ell=ell,
        m=m,
        geometry=geometry,
    )
    smith_d1 = gcd(gcd(ell, m), twist)
    smith_d2 = ell * m // smith_d1

    coordinates: dict[str, list[tuple[int, int]]] = {"left": [], "right": []}
    for index in indices:
        block = "left" if index < block_size else "right"
        offset = index if index < block_size else index - block_size
        coordinates[block].append((offset // m, offset % m))
    for block in coordinates:
        coordinates[block] = sorted(coordinates[block])

    payload = {
        "schema_version": FINGERPRINT_SCHEMA_VERSION,
        "kind": FINGERPRINT_KIND,
        "semantics": (
            "replayed logical upper-bound witness; negative feedback only; "
            "never distance lower-bound, fitness, or promotion evidence"
        ),
        "sector": sector,
        "weight": weight,
        "witness_sha256": witness_sha256,
        "quotient": {
            "volume": ell * m,
            "ell": ell,
            "m": m,
            "q": twist,
            "gcd_ell_m_q": smith_d1,
            "smith_invariants": [smith_d1, smith_d2],
        },
        "support_mechanism": mechanism,
        "support_difference_orders": {
            "A": _difference_orders(
                support_a,
                ell=ell,
                m=m,
                geometry=geometry,
            ),
            "B": _difference_orders(
                support_b,
                ell=ell,
                m=m,
                geometry=geometry,
            ),
        },
        "witness_blocks": {
            block: {
                "coordinates": [list(point) for point in points],
                "difference_orders": _difference_orders(
                    points,
                    ell=ell,
                    m=m,
                    geometry=geometry,
                ),
            }
            for block, points in coordinates.items()
        },
    }
    return {**payload, "fingerprint_sha256": _canonical_sha256(payload)}


__all__ = ["negative_witness_algebraic_fingerprint"]
