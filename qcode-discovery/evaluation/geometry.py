"""Canonical geometry descriptors for bivariate-bicycle codes.

Historically every candidate in this repository lived on the direct-product
torus ``Z_ell x Z_m``.  A candidate therefore needed only ``ell`` and ``m``.
The optional descriptor introduced here adds the twisted quotient

``Z^2 / <(0, m), (ell, q)>``,

or equivalently the relations ``y^m = 1`` and ``x^ell y^q = 1``.  Coordinates
are represented canonically by ``0 <= i < ell`` and ``0 <= j < m``.  Missing
geometry and ``q = 0`` deliberately canonicalize to ``None`` so existing JSON,
cache keys, and rectangular builders keep their historical identity.
"""

from __future__ import annotations

from collections.abc import Mapping
from numbers import Integral
from typing import Any


GEOMETRY_SCHEMA_VERSION = 1
TWISTED_TORUS_FAMILY = "twisted_torus"
RECTANGULAR_FAMILY = "rectangular"


def _positive_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise ValueError(f"{name} must be an integer")
    result = int(value)
    if result <= 0:
        raise ValueError(f"{name} must be positive")
    return result


def normalize_geometry(
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> dict[str, Any] | None:
    """Validate and canonicalize an optional BB geometry descriptor.

    The canonical non-legacy form is exactly::

        {"schema_version": 1, "family": "twisted_torus", "twist": q}

    where ``0 < q < m``.  ``None``, an explicit rectangular descriptor, and a
    twisted descriptor with ``q = 0`` all return ``None``.  Rejecting unknown
    fields is intentional: a misspelled geometry parameter must not silently
    build a different code.
    """

    _positive_int(ell, "ell")
    m_value = _positive_int(m, "m")
    if geometry is None:
        return None
    if not isinstance(geometry, Mapping):
        raise ValueError("geometry must be a mapping or None")

    family = geometry.get("family")
    if family == RECTANGULAR_FAMILY:
        allowed = {"schema_version", "family"}
        unknown = set(geometry) - allowed
        if unknown:
            raise ValueError(
                f"rectangular geometry has unknown fields: {sorted(unknown)}"
            )
        version = geometry.get("schema_version", GEOMETRY_SCHEMA_VERSION)
        if version != GEOMETRY_SCHEMA_VERSION or isinstance(version, bool):
            raise ValueError(
                f"unsupported geometry schema_version: {version!r}"
            )
        return None

    if family != TWISTED_TORUS_FAMILY:
        raise ValueError(f"unsupported geometry family: {family!r}")

    allowed = {"schema_version", "family", "twist"}
    unknown = set(geometry) - allowed
    if unknown:
        raise ValueError(
            f"twisted_torus geometry has unknown fields: {sorted(unknown)}"
        )
    version = geometry.get("schema_version")
    if version != GEOMETRY_SCHEMA_VERSION or isinstance(version, bool):
        raise ValueError(f"unsupported geometry schema_version: {version!r}")

    twist = geometry.get("twist")
    if isinstance(twist, bool) or not isinstance(twist, Integral):
        raise ValueError("geometry.twist must be an integer")
    twist_value = int(twist)
    if not (0 <= twist_value < m_value):
        raise ValueError(
            f"geometry.twist must satisfy 0 <= twist < m ({m_value})"
        )
    if twist_value == 0:
        return None
    return {
        "schema_version": GEOMETRY_SCHEMA_VERSION,
        "family": TWISTED_TORUS_FAMILY,
        "twist": twist_value,
    }


def candidate_geometry(candidate: Mapping[str, Any]) -> dict[str, Any] | None:
    """Return the canonical optional geometry stored in a candidate mapping."""

    if not isinstance(candidate, Mapping):
        raise ValueError("candidate must be a mapping")
    if "ell" not in candidate or "m" not in candidate:
        raise ValueError("candidate geometry requires ell and m")
    return normalize_geometry(
        candidate["ell"],
        candidate["m"],
        candidate.get("geometry"),
    )


def geometry_identity(
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Return a complete, JSON-safe identity for hashing and deduplication."""

    ell_value = _positive_int(ell, "ell")
    m_value = _positive_int(m, "m")
    canonical = normalize_geometry(ell_value, m_value, geometry)
    if canonical is None:
        return {
            "schema_version": GEOMETRY_SCHEMA_VERSION,
            "family": RECTANGULAR_FAMILY,
            "ell": ell_value,
            "m": m_value,
        }
    return {
        **canonical,
        "ell": ell_value,
        "m": m_value,
    }


def geometry_basis(
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None = None,
) -> tuple[tuple[int, int], tuple[int, int]]:
    """Return relation vectors ``((0,m), (ell,q))`` for the quotient lattice."""

    ell_value = _positive_int(ell, "ell")
    m_value = _positive_int(m, "m")
    canonical = normalize_geometry(ell_value, m_value, geometry)
    twist = 0 if canonical is None else int(canonical["twist"])
    return (0, m_value), (ell_value, twist)


def reduce_coordinate(
    ell: int,
    m: int,
    x_exp: int,
    y_exp: int,
    geometry: Mapping[str, Any] | None = None,
) -> tuple[int, int]:
    """Reduce an ambient exponent pair to the canonical quotient cell.

    For ``x_exp = wraps * ell + x_reduced`` we subtract
    ``wraps * (ell, q)``.  This implements ``x^ell = y^-q`` and then reduces
    the remaining y exponent modulo ``m``.  Python's ``divmod`` makes the same
    formula valid for negative exponents, which is needed by the X/Z isometry.
    """

    ell_value = _positive_int(ell, "ell")
    m_value = _positive_int(m, "m")
    if isinstance(x_exp, bool) or not isinstance(x_exp, Integral):
        raise ValueError("x_exp must be an integer")
    if isinstance(y_exp, bool) or not isinstance(y_exp, Integral):
        raise ValueError("y_exp must be an integer")
    canonical = normalize_geometry(ell_value, m_value, geometry)
    twist = 0 if canonical is None else int(canonical["twist"])
    wraps, x_reduced = divmod(int(x_exp), ell_value)
    y_reduced = (int(y_exp) - wraps * twist) % m_value
    return x_reduced, y_reduced


__all__ = [
    "GEOMETRY_SCHEMA_VERSION",
    "RECTANGULAR_FAMILY",
    "TWISTED_TORUS_FAMILY",
    "candidate_geometry",
    "geometry_basis",
    "geometry_identity",
    "normalize_geometry",
    "reduce_coordinate",
]
