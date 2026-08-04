"""Bivariate bicycle code construction and parameter computation.

Thin wrapper around ``qldpc.codes.BBCode`` that converts exponent-based
representations to sympy polynomials and provides a unified interface
for the evaluation pipeline.

A bivariate bicycle (BB) code is defined by two sparse polynomials over a
finite quotient of ``F_2[x, y]``.  The historical geometry is the rectangular
ring ``F_2[x, y] / (x^ell - 1, y^m - 1)``.  An optional geometry descriptor
also supports the twisted quotient with ``y^m = 1`` and
``x^ell y^q = 1``.  Each polynomial is represented in
this module as a list of three ``(x_exp, y_exp)`` tuples -- for example,
``[(3, 0), (0, 1), (0, 2)]`` encodes the polynomial ``x^3 + y + y^2``.

The module exposes four public helpers used throughout the project:

* :func:`terms_to_poly` -- convert exponent tuples to a sympy expression.
* :func:`validate_terms` -- check that a term list is a well-formed trinomial
  for a given ``(ell, m)`` lattice.
* :func:`build_bb_code` -- construct a :class:`qldpc.codes.BBCode` object.
* :func:`get_code_params_fast` -- return ``(n, k)`` without computing distance.

Typical usage::

    code = build_bb_code(12, 6,
                         [(3, 0), (0, 1), (0, 2)],   # A = x^3 + y + y^2
                         [(0, 3), (1, 0), (2, 0)])    # B = y^3 + x + x^2
    n, k = get_code_params_fast(code)                 # (144, 12)
"""

from __future__ import annotations

from collections.abc import Mapping
from functools import lru_cache
from typing import Any

import numpy as np
import sympy
from sympy.abc import x, y
from qldpc import codes

from evaluation.geometry import (
    geometry_basis,
    geometry_identity,
    normalize_geometry,
)


def terms_to_poly(terms: list[tuple[int, int]]) -> sympy.Expr:
    """Convert exponent pairs to a sympy polynomial.

    Args:
        terms: List of (x_exp, y_exp) tuples, e.g. [(3,0), (1,0), (0,1)].

    Returns:
        Sympy expression like x**3 + x + y.
    """
    monomials = []
    for x_exp, y_exp in terms:
        monomials.append(x ** x_exp * y ** y_exp)
    return sum(monomials)


def validate_terms(
    ell: int, m: int, terms: list[tuple[int, int]], name: str = "polynomial",
    min_terms: int = 2, max_terms: int = 6,
) -> None:
    """Validate that terms define a proper polynomial for the given lattice.

    Raises ValueError if:
    - Term count outside [min_terms, max_terms]
    - Duplicate monomials (after reducing mod ell, m)
    - Exponents out of range
    """
    if not (min_terms <= len(terms) <= max_terms):
        raise ValueError(
            f"{name} must have {min_terms}-{max_terms} terms, got {len(terms)}"
        )

    reduced = set()
    for x_exp, y_exp in terms:
        if not (0 <= x_exp < ell):
            raise ValueError(
                f"{name}: x-exponent {x_exp} out of range [0, {ell})"
            )
        if not (0 <= y_exp < m):
            raise ValueError(
                f"{name}: y-exponent {y_exp} out of range [0, {m})"
            )
        monomial = (x_exp % ell, y_exp % m)
        if monomial in reduced:
            raise ValueError(
                f"{name}: duplicate monomial x^{x_exp}*y^{y_exp}"
            )
        reduced.add(monomial)


def build_bb_code(
    ell: int,
    m: int,
    A_terms: list[tuple[int, int]],
    B_terms: list[tuple[int, int]],
    *,
    geometry: Mapping[str, Any] | None = None,
) -> codes.BBCode | "TwistedBBCode":
    """Construct a BBCode from lattice dimensions and exponent lists.

    Args:
        ell: Canonical x-coordinate extent.  It is the x order only for the
            rectangular geometry.
        m: Canonical y-coordinate extent and cyclic order of y.
        A_terms: 3 monomials [(a1,b1), (a2,b2), (a3,b3)] for polynomial A.
        B_terms: 3 monomials [(b1,c1), (b2,c2), (b3,c3)] for polynomial B.
        geometry: Optional canonical geometry descriptor.  Missing geometry or
            ``twist=0`` uses the original qldpc ``BBCode`` construction.

    Returns:
        A qldpc ``BBCode`` for the legacy rectangular geometry, or a
        ``TwistedBBCode`` (a qldpc ``CSSCode``) for a nonzero twist.
    """
    canonical_geometry = normalize_geometry(ell, m, geometry)
    poly_a = terms_to_poly(A_terms)
    poly_b = terms_to_poly(B_terms)
    if canonical_geometry is None:
        # Keep this path byte-for-byte equivalent to the historical builder.
        return codes.BBCode({x: ell, y: m}, poly_a, poly_b)
    return TwistedBBCode(
        ell,
        m,
        A_terms,
        B_terms,
        geometry=canonical_geometry,
    )


@lru_cache(maxsize=4096)
def _translation_columns(
    ell: int,
    m: int,
    x_exp: int,
    y_exp: int,
    *,
    twist: int,
) -> np.ndarray:
    """Return cached destination columns for one quotient translation."""

    ell = int(ell)
    m = int(m)
    block_size = ell * m
    rows = np.arange(block_size, dtype=np.int64)
    x_coords = rows // m
    y_coords = rows % m
    wraps, reduced_x = np.divmod(x_coords + int(x_exp), ell)
    reduced_y = np.mod(y_coords + int(y_exp) - wraps * int(twist), m)
    columns = reduced_x * m + reduced_y
    columns.setflags(write=False)
    return columns


def _translation_matrix(
    ell: int,
    m: int,
    x_exp: int,
    y_exp: int,
    *,
    twist: int,
) -> np.ndarray:
    """Return the regular-representation matrix for ``x^x_exp y^y_exp``.

    Matrix rows and columns use NumPy's flattened ``(ell, m)`` ordering.  A
    row for cell ``(i,j)`` has its one in the column for
    ``reduce(i+x_exp, j+y_exp)``.  This is the same convention as
    ``qldpc.BBCode.eval(...).lift().T`` when ``twist == 0``.
    """

    block_size = int(ell) * int(m)
    rows = np.arange(block_size, dtype=np.int64)
    columns = _translation_columns(
        int(ell),
        int(m),
        int(x_exp),
        int(y_exp),
        twist=int(twist),
    )
    matrix = np.zeros((block_size, block_size), dtype=np.uint8)
    matrix[rows, columns] = 1
    return matrix


def _polynomial_matrix(
    ell: int,
    m: int,
    terms: list[tuple[int, int]],
    *,
    twist: int,
) -> np.ndarray:
    """Evaluate a sparse binary polynomial in the twisted group algebra."""

    block_size = int(ell) * int(m)
    rows = np.arange(block_size, dtype=np.int64)
    matrix = np.zeros((block_size, block_size), dtype=np.uint8)
    for x_exp, y_exp in terms:
        columns = _translation_columns(
            int(ell),
            int(m),
            int(x_exp),
            int(y_exp),
            twist=int(twist),
        )
        matrix[rows, columns] ^= 1
    return matrix


class TwistedBBCode(codes.CSSCode):
    """Generalized BB code over ``Z^2 / <(0,m),(ell,q)>``.

    The class intentionally exposes the ordinary qldpc ``CSSCode`` interface
    used by distance and certificate code.  Metadata needed to reconstruct the
    outer geometry is retained in ``geometry`` and ``geometry_identity``.
    """

    def __init__(
        self,
        ell: int,
        m: int,
        A_terms: list[tuple[int, int]],
        B_terms: list[tuple[int, int]],
        *,
        geometry: Mapping[str, Any],
    ) -> None:
        canonical = normalize_geometry(ell, m, geometry)
        if canonical is None:
            raise ValueError("TwistedBBCode requires a nonzero twist")
        twist = int(canonical["twist"])
        matrix_a = _polynomial_matrix(ell, m, A_terms, twist=twist)
        matrix_b = _polynomial_matrix(ell, m, B_terms, twist=twist)
        matrix_x = np.hstack((matrix_a, matrix_b))
        matrix_z = np.hstack((matrix_b.T, matrix_a.T))
        super().__init__(
            matrix_x,
            matrix_z,
            field=2,
            promise_equal_distance_xz=True,
        )

        # Retain reconstruction metadata without exposing BBCode.orders: x
        # generally has order ell*m/gcd(m,q), so ``orders=(ell,m)`` would be a
        # mathematically false direct-product claim.
        self.ell = int(ell)
        self.m = int(m)
        self.layout_shape = (self.ell, self.m)
        self.poly_a = sympy.Poly(terms_to_poly(A_terms), x, y)
        self.poly_b = sympy.Poly(terms_to_poly(B_terms), x, y)
        self.A_terms = tuple(tuple(map(int, term)) for term in A_terms)
        self.B_terms = tuple(tuple(map(int, term)) for term in B_terms)
        self.geometry = dict(canonical)
        self.geometry_identity = geometry_identity(
            self.ell,
            self.m,
            canonical,
        )
        self.relation_basis = geometry_basis(
            self.ell,
            self.m,
            canonical,
        )


def get_code_params_fast(code: codes.CSSCode) -> tuple[int, int]:
    """Get (n, k) quickly -- no distance computation.

    Returns:
        (n, k) where n = num_qubits, k = dimension.
    """
    return code.num_qudits, code.dimension
