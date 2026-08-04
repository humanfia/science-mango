"""Deterministic algebraic-mechanism descriptors for BB-code supports.

This module deliberately contains no evaluator or numerical dependencies.  It
turns the two Laurent-polynomial supports of a bivariate bicycle candidate into
a small, JSON-serialisable descriptor suitable for portfolio quotas and
MAP-Elites cells.

The labels are structural heuristics, not mathematical claims about distance:

``complementary_diagonal``
    Each support spans one affine line and the two line directions differ.
``affine_orbit``
    The supports are related by a translation and a signed coordinate
    permutation (on the supplied torus when ``ell`` and ``m`` are known).
``shared_anchor_coset``
    The supports share an exponent (an anchor) and at least one primitive
    difference direction, but do not satisfy a stronger rule above.
``asymmetric_anchor``
    Exactly one support is two-dimensional or contains an axis-aligned corner.
``unstructured``
    None of the deterministic relations above applies.

The public function accepts either a candidate mapping with ``A_terms`` and
``B_terms``, a pair ``(A_terms, B_terms)``, or two explicit support arguments.
Individual terms may be exponent pairs or mappings such as ``{"x": 2,
"y": 3}`` / ``{"x_exp": 2, "y_exp": 3}``.  A polynomial may also be a
mapping from exponent pairs to coefficients; zero coefficients are ignored.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from functools import lru_cache
from math import gcd, lcm
from typing import Any

from evaluation.geometry import normalize_geometry, reduce_coordinate


RELATION_TYPES = (
    "affine_orbit",
    "shared_anchor_coset",
    "complementary_diagonal",
    "asymmetric_anchor",
    "unstructured",
)


def _integer(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{label} must be an integer, got {value!r}")
    return int(value)


def _term_pair(term: Any) -> tuple[int, int]:
    if isinstance(term, Mapping):
        for x_key, y_key in (("x", "y"), ("x_exp", "y_exp"), ("i", "j")):
            if x_key in term and y_key in term:
                return (
                    _integer(term[x_key], f"term[{x_key!r}]"),
                    _integer(term[y_key], f"term[{y_key!r}]"),
                )
        if 0 in term and 1 in term:
            return (_integer(term[0], "term[0]"), _integer(term[1], "term[1]"))
        raise TypeError(f"term mapping has no recognised exponent keys: {term!r}")
    if isinstance(term, Sequence) and not isinstance(term, (str, bytes)):
        if len(term) != 2:
            raise TypeError(f"term must contain two exponents, got {term!r}")
        return (_integer(term[0], "term[0]"), _integer(term[1], "term[1]"))
    raise TypeError(f"term must be an exponent pair, got {term!r}")


def _normalise_terms(
    terms: Any,
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> tuple[tuple[int, int], ...]:
    if isinstance(terms, Mapping):
        if "terms" in terms:
            terms = terms["terms"]
        elif any(key in terms for key in ("x", "x_exp", "i", 0)):
            terms = (terms,)
        else:
            # Sparse-polynomial form: {(x, y): coefficient}.  Coefficients are
            # interpreted only as zero/non-zero; BB supports are binary.
            terms = tuple(key for key, coefficient in terms.items() if coefficient)
    if isinstance(terms, (str, bytes)) or not isinstance(terms, Iterable):
        raise TypeError("terms must be an iterable of exponent pairs")

    normalised: set[tuple[int, int]] = set()
    for raw_term in terms:
        x, y = _term_pair(raw_term)
        if ell is not None and m is not None:
            x, y = _reduce(x, y, ell=ell, m=m, twist=twist)
        else:
            if ell is not None:
                x %= ell
            if m is not None:
                y %= m
        normalised.add((x, y))
    return tuple(sorted(normalised))


def _candidate_parts(
    candidate_or_a_terms: Any,
    b_terms: Any | None,
    ell: int | None,
    m: int | None,
    geometry: Mapping[str, Any] | None,
) -> tuple[Any, Any, int | None, int | None, Mapping[str, Any] | None]:
    if b_terms is not None:
        return candidate_or_a_terms, b_terms, ell, m, geometry
    if isinstance(candidate_or_a_terms, Mapping):
        if "A_terms" not in candidate_or_a_terms or "B_terms" not in candidate_or_a_terms:
            raise TypeError("candidate mapping must contain A_terms and B_terms")
        if ell is None and candidate_or_a_terms.get("ell") is not None:
            ell = _integer(candidate_or_a_terms["ell"], "ell")
        if m is None and candidate_or_a_terms.get("m") is not None:
            m = _integer(candidate_or_a_terms["m"], "m")
        if geometry is None:
            geometry = candidate_or_a_terms.get("geometry")
        return (
            candidate_or_a_terms["A_terms"],
            candidate_or_a_terms["B_terms"],
            ell,
            m,
            geometry,
        )
    if (
        isinstance(candidate_or_a_terms, Sequence)
        and not isinstance(candidate_or_a_terms, (str, bytes))
        and len(candidate_or_a_terms) == 2
    ):
        return candidate_or_a_terms[0], candidate_or_a_terms[1], ell, m, geometry
    raise TypeError(
        "pass a candidate mapping, an (A_terms, B_terms) pair, or explicit B_terms"
    )


def _geometry_from_twist(twist: int) -> dict[str, Any] | None:
    if twist == 0:
        return None
    return {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": twist,
    }


def _reduce(
    x: int,
    y: int,
    *,
    ell: int,
    m: int,
    twist: int,
) -> tuple[int, int]:
    """Reduce one group element in the selected quotient geometry."""

    if twist == 0:
        return x % ell, y % m
    return reduce_coordinate(
        ell,
        m,
        x,
        y,
        _geometry_from_twist(twist),
    )


def _primitive(dx: int, dy: int) -> tuple[int, int] | None:
    if dx == 0 and dy == 0:
        return None
    divisor = gcd(abs(dx), abs(dy))
    dx //= divisor
    dy //= divisor
    if dx < 0 or (dx == 0 and dy < 0):
        dx, dy = -dx, -dy
    return dx, dy


def _torus_delta(
    first: tuple[int, int],
    second: tuple[int, int],
    *,
    ell: int,
    m: int,
    twist: int = 0,
) -> tuple[int, int]:
    """Return the oriented difference in the selected finite quotient."""

    return _reduce(
        second[0] - first[0],
        second[1] - first[1],
        ell=ell,
        m=m,
        twist=twist,
    )


@lru_cache(maxsize=8192)
def _element_order(
    delta: tuple[int, int], *, ell: int, m: int, twist: int = 0,
) -> int:
    """Return the additive order of one element of the finite quotient."""

    dx, dy = delta
    if twist == 0:
        return lcm(ell // gcd(ell, dx), m // gcd(m, dy))
    current = (0, 0)
    for order in range(1, ell * m + 1):
        current = _reduce(
            current[0] + dx,
            current[1] + dy,
            ell=ell,
            m=m,
            twist=twist,
        )
        if current == (0, 0):
            return order
    raise ValueError("quotient element order exceeds the finite group size")


@lru_cache(maxsize=4096)
def _cyclic_subgroup(
    delta: tuple[int, int],
    *,
    ell: int,
    m: int,
    twist: int = 0,
) -> frozenset[tuple[int, int]]:
    """Return a canonical representation of the subgroup generated by delta."""

    order = _element_order(delta, ell=ell, m=m, twist=twist)
    dx, dy = delta
    return frozenset(
        _reduce(
            scale * dx,
            scale * dy,
            ell=ell,
            m=m,
            twist=twist,
        )
        for scale in range(order)
    )


@lru_cache(maxsize=4096)
def _directions(
    terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> frozenset[object]:
    """Return canonical unoriented intra-support difference directions.

    On a finite torus a direction is the cyclic subgroup generated by the
    modular difference.  This is invariant under wrap-around and identifies a
    difference with its negative without choosing an arbitrary signed residue.
    Without a complete torus modulus, the legacy primitive-integer direction
    is retained.
    """

    result: set[object] = set()
    for index, (x1, y1) in enumerate(terms):
        for x2, y2 in terms[index + 1 :]:
            if ell is not None and m is not None:
                delta = _torus_delta(
                    (x1, y1),
                    (x2, y2),
                    ell=ell,
                    m=m,
                    twist=twist,
                )
                direction = (
                    None
                    if delta == (0, 0)
                    else _cyclic_subgroup(
                        delta, ell=ell, m=m, twist=twist,
                    )
                )
            else:
                direction = _primitive(x2 - x1, y2 - y1)
            if direction is not None:
                result.add(direction)
    return frozenset(result)


@lru_cache(maxsize=8192)
def _affine_span_key(
    terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> object | None:
    """Return the rank-one span key, or ``None`` for rank zero/two.

    For a finite torus, rank one means that all affine differences lie in a
    cyclic subgroup generated by an observed support difference.  The key is
    that subgroup itself, not a representative vector.  The latter would be
    unstable at the periodic boundary and non-unique for composite moduli.
    """

    if len(terms) < 2:
        return None
    x0, y0 = terms[0]
    if ell is not None and m is not None:
        anchor_differences = [
            _torus_delta(
                (x0, y0), (x, y), ell=ell, m=m, twist=twist,
            )
            for x, y in terms[1:]
            if (x, y) != (x0, y0)
        ]
        if not anchor_differences:
            return None
        observed_differences = {
            _torus_delta(
                first, second, ell=ell, m=m, twist=twist,
            )
            for index, first in enumerate(terms)
            for second in terms[index + 1 :]
        }
        containing_subgroups = {
            _cyclic_subgroup(delta, ell=ell, m=m, twist=twist)
            for delta in observed_differences
            if delta != (0, 0)
        }
        containing_subgroups = {
            subgroup
            for subgroup in containing_subgroups
            if all(delta in subgroup for delta in anchor_differences)
            # A cyclic presentation of the entire product can occur when the
            # two moduli are coprime.  Treating that as a one-dimensional
            # geometric orbit would collapse every support on the torus into
            # one bin, so only proper cyclic subgroups count when both axes
            # are non-trivial.
            and not (
                ell > 1 and m > 1 and len(subgroup) == ell * m
            )
        }
        if containing_subgroups:
            subgroup = min(
                containing_subgroups,
                key=lambda value: (len(value), tuple(sorted(value))),
            )
            return tuple(sorted(subgroup))
        return None

    nonzero = [
        (x - x0, y - y0)
        for x, y in terms[1:]
        if (x, y) != (x0, y0)
    ]
    if not nonzero:
        return None
    dx, dy = nonzero[0]
    if all(dx * other_y == dy * other_x for other_x, other_y in nonzero[1:]):
        return _primitive(dx, dy)
    return None


def _affine_rank(
    terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> int:
    if len(terms) < 2:
        return 0
    return (
        1
        if _affine_span_key(
            terms, ell=ell, m=m, twist=twist,
        ) is not None
        else 2
    )


def _complementary_diagonal(
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> bool:
    a_direction = _affine_span_key(
        a_terms, ell=ell, m=m, twist=twist,
    )
    b_direction = _affine_span_key(
        b_terms, ell=ell, m=m, twist=twist,
    )
    return bool(
        a_direction is not None
        and b_direction is not None
        and a_direction != b_direction
    )


def _signed_coordinate_maps(allow_swap: bool):
    for sign_x in (-1, 1):
        for sign_y in (-1, 1):
            yield lambda x, y, sx=sign_x, sy=sign_y: (sx * x, sy * y)
            if allow_swap:
                yield lambda x, y, sx=sign_x, sy=sign_y: (sx * y, sy * x)


@lru_cache(maxsize=256)
def _quotient_signed_coordinate_matrices(
    ell: int,
    m: int,
    twist: int,
) -> tuple[tuple[int, int, int, int], ...]:
    """Return signed-coordinate maps that are automorphisms of the quotient."""

    candidates: list[tuple[int, int, int, int]] = []
    for sign_x in (-1, 1):
        for sign_y in (-1, 1):
            candidates.append((sign_x, 0, 0, sign_y))
            if ell == m:
                candidates.append((0, sign_x, sign_y, 0))

    result: list[tuple[int, int, int, int]] = []
    domain = tuple(
        (x_coord, y_coord)
        for x_coord in range(ell)
        for y_coord in range(m)
    )
    for matrix in candidates:
        a, b, c, d = matrix

        # A coordinate formula descends to the quotient only if it maps both
        # defining relations to zero.  Bijectivity then makes it an
        # automorphism rather than a non-invertible endomorphism.
        relation_y = _reduce(
            b * m,
            d * m,
            ell=ell,
            m=m,
            twist=twist,
        )
        relation_x = _reduce(
            a * ell + b * twist,
            c * ell + d * twist,
            ell=ell,
            m=m,
            twist=twist,
        )
        if relation_y != (0, 0) or relation_x != (0, 0):
            continue
        image = {
            _reduce(
                a * x_coord + b * y_coord,
                c * x_coord + d * y_coord,
                ell=ell,
                m=m,
                twist=twist,
            )
            for x_coord, y_coord in domain
        }
        if len(image) == ell * m:
            result.append(matrix)
    return tuple(result)


def _affine_orbit(
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> bool:
    if len(a_terms) != len(b_terms) or not a_terms:
        return False
    b_set = set(b_terms)
    if twist == 0:
        # Keep the historical rectangular classifier bit-for-bit stable.
        allow_swap = ell is None or m is None or ell == m
        for transform in _signed_coordinate_maps(allow_swap):
            transformed = [transform(x, y) for x, y in a_terms]
            first_x, first_y = transformed[0]
            for target_x, target_y in b_terms:
                shift_x, shift_y = target_x - first_x, target_y - first_y
                image = set()
                for x, y in transformed:
                    image_x, image_y = x + shift_x, y + shift_y
                    if ell is not None:
                        image_x %= ell
                    if m is not None:
                        image_y %= m
                    image.add((image_x, image_y))
                if image == b_set:
                    return True
        return False

    if ell is None or m is None:
        raise ValueError("twisted affine-orbit classification requires ell and m")
    for a, b, c, d in _quotient_signed_coordinate_matrices(ell, m, twist):
        transformed = [
            _reduce(
                a * x + b * y,
                c * x + d * y,
                ell=ell,
                m=m,
                twist=twist,
            )
            for x, y in a_terms
        ]
        first = transformed[0]
        for target in b_terms:
            shift_x, shift_y = _torus_delta(
                first, target, ell=ell, m=m, twist=twist,
            )
            image = {
                _reduce(
                    x + shift_x,
                    y + shift_y,
                    ell=ell,
                    m=m,
                    twist=twist,
                )
                for x, y in transformed
            }
            if image == b_set:
                return True
    return False


def _has_axis_anchor(
    terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None = None,
    m: int | None = None,
    twist: int = 0,
) -> bool:
    if twist != 0:
        if ell is None or m is None:
            raise ValueError("twisted axis classification requires ell and m")
        x_axis = _cyclic_subgroup(
            (1, 0), ell=ell, m=m, twist=twist,
        )
        y_axis = _cyclic_subgroup(
            (0, 1), ell=ell, m=m, twist=twist,
        )
        for anchor in terms:
            deltas = {
                _torus_delta(
                    anchor, other, ell=ell, m=m, twist=twist,
                )
                for other in terms
                if other != anchor
            }
            if (
                any(delta in x_axis for delta in deltas)
                and any(delta in y_axis for delta in deltas)
            ):
                return True
        return False
    for anchor_x, anchor_y in terms:
        shares_x = any(x == anchor_x and y != anchor_y for x, y in terms)
        shares_y = any(y == anchor_y and x != anchor_x for x, y in terms)
        if shares_x and shares_y:
            return True
    return False


def _relation_type(
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> str:
    if _complementary_diagonal(
        a_terms, b_terms, ell=ell, m=m, twist=twist,
    ):
        return "complementary_diagonal"
    if _affine_orbit(
        a_terms, b_terms, ell=ell, m=m, twist=twist,
    ):
        return "affine_orbit"
    if set(a_terms).intersection(b_terms) and _directions(
        a_terms, ell=ell, m=m, twist=twist,
    ).intersection(
        _directions(b_terms, ell=ell, m=m, twist=twist)
    ):
        return "shared_anchor_coset"

    a_asymmetric = (
        _affine_rank(a_terms, ell=ell, m=m, twist=twist) == 2
        or _has_axis_anchor(
            a_terms, ell=ell, m=m, twist=twist,
        )
    )
    b_asymmetric = (
        _affine_rank(b_terms, ell=ell, m=m, twist=twist) == 2
        or _has_axis_anchor(
            b_terms, ell=ell, m=m, twist=twist,
        )
    )
    if a_asymmetric != b_asymmetric:
        return "asymmetric_anchor"
    return "unstructured"


def _difference_spectrum_bin(
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    *,
    ell: int | None,
    m: int | None,
    twist: int = 0,
) -> int:
    size = len(
        _directions(a_terms, ell=ell, m=m, twist=twist).union(
            _directions(b_terms, ell=ell, m=m, twist=twist)
        )
    )
    if size == 0:
        return 0
    if size <= 2:
        return 1
    if size <= 5:
        return 2
    return 3


def classify_algebraic_mechanism(
    candidate_or_a_terms: Any,
    b_terms: Any | None = None,
    *,
    ell: int | None = None,
    m: int | None = None,
    geometry: Mapping[str, Any] | None = None,
) -> dict[str, str | int]:
    """Return a stable mechanism descriptor for a pair of BB supports.

    ``orbit_span_bin`` is the affine rank (0, 1, or 2) of the combined
    support.  On ``Z_ell x Z_m``, rank one means that all support differences
    lie in one cyclic subgroup generated by an observed difference.
    ``difference_spectrum_bin`` buckets the number of
    distinct cyclic subgroups generated by intra-support differences as 0,
    1--2, 3--5, or 6+ (and uses primitive integer directions without torus
    dimensions).
    These deliberately small integer domains can be used directly as MAP
    dimensions.  Duplicate terms and input ordering do not affect the result.
    """

    raw_a, raw_b, ell, m, geometry = _candidate_parts(
        candidate_or_a_terms, b_terms, ell, m, geometry,
    )
    if ell is not None:
        ell = _integer(ell, "ell")
        if ell <= 0:
            raise ValueError("ell must be positive")
    if m is not None:
        m = _integer(m, "m")
        if m <= 0:
            raise ValueError("m must be positive")
    if geometry is not None and (ell is None or m is None):
        raise ValueError("geometry requires both ell and m")
    canonical_geometry = (
        normalize_geometry(ell, m, geometry)
        if ell is not None and m is not None
        else None
    )
    twist = (
        0
        if canonical_geometry is None
        else int(canonical_geometry["twist"])
    )

    a_terms = _normalise_terms(raw_a, ell=ell, m=m, twist=twist)
    b_terms_normalised = _normalise_terms(
        raw_b, ell=ell, m=m, twist=twist,
    )
    combined = tuple(sorted(set(a_terms).union(b_terms_normalised)))
    return {
        "relation_type": _relation_type(
            a_terms,
            b_terms_normalised,
            ell=ell,
            m=m,
            twist=twist,
        ),
        "orbit_span_bin": _affine_rank(
            combined, ell=ell, m=m, twist=twist,
        ),
        "difference_spectrum_bin": _difference_spectrum_bin(
            a_terms,
            b_terms_normalised,
            ell=ell,
            m=m,
            twist=twist,
        ),
        "support_split_type": f"{len(a_terms)}+{len(b_terms_normalised)}",
    }


__all__ = ["RELATION_TYPES", "classify_algebraic_mechanism"]
