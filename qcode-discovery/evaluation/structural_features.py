"""Lightweight canonical structural features shared by search controllers."""

from __future__ import annotations

from typing import Sequence


PATTERN_CLASSIFIER_VERSION = 2


def classify_pattern(
    a_terms: Sequence[Sequence[int]],
    b_terms: Sequence[Sequence[int]],
) -> float:
    """Classify a BB polynomial pair for candidate and pool MAP cells.

    0.0 = univariate
    1.0 = x/y-swap
    2.0 = self-dual
    3.0 = compact mixed monomials
    4.0 = multi-term structure (at least four terms on either side)
    5.0 = hybrid/non-standard pure
    """

    a_set = sorted(tuple(term) for term in a_terms)
    b_set = sorted(tuple(term) for term in b_terms)
    if a_set == b_set:
        return 2.0
    has_many_terms = len(a_terms) >= 4 or len(b_terms) >= 4
    has_mixed = any(x > 0 and y > 0 for x, y in a_terms) or any(
        x > 0 and y > 0 for x, y in b_terms
    )
    if has_many_terms:
        return 4.0
    if has_mixed:
        return 3.0
    a_y_only = all(x == 0 for x, _y in a_terms)
    a_x_only = all(y == 0 for _x, y in a_terms)
    b_y_only = all(x == 0 for x, _y in b_terms)
    b_x_only = all(y == 0 for _x, y in b_terms)
    if (a_y_only and b_x_only) or (a_x_only and b_y_only):
        return 0.0
    a_has_const = any(x == 0 and y == 0 for x, y in a_terms)
    b_has_const = any(x == 0 and y == 0 for x, y in b_terms)
    if a_has_const or b_has_const:
        return 5.0
    return 1.0


def count_terms(
    a_terms: Sequence[Sequence[int]],
    b_terms: Sequence[Sequence[int]],
) -> float:
    """Return the canonical candidate-level MAP support size."""

    return float(max(len(a_terms), len(b_terms)))
