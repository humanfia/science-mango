"""Generalized-toric seed for the published-volume twisted experiment.

The mutable block proposes only the two non-anchor monomials ``(a,b)`` and
``(c,d)`` in

``A = 1 + x + x^a y^b`` and ``B = 1 + y + x^c y^d``.

The immutable wrapper owns the HNF geometry, expands every non-degenerate
shape across the complete canonical ``0 <= q < m`` range, binds the thin
``(1,127)`` shape to a bounded paper-representative ``q=25`` lane,
injects eight published calibration anchors, and returns ordinary BB
construction mappings.  A published anchor is a known-answer control, never
a novelty or win claim.  No equivalence is claimed for omitted thin-lane q
values.
"""

from __future__ import annotations

from collections.abc import Mapping
from math import gcd, lcm
from typing import Any

from evaluation.geometry import reduce_coordinate
from evaluation.search_contract import PUBLISHED_VOLUME_GEOMETRY_CONTRACT


MAX_TWISTED_POOL = 420
MIN_TWISTED_POOL = 60
MIN_CANDIDATES_PER_TWIST = 3
MAX_RAW_PARAMETER_PROPOSALS = 4000

# Table 3/4 exact-distance rows of Liang--Liu--Song--Chen,
# arXiv:2503.03827v3.  Keys are the paper HNF basis ((0,m),(ell,q)); values are
# the third monomials in the canonical generalized-toric ansatz.  Distances
# are metadata used by the registry/calibration tests, not local proof credit.
PUBLISHED_CALIBRATION_ANCHORS: dict[
    tuple[int, int, int], dict[str, Any]
] = {
    (5, 21, 10): {
        "third_a": (-3, 2), "third_b": (-3, -1),
        "parameters": (210, 10, 16),
    },
    (2, 62, 25): {
        "third_a": (-2, 1), "third_b": (-3, -2),
        "parameters": (248, 10, 18),
    },
    (7, 18, 7): {
        "third_a": (-3, -1), "third_b": (2, -2),
        "parameters": (252, 12, 16),
    },
    (1, 127, 25): {
        "third_a": (-1, -3), "third_b": (0, -6),
        "parameters": (254, 14, 16),
    },
    (2, 66, 28): {
        "third_a": (1, -5), "third_b": (1, 4),
        "parameters": (264, 8, 20),
    },
    (12, 12, 0): {
        "third_a": (-1, -3), "third_b": (3, -1),
        "parameters": (288, 12, 18),
    },
    (7, 21, 7): {
        "third_a": (-3, 1), "third_b": (1, -3),
        "parameters": (294, 10, 20),
    },
    (5, 34, 27): {
        "third_a": (0, -4), "third_b": (4, 0),
        "parameters": (340, 16, 18),
    },
}


def _geometry_descriptor(twist: int) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": int(twist),
    }


def _normalise_support(terms, ell: int, m: int, *, twist: int):
    geometry = _geometry_descriptor(twist)
    return tuple(sorted({
        reduce_coordinate(ell, m, int(x), int(y), geometry)
        for x, y in terms
    }))


def _canonical_candidate_key(
    a_terms,
    b_terms,
    ell: int,
    m: int,
    *,
    twist: int,
):
    """Canonicalize translations and A/B exchange in the twisted quotient."""

    geometry = _geometry_descriptor(twist)
    A = _normalise_support(a_terms, ell, m, twist=twist)
    B = _normalise_support(b_terms, ell, m, twist=twist)
    anchors = tuple(sorted(set(A).union(B)))
    variants = []
    for anchor_x, anchor_y in anchors:
        shifted_a = tuple(sorted(
            reduce_coordinate(
                ell, m, x - anchor_x, y - anchor_y, geometry
            )
            for x, y in A
        ))
        shifted_b = tuple(sorted(
            reduce_coordinate(
                ell, m, x - anchor_x, y - anchor_y, geometry
            )
            for x, y in B
        ))
        pair = (shifted_a, shifted_b)
        swapped = (shifted_b, shifted_a)
        variants.append(pair if pair <= swapped else swapped)
    return min(variants)


def _proposal_terms(proposal) -> tuple[tuple[int, int], tuple[int, int]]:
    if isinstance(proposal, Mapping):
        if set(proposal) == {"third_a", "third_b"}:
            third_a, third_b = proposal["third_a"], proposal["third_b"]
        elif set(proposal) == {"a", "b", "c", "d"}:
            third_a = (proposal["a"], proposal["b"])
            third_b = (proposal["c"], proposal["d"])
        else:
            raise ValueError("parameter proposal has unknown fields")
    elif isinstance(proposal, (list, tuple)) and len(proposal) == 2:
        third_a, third_b = proposal
    else:
        raise ValueError("parameter proposal must contain two monomials")
    if (
        not isinstance(third_a, (list, tuple))
        or len(third_a) != 2
        or not isinstance(third_b, (list, tuple))
        or len(third_b) != 2
    ):
        raise ValueError("third monomials must be exponent pairs")
    values = (*third_a, *third_b)
    if any(isinstance(value, bool) or not isinstance(value, int) for value in values):
        raise ValueError("third-monomial exponents must be integers")
    return (int(third_a[0]), int(third_a[1])), (
        int(third_b[0]), int(third_b[1])
    )


def _parameter_fallbacks(
    ell: int,
    m: int,
    twist: int,
) -> list[dict[str, tuple[int, int]]]:
    """Return immutable ansatz parameters for a degenerate mutation output.

    These are third-monomial parameters, not raw supports.  Consequently the
    same canonical ``1,x`` and ``1,y`` anchors used for every evolved proposal
    remain present even on the thin ``ell=1`` lane.
    """

    if (ell, m, twist) == (1, 127, 25):
        return [
            {"third_a": (0, 114), "third_b": (0, 118)},
            {"third_a": (0, 119), "third_b": (0, 109)},
            {"third_a": (0, 4), "third_b": (0, 89)},
        ]
    return []


def _records_for_twist(
    ell: int,
    m: int,
    twist: int,
    proposals,
) -> list[dict[str, Any]]:
    anchor = PUBLISHED_CALIBRATION_ANCHORS.get((ell, m, twist))
    ordered = []
    if anchor is not None:
        ordered.append({
            "third_a": anchor["third_a"],
            "third_b": anchor["third_b"],
        })
    ordered.extend(_parameter_fallbacks(ell, m, twist))
    ordered.extend(proposals)

    records: list[dict[str, Any]] = []
    seen = set()
    for proposal in ordered:
        try:
            third_a, third_b = _proposal_terms(proposal)
            A = _normalise_support(
                [(0, 0), (1, 0), third_a], ell, m, twist=twist
            )
            B = _normalise_support(
                [(0, 0), (0, 1), third_b], ell, m, twist=twist
            )
        except (TypeError, ValueError):
            continue
        if len(A) != 3 or len(B) != 3 or A == B:
            continue
        key = _canonical_candidate_key(A, B, ell, m, twist=twist)
        if key in seen:
            continue
        seen.add(key)
        records.append({
            "A_terms": [tuple(term) for term in A],
            "B_terms": [tuple(term) for term in B],
            "geometry": _geometry_descriptor(twist),
        })

    return records


def _staggered_proposals(
    proposals: list,
    *,
    ell: int,
    m: int,
    twist: int,
    sample_size: int,
) -> list:
    if not proposals or sample_size <= 0:
        return []
    count = len(proposals)
    if count <= sample_size:
        return list(proposals)
    stride = 2 * twist + 1
    while gcd(stride, count) != 1:
        stride += 2
    start = (twist * 1315423911 + ell * 2654435761 + m * 97531) % count
    selected = [proposals[0]]
    seen_indices = {0}
    cursor = start
    while len(selected) < sample_size and len(seen_indices) < count:
        if cursor not in seen_indices:
            seen_indices.add(cursor)
            selected.append(proposals[cursor])
        cursor = (cursor + stride) % count
    return selected


def _expand_twist_quota(
    ell: int,
    m: int,
    proposals,
    *,
    limit: int,
) -> list[dict[str, Any]]:
    from evaluation.search_contract import allowed_twists

    twists = allowed_twists(
        ell, m, contract=PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    limit = min(MAX_TWISTED_POOL, max(0, int(limit)))
    minimum = MIN_CANDIDATES_PER_TWIST * len(twists)
    if limit < minimum:
        raise ValueError(
            f"candidate limit {limit} cannot provide three rows for "
            f"{len(twists)} twist strata"
        )
    per_twist_target = (limit + len(twists) - 1) // len(twists)
    proposal_budget = min(
        MAX_RAW_PARAMETER_PROPOSALS,
        max(24, 8 * per_twist_target),
    )
    all_proposals = list(proposals)[:MAX_RAW_PARAMETER_PROPOSALS]
    lanes = {
        twist: _records_for_twist(
            ell,
            m,
            twist,
            _staggered_proposals(
                all_proposals,
                ell=ell,
                m=m,
                twist=twist,
                sample_size=proposal_budget,
            ),
        )
        for twist in twists
    }
    insufficient = {
        twist: len(rows)
        for twist, rows in lanes.items()
        if len(rows) < MIN_CANDIDATES_PER_TWIST
    }
    if insufficient:
        raise RuntimeError(
            f"published-volume twist quota is incomplete: {insufficient}"
        )

    positions = {twist: 0 for twist in twists}
    output: list[dict[str, Any]] = []
    while len(output) < limit:
        progressed = False
        for twist in twists:
            position = positions[twist]
            rows = lanes[twist]
            if position >= len(rows):
                continue
            output.append(rows[position])
            positions[twist] += 1
            progressed = True
            if len(output) >= limit:
                break
        if not progressed:
            break
    observed = {int(row["geometry"]["twist"]) for row in output}
    if observed != set(twists):
        raise RuntimeError("published-volume wrapper lost a twist stratum")
    return output


def _default_pool_limit(ell: int, m: int) -> int:
    if (int(ell), int(m)) == (1, 127):
        return MIN_TWISTED_POOL
    return min(
        MAX_TWISTED_POOL,
        max(MIN_TWISTED_POOL, MIN_CANDIDATES_PER_TWIST * int(m)),
    )


# EVOLVE-BLOCK-START
def _generate_parameter_proposals(ell: int, m: int):
    """Propose the two variable monomials of a generalized toric code."""

    points = [
        (x, y)
        for x in range(-ell, ell + 1)
        for y in range(-m, m + 1)
        if (x, y) not in {(0, 0), (1, 0), (0, 1)}
    ]
    points.sort(key=lambda point: (
        -lcm(
            ell // gcd(ell, point[0]),
            m // gcd(m, point[1]),
        ),
        abs(point[0]) + abs(point[1]),
        point,
    ))
    proposals = []
    count = len(points)
    for index, third_a in enumerate(points):
        for stride in (1, 3, 5, 7, 11, 13, 17):
            third_b = points[(index + stride) % count]
            if third_a == third_b:
                continue
            proposals.append((third_a, third_b))
            if len(proposals) >= 1200:
                return proposals
    return proposals
# EVOLVE-BLOCK-END


def generate_candidates(ell: int, m: int) -> list[dict[str, Any]]:
    proposals = _generate_parameter_proposals(ell, m)
    if not isinstance(proposals, (list, tuple)):
        proposals = []
    return _expand_twist_quota(
        ell,
        m,
        proposals,
        limit=_default_pool_limit(ell, m),
    )


__all__ = [
    "MAX_TWISTED_POOL",
    "MIN_CANDIDATES_PER_TWIST",
    "PUBLISHED_CALIBRATION_ANCHORS",
    "_canonical_candidate_key",
    "_default_pool_limit",
    "_expand_twist_quota",
    "generate_candidates",
]
