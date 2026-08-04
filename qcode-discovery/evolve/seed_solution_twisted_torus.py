"""Seed for the proof-compatible twisted-torus BB representation.

The evolved block proposes sparse polynomial supports.  Geometry allocation is
deliberately outside that block: :func:`generate_candidates` expands the
proposals across every contracted twist ``0 <= q < m`` with a deterministic
round-robin quota.  This prevents the optimizer from collapsing back to the
rectangular ``q=0`` lane while retaining the historical
``generate_candidates(ell, m)`` entry point.

Candidate records use the explicit, extensible mapping schema::

    {
        "A_terms": [(a, b), ...],
        "B_terms": [(c, d), ...],
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": q,
        },
    }

The quotient relations are ``y^m=1`` and ``x^ell*y^q=1``.  A geometry label
is a construction input, not a distance or novelty claim.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from evaluation.geometry import reduce_coordinate
from evaluation.search_contract import (
    TWISTED_MIN_CANDIDATES_PER_TWIST,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    allowed_twists,
)


CHALLENGE_TERM_SPLITS = frozenset({
    (2, 2),
    (2, 3),
    (3, 2),
    (2, 4),
    (4, 2),
    (3, 3),
})
MAX_TWISTED_POOL = 300
MIN_TWISTED_POOL = 60
MIN_CANDIDATES_PER_TWIST = TWISTED_MIN_CANDIDATES_PER_TWIST
MAX_RAW_SUPPORT_PROPOSALS = 4000


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
    """Canonicalize translation and A/B exchange in the twisted quotient.

    A wrap in the x coordinate changes y by ``-q``.  Applying independent
    coordinatewise modulo arithmetic here would therefore be mathematically
    wrong for every nonzero twist.
    """

    geometry = _geometry_descriptor(twist)
    A = _normalise_support(a_terms, ell, m, twist=twist)
    B = _normalise_support(b_terms, ell, m, twist=twist)
    anchors = tuple(sorted(set(A).union(B)))
    variants = []
    for anchor_x, anchor_y in anchors:
        shifted_a = tuple(sorted(
            reduce_coordinate(
                ell,
                m,
                x - anchor_x,
                y - anchor_y,
                geometry,
            )
            for x, y in A
        ))
        shifted_b = tuple(sorted(
            reduce_coordinate(
                ell,
                m,
                x - anchor_x,
                y - anchor_y,
                geometry,
            )
            for x, y in B
        ))
        pair = (shifted_a, shifted_b)
        swapped = (shifted_b, shifted_a)
        variants.append(pair if pair <= swapped else swapped)
    if not variants:
        pair = (A, B)
        swapped = (B, A)
        return pair if pair <= swapped else swapped
    return min(variants)


def _proposal_terms(proposal) -> tuple[Any, Any]:
    """Extract an A/B support proposal without accepting geometry control."""

    if isinstance(proposal, Mapping):
        unknown = set(proposal) - {"A_terms", "B_terms"}
        if unknown:
            raise ValueError(
                "support proposal cannot set outer geometry or metadata: "
                f"{sorted(unknown)}"
            )
        return proposal["A_terms"], proposal["B_terms"]
    if not isinstance(proposal, (list, tuple)) or len(proposal) != 2:
        raise ValueError("support proposal must contain exactly A_terms/B_terms")
    return proposal[0], proposal[1]


def _fallback_support_proposals(ell: int, m: int):
    """Return immutable legal supports so every twist remains observable."""

    # Every contracted axis has length at least two.  These small local cells
    # remain syntactically legal on the thinnest 2-by-N and N-by-2 shapes.
    return [
        (
            [(0, 0), (1 % ell, 0)],
            [(0, 1 % m), (1 % ell, 1 % m)],
        ),
        (
            [(0, 0), (0, 1 % m)],
            [(1 % ell, 0), (1 % ell, 1 % m)],
        ),
        (
            [(0, 0), (1 % ell, 1 % m)],
            [(1 % ell, 0), (0, 1 % m)],
        ),
    ]


def _records_for_twist(
    ell: int,
    m: int,
    twist: int,
    proposals,
) -> list[dict[str, Any]]:
    records = []
    seen = set()
    for proposal in [*proposals, *_fallback_support_proposals(ell, m)]:
        try:
            a_terms, b_terms = _proposal_terms(proposal)
            A = _normalise_support(a_terms, ell, m, twist=twist)
            B = _normalise_support(b_terms, ell, m, twist=twist)
        except (KeyError, TypeError, ValueError):
            continue
        split = (len(A), len(B))
        if split not in CHALLENGE_TERM_SPLITS or len(A) + len(B) > 6:
            continue
        if A == B:
            continue
        key = _canonical_candidate_key(
            A,
            B,
            ell,
            m,
            twist=twist,
        )
        if key in seen:
            continue
        seen.add(key)
        records.append({
            "A_terms": [tuple(term) for term in A],
            "B_terms": [tuple(term) for term in B],
            # Keep q=0 explicit in generator output.  The builder canonicalizes
            # it to legacy rectangular identity, while coverage accounting can
            # still prove that the zero-twist stratum was requested.
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
    """Select a reproducible q-dependent slice from the complete vocabulary."""

    from math import gcd

    if not proposals or sample_size <= 0:
        return []
    count = len(proposals)
    if count <= sample_size:
        return list(proposals)

    # Proposal zero is a common anchor across q lanes.  Remaining positions
    # use a q-dependent cyclic permutation, so a wide-m shape with only three
    # final records per twist still exposes the whole evolved vocabulary over
    # all twists instead of repeating its first three rows ninety times.
    stride = 2 * twist + 1
    while gcd(stride, count) != 1:
        stride += 2
    start = (
        twist * 1315423911 + ell * 2654435761 + m * 97531
    ) % count
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
    limit: int = MAX_TWISTED_POOL,
) -> list[dict[str, Any]]:
    """Round-robin immutable q strata and guarantee at least one row per q."""

    twists = allowed_twists(
        ell,
        m,
        contract=TWISTED_TORUS_GEOMETRY_CONTRACT,
    )
    limit = min(MAX_TWISTED_POOL, max(0, int(limit)))
    if limit < len(twists):
        raise ValueError(
            f"candidate limit {limit} cannot cover {len(twists)} twists"
        )
    per_twist_target = (limit + len(twists) - 1) // len(twists)
    # Canonicalizing one support under q-aware translations is intentionally
    # more expensive than rectangular tuple hashing.  Inspect enough raw rows
    # to absorb duplicates without multiplying a 1200-row vocabulary by all
    # ninety q strata of the widest contracted shape.
    proposal_budget = min(
        MAX_RAW_SUPPORT_PROPOSALS,
        max(24, 8 * per_twist_target),
    )
    all_proposals = list(proposals)[:MAX_RAW_SUPPORT_PROPOSALS]
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
    empty = [twist for twist, rows in lanes.items() if not rows]
    if empty:
        raise RuntimeError(f"no legal support survived for twists {empty}")

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
        raise RuntimeError(
            "immutable twist quota failed: "
            f"observed={sorted(observed)}, expected={list(twists)}"
        )
    return output


def _default_twisted_pool_limit(m: int) -> int:
    """Scale work with q coverage instead of spending 300 rows on every shape."""

    return min(
        MAX_TWISTED_POOL,
        max(MIN_TWISTED_POOL, MIN_CANDIDATES_PER_TWIST * int(m)),
    )


# EVOLVE-BLOCK-START
def _generate_support_proposals(ell: int, m: int):
    """Propose sparse local/algebraic supports; outer geometry is immutable."""

    from math import gcd, lcm

    points = [
        (x, y)
        for x in range(ell)
        for y in range(m)
        if (x, y) != (0, 0)
    ]
    # Prefer directions with long order, then interleave axis and mixed
    # directions.  This is a self-contained initial vocabulary: changing a
    # different campaign seed cannot alter this campaign's checkpoint input.
    points.sort(key=lambda point: (
        -lcm(
            ell // gcd(ell, point[0]),
            m // gcd(m, point[1]),
        ),
        (point[0] == 0) + (point[1] == 0),
        point,
    ))
    proposals = []
    count = len(points)
    strides = (1, 3, 5, 7, 11, 13, 17)
    for index, u in enumerate(points):
        for stride in strides:
            v = points[(index + stride) % count]
            w = points[(index + 2 * stride + 1) % count]
            z = points[(index + 3 * stride + 2) % count]
            anchor = points[(index * 5 + stride) % count]
            if len({(0, 0), u, v, w, z, anchor}) < 5:
                continue
            # All six challenge-legal support splits occur before truncation.
            proposals.extend([
                ([(0, 0), u], [anchor, v]),
                ([(0, 0), u], [anchor, v, w]),
                ([(0, 0), u, v], [anchor, w]),
                ([(0, 0), u], [anchor, v, w, z]),
                ([(0, 0), u, v, w], [anchor, z]),
                ([(0, 0), u, v], [anchor, w, z]),
            ])
            if len(proposals) >= 1200:
                return proposals
    return proposals
# EVOLVE-BLOCK-END


def generate_candidates(ell: int, m: int) -> list[dict[str, Any]]:
    """Return a bounded geometry-aware pool covering every q at least thrice."""

    proposals = _generate_support_proposals(ell, m)
    if not isinstance(proposals, (list, tuple)):
        proposals = []
    return _expand_twist_quota(
        ell,
        m,
        proposals,
        limit=_default_twisted_pool_limit(m),
    )


__all__ = [
    "CHALLENGE_TERM_SPLITS",
    "MAX_TWISTED_POOL",
    "MIN_CANDIDATES_PER_TWIST",
    "MIN_TWISTED_POOL",
    "_canonical_candidate_key",
    "_default_twisted_pool_limit",
    "_expand_twist_quota",
    "generate_candidates",
]
