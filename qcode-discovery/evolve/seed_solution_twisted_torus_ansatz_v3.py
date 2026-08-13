"""Anchor-free full-support ansatz for published-volume twisted BB search.

The evolved block proposes complete ``A_terms`` and ``B_terms`` supports.
Unlike the preceding representation, the immutable wrapper never adds
``1+x``, ``1+y``, a third monomial, or a published construction.  It accepts
only the preregistered sparse splits and expands each proposal over the
immutable published-volume HNF geometry contract.

Published controls are intentionally absent from this module.  They may be
loaded only by the post-search blind-calibration verifier.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Mapping, Sequence
from math import gcd, lcm
from typing import Any

from evaluation.algebraic_mechanisms import classify_algebraic_mechanism
from evaluation.geometry import reduce_coordinate
from evaluation.search_contract import (
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    allowed_twists,
)


MAX_TWISTED_POOL = 420
MIN_TWISTED_POOL = 60
MIN_CANDIDATES_PER_TWIST = 3
MAX_RAW_SUPPORT_PROPOSALS = 4000
PREREGISTERED_SUPPORT_SPLITS = (
    (2, 4),
    (4, 2),
    (2, 3),
    (3, 2),
    (2, 2),
    (3, 3),
)


def _geometry_descriptor(twist: int) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": int(twist),
    }


def _normalise_support(
    terms: Sequence[Sequence[int]],
    ell: int,
    m: int,
    *,
    twist: int,
) -> tuple[tuple[int, int], ...]:
    geometry = _geometry_descriptor(twist)
    return tuple(sorted({
        reduce_coordinate(ell, m, int(x), int(y), geometry)
        for x, y in terms
    }))


def _canonical_candidate_key(
    a_terms: Sequence[Sequence[int]],
    b_terms: Sequence[Sequence[int]],
    ell: int,
    m: int,
    *,
    twist: int,
) -> tuple[tuple[tuple[int, int], ...], tuple[tuple[int, int], ...]]:
    """Canonicalize global translations and A/B exchange."""

    geometry = _geometry_descriptor(twist)
    support_a = _normalise_support(a_terms, ell, m, twist=twist)
    support_b = _normalise_support(b_terms, ell, m, twist=twist)
    origins = tuple(sorted(set(support_a).union(support_b)))
    if not origins:
        raise ValueError("candidate supports may not both be empty")
    variants = []
    for origin_x, origin_y in origins:
        shifted_a = tuple(sorted(
            reduce_coordinate(
                ell,
                m,
                x - origin_x,
                y - origin_y,
                geometry,
            )
            for x, y in support_a
        ))
        shifted_b = tuple(sorted(
            reduce_coordinate(
                ell,
                m,
                x - origin_x,
                y - origin_y,
                geometry,
            )
            for x, y in support_b
        ))
        variants.append(
            (shifted_a, shifted_b)
            if shifted_a <= shifted_b
            else (shifted_b, shifted_a)
        )
    return min(variants)


def _strict_support(value: Any, *, label: str) -> tuple[tuple[int, int], ...]:
    if not isinstance(value, (list, tuple)):
        raise ValueError(f"{label} must be a list or tuple")
    terms = []
    for index, term in enumerate(value):
        if not isinstance(term, (list, tuple)) or len(term) != 2:
            raise ValueError(f"{label}[{index}] must be an exponent pair")
        if any(isinstance(item, bool) or not isinstance(item, int) for item in term):
            raise ValueError(f"{label}[{index}] exponents must be integers")
        terms.append((int(term[0]), int(term[1])))
    return tuple(terms)


def _proposal_supports(
    proposal: Any,
) -> tuple[tuple[tuple[int, int], ...], tuple[tuple[int, int], ...]]:
    if isinstance(proposal, Mapping):
        if set(proposal) != {"A_terms", "B_terms"}:
            raise ValueError("support proposal has unknown fields")
        raw_a, raw_b = proposal["A_terms"], proposal["B_terms"]
    elif isinstance(proposal, (list, tuple)) and len(proposal) == 2:
        raw_a, raw_b = proposal
    else:
        raise ValueError("proposal must contain complete A/B supports")
    support_a = _strict_support(raw_a, label="A_terms")
    support_b = _strict_support(raw_b, label="B_terms")
    if (len(support_a), len(support_b)) not in PREREGISTERED_SUPPORT_SPLITS:
        raise ValueError("proposal support split is outside the preregistration")
    if len(support_a) + len(support_b) > 6:
        raise ValueError("combined support exceeds the sparse challenge bound")
    return support_a, support_b


def _records_for_twist(
    ell: int,
    m: int,
    twist: int,
    proposals: Sequence[Any],
) -> list[dict[str, Any]]:
    """Validate full supports and interleave their genuine split classes."""

    by_split: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    seen = set()
    geometry = _geometry_descriptor(twist)
    for proposal in proposals:
        try:
            raw_a, raw_b = _proposal_supports(proposal)
            support_a = _normalise_support(raw_a, ell, m, twist=twist)
            support_b = _normalise_support(raw_b, ell, m, twist=twist)
        except (TypeError, ValueError):
            continue
        split = (len(support_a), len(support_b))
        if (
            split not in PREREGISTERED_SUPPORT_SPLITS
            or len(support_a) + len(support_b) > 6
            or support_a == support_b
        ):
            continue
        key = _canonical_candidate_key(
            support_a,
            support_b,
            ell,
            m,
            twist=twist,
        )
        if key in seen:
            continue
        seen.add(key)
        mechanism = classify_algebraic_mechanism(
            support_a,
            support_b,
            ell=ell,
            m=m,
            geometry=geometry,
        )
        by_split[split].append({
            "A_terms": [tuple(term) for term in support_a],
            "B_terms": [tuple(term) for term in support_b],
            "geometry": geometry,
            "relation_type": mechanism["relation_type"],
            "support_split_type": mechanism["support_split_type"],
            "search_representation_id": (
                PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
            ),
        })

    output: list[dict[str, Any]] = []
    rotation = int(twist) % len(PREREGISTERED_SUPPORT_SPLITS)
    split_order = (
        PREREGISTERED_SUPPORT_SPLITS[rotation:]
        + PREREGISTERED_SUPPORT_SPLITS[:rotation]
    )
    positions = {split: 0 for split in split_order}
    while True:
        progressed = False
        for split in split_order:
            position = positions[split]
            rows = by_split.get(split, ())
            if position >= len(rows):
                continue
            output.append(rows[position])
            positions[split] += 1
            progressed = True
        if not progressed:
            break
    return output


def _staggered_proposals(
    proposals: Sequence[Any],
    *,
    ell: int,
    m: int,
    twist: int,
    sample_size: int,
) -> list[Any]:
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
    proposals: Sequence[Any],
    *,
    limit: int,
) -> list[dict[str, Any]]:
    twists = allowed_twists(
        ell,
        m,
        contract=PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    limit = min(MAX_TWISTED_POOL, max(0, int(limit)))
    minimum = MIN_CANDIDATES_PER_TWIST * len(twists)
    if limit < minimum:
        raise ValueError(
            f"candidate limit {limit} cannot cover {len(twists)} q strata"
        )
    per_twist_target = (limit + len(twists) - 1) // len(twists)
    proposal_budget = min(
        MAX_RAW_SUPPORT_PROPOSALS,
        max(48, 10 * per_twist_target),
    )
    bounded = list(proposals)[:MAX_RAW_SUPPORT_PROPOSALS]
    lanes = {
        twist: _records_for_twist(
            ell,
            m,
            twist,
            _staggered_proposals(
                bounded,
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
            "full-support proposal failed immutable q coverage: "
            f"{insufficient}"
        )

    positions = {twist: 0 for twist in twists}
    output: list[dict[str, Any]] = []
    while len(output) < limit:
        progressed = False
        for twist in twists:
            position = positions[twist]
            if position >= len(lanes[twist]):
                continue
            output.append(lanes[twist][position])
            positions[twist] += 1
            progressed = True
            if len(output) >= limit:
                break
        if not progressed:
            break
    if {int(row["geometry"]["twist"]) for row in output} != set(twists):
        raise RuntimeError("full-support wrapper lost a contracted q stratum")
    return output


def _default_pool_limit(ell: int, m: int) -> int:
    if (int(ell), int(m)) == (1, 127):
        return MIN_TWISTED_POOL
    twists = allowed_twists(
        int(ell),
        int(m),
        contract=PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    return min(
        MAX_TWISTED_POOL,
        max(MIN_TWISTED_POOL, MIN_CANDIDATES_PER_TWIST * len(twists)),
    )


# EVOLVE-BLOCK-START
def _generate_support_proposals(ell: int, m: int):
    """Propose complete sparse supports without privileged monomials."""

    x_radius = max(1, min(ell, 8))
    y_radius = max(2, min(m, 16))
    points = [
        (x, y)
        for x in range(-x_radius, x_radius + 1)
        for y in range(-y_radius, y_radius + 1)
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
    for step in range(220):
        for split_index, (a_count, b_count) in enumerate(
            PREREGISTERED_SUPPORT_SPLITS
        ):
            a_stride = (2 * split_index + 1) % count or 1
            b_stride = (2 * split_index + 5) % count or 1
            a_start = (step * 17 + split_index * 13) % count
            b_start = (step * 29 + split_index * 19 + 1) % count
            support_a = tuple(
                points[(a_start + index * a_stride) % count]
                for index in range(a_count)
            )
            support_b = tuple(
                points[(b_start + index * b_stride) % count]
                for index in range(b_count)
            )
            if len(set(support_a)) != a_count or len(set(support_b)) != b_count:
                continue
            proposals.append({
                "A_terms": support_a,
                "B_terms": support_b,
            })
            if len(proposals) >= 1200:
                return proposals
    return proposals
# EVOLVE-BLOCK-END


def generate_candidates(ell: int, m: int) -> list[dict[str, Any]]:
    proposals = _generate_support_proposals(ell, m)
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
    "PREREGISTERED_SUPPORT_SPLITS",
    "_canonical_candidate_key",
    "_default_pool_limit",
    "_expand_twist_quota",
    "_generate_support_proposals",
    "_normalise_support",
    "generate_candidates",
]
