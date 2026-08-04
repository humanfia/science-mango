"""Immutable-wrapper seed for coset two-block Stage-1 search.

OpenEvolve may change only :func:`_propose_coset_supports`.  The wrapper owns
the catalog, action quotas, identity anchors, 3+3 weight contract, canonical
IDs, and output cap.  No evolved program is allowed to provide permutation
matrices or mathematical evidence.
"""

from __future__ import annotations

import itertools
from collections.abc import Mapping
from math import gcd
from typing import Any

from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION,
    COSET_REPRESENTATION_ID,
    MAX_GENERATED_CANDIDATES,
    action_search_views,
    candidate_digest,
    canonical_json_sha256,
    normalize_candidate,
    quota_by_normality,
)


MAX_EVOLVED_PROPOSALS = 4096


def _candidate(
    action_id: str,
    left_support,
    right_support,
) -> dict[str, Any]:
    return {
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": action_id,
        "left_support": list(left_support),
        "right_support": list(right_support),
    }


# EVOLVE-BLOCK-START
def _propose_coset_supports():
    """Propose sparse supports; immutable code validates every returned row.

    The seed deliberately starts with the catalog's published alias when one
    exists, then adds asymmetric supports from early closure elements.  Evolved
    variants should diversify across ``action_id`` and conjugacy/orbit
    structure, not attach decoder scores or distance claims.
    """

    proposals = []
    for view in action_search_views():
        if (
            view.published_left_support is not None
            and view.published_right_support is not None
        ):
            proposals.append(_candidate(
                view.action_id,
                view.published_left_support,
                view.published_right_support,
            ))
        left = [
            element
            for element in view.left_element_ids
            if element != view.left_identity_id
        ]
        right = [
            element
            for element in view.right_element_ids
            if element != view.right_identity_id
        ]
        if len(left) >= 2 and len(right) >= 2:
            proposals.append(_candidate(
                view.action_id,
                (view.left_identity_id, left[0], left[-1]),
                (view.right_identity_id, right[0], right[-1]),
            ))
    return proposals
# EVOLVE-BLOCK-END


def _proposal_parts(raw: Any) -> tuple[str, Any, Any]:
    if not isinstance(raw, Mapping):
        raise ValueError("coset proposal must be a mapping")
    unknown = set(raw) - {"action_id", "left_support", "right_support"}
    # The immutable seed's own complete records are accepted too, but evolved
    # metadata and proof claims are not.
    unknown -= {"schema_version", "representation_id"}
    if unknown:
        raise ValueError(f"coset proposal controls forbidden fields: {sorted(unknown)}")
    return raw["action_id"], raw["left_support"], raw["right_support"]


def _normalized_proposal(raw: Any) -> dict[str, Any]:
    action_id, left, right = _proposal_parts(raw)
    return normalize_candidate(_candidate(action_id, left, right))


def _fallback_candidates(view, quota: int, *, proposal_salt: str):
    """Sample the Cartesian pair-of-pairs space without materializing it."""

    if quota <= 0:
        return []
    left_ids = [
        item for item in view.left_element_ids
        if item != view.left_identity_id
    ]
    right_ids = [
        item for item in view.right_element_ids
        if item != view.right_identity_id
    ]
    left_pairs = list(itertools.combinations(left_ids, 2))
    right_pairs = list(itertools.combinations(right_ids, 2))
    if not left_pairs or not right_pairs:
        return []
    pair_space = len(left_pairs) * len(right_pairs)
    limit = min(int(quota), pair_space)
    # A digest-derived odd stride makes aliases stable across processes while
    # avoiding the highly correlated first lexicographic rectangle.
    seed = int(canonical_json_sha256({
        "action_id": view.action_id,
        "proposal_salt": proposal_salt,
        "fallback_anchor": _candidate(
            view.action_id,
            (view.left_identity_id, *left_pairs[0]),
            (view.right_identity_id, *right_pairs[0]),
        ),
    })[:16], 16)
    stride = 2 * (seed % max(1, pair_space // 2)) + 1
    while gcd(stride, pair_space) != 1:
        stride += 2
    cursor = seed % pair_space
    rows = []
    for _ in range(limit):
        left_index, right_index = divmod(cursor, len(right_pairs))
        rows.append(normalize_candidate(_candidate(
            view.action_id,
            (view.left_identity_id, *left_pairs[left_index]),
            (view.right_identity_id, *right_pairs[right_index]),
        )))
        cursor = (cursor + stride) % pair_space
    return rows


def generate_candidates(limit: int = MAX_GENERATED_CANDIDATES):
    """Return a bounded, normality-balanced set of strict coset candidates."""

    if isinstance(limit, bool) or not isinstance(limit, int) or limit < 1:
        raise ValueError("coset candidate limit must be a positive integer")
    limit = min(limit, MAX_GENERATED_CANDIDATES)
    views = action_search_views()
    quotas = quota_by_normality(views, limit)
    proposed: dict[str, list[dict[str, Any]]] = {
        view.action_id: [] for view in views
    }
    seen: set[str] = set()
    raw_proposals = _propose_coset_supports()
    try:
        bounded_proposals = itertools.islice(
            iter(raw_proposals), MAX_EVOLVED_PROPOSALS
        )
    except TypeError as exc:
        raise ValueError("coset proposals must be iterable") from exc
    for raw in bounded_proposals:
        try:
            row = _normalized_proposal(raw)
        except (KeyError, TypeError, ValueError):
            continue
        action_id = row["action_id"]
        if action_id not in proposed or len(proposed[action_id]) >= quotas[action_id]:
            continue
        digest = candidate_digest(row)
        if digest in seen:
            continue
        seen.add(digest)
        proposed[action_id].append(row)

    # The evolved block normally proposes only a handful of structural
    # anchors, while the immutable wrapper fills a much larger quota.  Bind
    # the traversal to the complete accepted proposal set so a meaningful
    # support mutation changes most filler samples instead of re-evaluating
    # an action-only fixed pool in every program. Sorting digests makes the
    # salt canonical and independent of incidental proposal ordering.
    proposal_salt = canonical_json_sha256(sorted(seen))
    for view in views:
        missing = quotas[view.action_id] - len(proposed[view.action_id])
        if missing <= 0:
            continue
        # Generate more than the deficit because evolved proposals may overlap
        # the deterministic fallback prefix.
        fallback_limit = min(
            len(view.left_element_ids) ** 2 * len(view.right_element_ids) ** 2,
            missing + len(proposed[view.action_id]) + 32,
        )
        for row in _fallback_candidates(
            view,
            fallback_limit,
            proposal_salt=proposal_salt,
        ):
            if len(proposed[view.action_id]) >= quotas[view.action_id]:
                break
            digest = candidate_digest(row)
            if digest in seen:
                continue
            seen.add(digest)
            proposed[view.action_id].append(row)

    # Round-robin action IDs so truncation cannot erase a catalog stratum.
    output = []
    ordered_ids = [view.action_id for view in views]
    for offset in range(max(map(len, proposed.values()), default=0)):
        for action_id in ordered_ids:
            lane = proposed[action_id]
            if offset < len(lane):
                output.append(lane[offset])
                if len(output) == limit:
                    return output
    return output


if __name__ == "__main__":
    import json

    print(json.dumps(generate_candidates(), indent=2, sort_keys=True))
