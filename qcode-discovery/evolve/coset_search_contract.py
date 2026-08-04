"""Immutable Stage-1 contract for coset two-block action search.

The mutable OpenEvolve program chooses only an ``action_id`` and sparse
left/right support element IDs.  It cannot define permutation matrices,
override subgroup metadata, or attach distance claims.  Those objects come
from the source-bound action catalog in :mod:`evaluation.coset_action_catalog`.

This representation is intentionally checkpoint-incompatible with every BB
``(ell, m, q)`` representation.  In particular, an action element ID is not a
polynomial exponent and must never be passed to the BB builder.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import Any


COSET_CANDIDATE_SCHEMA_VERSION = 1
COSET_REPRESENTATION_ID = "css-coset-two-block-actions-v1"
COSET_EVALUATOR_KIND = "coset-two-block"
COSET_MAP_SCHEMA_VERSION = 1

COSET_ACTION_FAMILY_METRIC = "coset_action_family"
COSET_SUBGROUP_NORMALITY_METRIC = "coset_subgroup_normality"
COSET_SUPPORT_ORBIT_METRIC = "coset_support_orbit"
COSET_MAP_SCHEMA_METRIC = "coset_map_schema_version"

COSET_FEATURE_DIMENSIONS = (
    COSET_ACTION_FAMILY_METRIC,
    COSET_SUBGROUP_NORMALITY_METRIC,
    COSET_SUPPORT_ORBIT_METRIC,
)
COSET_FEATURE_BINS = {
    COSET_ACTION_FAMILY_METRIC: 4,
    COSET_SUBGROUP_NORMALITY_METRIC: 2,
    COSET_SUPPORT_ORBIT_METRIC: 8,
}

MAX_TOTAL_SUPPORT_WEIGHT = 6
PRODUCTION_LEFT_WEIGHT = 3
PRODUCTION_RIGHT_WEIGHT = 3
MAX_GENERATED_CANDIDATES = 384
DEFAULT_PER_ACTION_QUOTA = 96
LOW_WEIGHT_ORACLE_THRESHOLD = 4
TARGET_FOM = 12.0
ACTION_FAMILY_BINS = {
    "nonnormal-coset": 0,
    "normal-regular": 1,
}


@dataclass(frozen=True)
class ActionSearchView:
    """Search-only view of one immutable catalog action."""

    action_id: str
    block_size: int
    subgroup_normal: bool
    action_family_bin: int
    left_element_ids: tuple[str, ...]
    right_element_ids: tuple[str, ...]
    left_identity_id: str
    right_identity_id: str
    published_left_support: tuple[str, ...] | None = None
    published_right_support: tuple[str, ...] | None = None


def canonical_json_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _strict_string_tuple(value: Any, *, label: str) -> tuple[str, ...]:
    if (
        not isinstance(value, (list, tuple))
        or not value
        or any(not isinstance(item, str) or not item for item in value)
    ):
        raise ValueError(f"{label} must be a nonempty sequence of strings")
    result = tuple(value)
    if len(set(result)) != len(result):
        raise ValueError(f"{label} contains duplicate element IDs")
    return result


def _optional_support(value: Any, *, label: str) -> tuple[str, ...] | None:
    if value is None:
        return None
    return _strict_string_tuple(value, label=label)


def normalize_action_descriptor(raw: Mapping[str, Any]) -> ActionSearchView:
    """Validate the stable search fields exported by the action catalog."""

    if not isinstance(raw, Mapping):
        raise ValueError("action descriptor must be a mapping")
    action_id = raw.get("action_id")
    block_size = raw.get("block_size")
    subgroup_normal = raw.get("subgroup_normal")
    family_bin = raw.get("action_family_bin")
    if family_bin is None:
        bin_name = raw.get("bin")
        try:
            family_bin = ACTION_FAMILY_BINS[bin_name]
        except (KeyError, TypeError) as exc:
            raise ValueError(
                f"action {action_id} has no recognized fixed family bin"
            ) from exc
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("action descriptor has no action_id")
    if isinstance(block_size, bool) or not isinstance(block_size, int) or block_size < 2:
        raise ValueError(f"action {action_id} has invalid block_size")
    if not isinstance(subgroup_normal, bool):
        raise ValueError(f"action {action_id} has invalid subgroup_normal")
    if (
        isinstance(family_bin, bool)
        or not isinstance(family_bin, int)
        or not 0 <= family_bin < COSET_FEATURE_BINS[COSET_ACTION_FAMILY_METRIC]
    ):
        raise ValueError(f"action {action_id} has invalid action_family_bin")
    left_ids = _strict_string_tuple(
        raw.get("left_element_ids"),
        label=f"action {action_id} left_element_ids",
    )
    right_ids = _strict_string_tuple(
        raw.get("right_element_ids"),
        label=f"action {action_id} right_element_ids",
    )
    left_identity = raw.get("left_identity_id")
    right_identity = raw.get("right_identity_id")
    if left_identity not in left_ids:
        raise ValueError(f"action {action_id} left identity is not allowed")
    if right_identity not in right_ids:
        raise ValueError(f"action {action_id} right identity is not allowed")
    published = raw.get("published_support")
    if published is not None and not isinstance(published, Mapping):
        raise ValueError(f"action {action_id} published_support is invalid")
    published_left_raw = raw.get("published_left_support")
    published_right_raw = raw.get("published_right_support")
    if isinstance(published, Mapping):
        if published_left_raw is None:
            published_left_raw = published.get("left_support")
        if published_right_raw is None:
            published_right_raw = published.get("right_support")
    published_left = _optional_support(
        published_left_raw,
        label=f"action {action_id} published left support",
    )
    published_right = _optional_support(
        published_right_raw,
        label=f"action {action_id} published right support",
    )
    if published_left is not None and not set(published_left) <= set(left_ids):
        raise ValueError(f"action {action_id} published left support is unknown")
    if published_right is not None and not set(published_right) <= set(right_ids):
        raise ValueError(f"action {action_id} published right support is unknown")
    return ActionSearchView(
        action_id=action_id,
        block_size=block_size,
        subgroup_normal=subgroup_normal,
        action_family_bin=family_bin,
        left_element_ids=left_ids,
        right_element_ids=right_ids,
        left_identity_id=left_identity,
        right_identity_id=right_identity,
        published_left_support=published_left,
        published_right_support=published_right,
    )


def _catalog_descriptors() -> Iterable[Mapping[str, Any]]:
    """Read descriptors without guessing closure indices or GAP ordering."""

    from evaluation import coset_action_catalog as catalog

    provider = getattr(catalog, "list_action_descriptors", None)
    if not callable(provider):
        provider = getattr(catalog, "coset_action_descriptors", None)
    if not callable(provider):
        raise RuntimeError(
            "coset action catalog does not expose list_action_descriptors()"
        )
    raw = provider()
    if not isinstance(raw, (list, tuple)) or not raw:
        raise RuntimeError("coset action catalog is empty")
    return raw


def action_search_views() -> tuple[ActionSearchView, ...]:
    enabled = []
    for raw in _catalog_descriptors():
        search_enabled = raw.get("search_enabled", True)
        if not isinstance(search_enabled, bool):
            raise RuntimeError("coset action search_enabled must be boolean")
        if search_enabled:
            enabled.append(raw)
    if not enabled:
        raise RuntimeError("coset action catalog has no search-enabled action")
    views = tuple(normalize_action_descriptor(raw) for raw in enabled)
    ids = [view.action_id for view in views]
    if len(set(ids)) != len(ids):
        raise RuntimeError("coset action catalog contains duplicate action_id")
    return tuple(sorted(views, key=lambda view: view.action_id))


def action_search_view(action_id: str) -> ActionSearchView:
    matches = [view for view in action_search_views() if view.action_id == action_id]
    if len(matches) != 1:
        raise ValueError(f"unknown coset action_id: {action_id!r}")
    return matches[0]


def normalize_candidate(
    raw: Mapping[str, Any],
    *,
    require_production_split: bool = True,
) -> dict[str, Any]:
    """Return a strict candidate containing only catalog-bound search inputs."""

    if not isinstance(raw, Mapping):
        raise ValueError("coset candidate must be a mapping")
    allowed = {
        "schema_version",
        "representation_id",
        "action_id",
        "left_support",
        "right_support",
    }
    unknown = set(raw) - allowed
    if unknown:
        raise ValueError(f"coset candidate has unknown fields: {sorted(unknown)}")
    if raw.get("schema_version") != COSET_CANDIDATE_SCHEMA_VERSION:
        raise ValueError("coset candidate schema is incompatible")
    if raw.get("representation_id") != COSET_REPRESENTATION_ID:
        raise ValueError("coset candidate representation is incompatible")
    action_id = raw.get("action_id")
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("coset candidate action_id is invalid")
    view = action_search_view(action_id)
    left = _strict_string_tuple(raw.get("left_support"), label="left_support")
    right = _strict_string_tuple(raw.get("right_support"), label="right_support")
    if len(left) + len(right) > MAX_TOTAL_SUPPORT_WEIGHT:
        raise ValueError("total coset support weight exceeds six")
    if require_production_split and (
        len(left) != PRODUCTION_LEFT_WEIGHT
        or len(right) != PRODUCTION_RIGHT_WEIGHT
    ):
        raise ValueError("production coset search requires a 3+3 support split")
    if view.left_identity_id not in left or view.right_identity_id not in right:
        raise ValueError("coset supports must contain their fixed identities")
    if not set(left) <= set(view.left_element_ids):
        raise ValueError("left_support contains an element outside the action")
    if not set(right) <= set(view.right_element_ids):
        raise ValueError("right_support contains an element outside the action")
    normalized = {
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": view.action_id,
        # Catalog order is stable and semantically meaningful; sort by that
        # order rather than lexical aliases or GAP enumeration indices.
        "left_support": sorted(
            left, key={value: index for index, value in enumerate(view.left_element_ids)}.__getitem__,
        ),
        "right_support": sorted(
            right, key={value: index for index, value in enumerate(view.right_element_ids)}.__getitem__,
        ),
    }
    return normalized


def candidate_digest(candidate: Mapping[str, Any]) -> str:
    return canonical_json_sha256(normalize_candidate(candidate))


def support_orbit_bin(candidate: Mapping[str, Any]) -> int:
    normalized = normalize_candidate(candidate)
    digest = canonical_json_sha256({
        "left_support": normalized["left_support"],
        "right_support": normalized["right_support"],
    })
    return int(digest[:8], 16) % COSET_FEATURE_BINS[COSET_SUPPORT_ORBIT_METRIC]


def quota_by_normality(
    views: Sequence[ActionSearchView],
    total_limit: int,
) -> dict[str, int]:
    """Allocate deterministic action quotas without starving either H class."""

    if isinstance(total_limit, bool) or not isinstance(total_limit, int) or total_limit < 1:
        raise ValueError("total_limit must be a positive integer")
    if not views:
        raise ValueError("cannot allocate an empty action catalog")
    groups = {
        False: [view for view in views if not view.subgroup_normal],
        True: [view for view in views if view.subgroup_normal],
    }
    present = [normal for normal in (False, True) if groups[normal]]
    if len(present) == 2:
        # The nonnormal coset action is the production lane; the normal
        # regular action is a useful control but should not consume half of a
        # finite evaluation budget.  Preserve at least one control row whenever
        # the total budget can represent both classes.
        normal_budget = max(1, total_limit // 4) if total_limit > 1 else 0
        class_budget = {
            False: total_limit - normal_budget,
            True: normal_budget,
        }
    else:
        class_budget = {present[0]: total_limit}
    quotas = {view.action_id: 0 for view in views}
    for normal in present:
        members = sorted(groups[normal], key=lambda view: view.action_id)
        budget = class_budget[normal]
        for index in range(budget):
            quotas[members[index % len(members)].action_id] += 1
    return quotas


__all__ = [
    "ActionSearchView",
    "ACTION_FAMILY_BINS",
    "COSET_ACTION_FAMILY_METRIC",
    "COSET_CANDIDATE_SCHEMA_VERSION",
    "COSET_EVALUATOR_KIND",
    "COSET_FEATURE_BINS",
    "COSET_FEATURE_DIMENSIONS",
    "COSET_MAP_SCHEMA_METRIC",
    "COSET_MAP_SCHEMA_VERSION",
    "COSET_REPRESENTATION_ID",
    "COSET_SUBGROUP_NORMALITY_METRIC",
    "COSET_SUPPORT_ORBIT_METRIC",
    "DEFAULT_PER_ACTION_QUOTA",
    "LOW_WEIGHT_ORACLE_THRESHOLD",
    "MAX_GENERATED_CANDIDATES",
    "MAX_TOTAL_SUPPORT_WEIGHT",
    "PRODUCTION_LEFT_WEIGHT",
    "PRODUCTION_RIGHT_WEIGHT",
    "TARGET_FOM",
    "action_search_view",
    "action_search_views",
    "candidate_digest",
    "canonical_json_sha256",
    "normalize_action_descriptor",
    "normalize_candidate",
    "quota_by_normality",
    "support_orbit_bin",
]
