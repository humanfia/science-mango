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
from functools import lru_cache
from typing import Any


COSET_CANDIDATE_SCHEMA_VERSION = 2
COSET_REPRESENTATION_ID = "css-coset-two-block-actions-v2"
COSET_EVALUATOR_KIND = "coset-two-block"
COSET_MAP_SCHEMA_VERSION = 3

# Legacy candidate-level labels remain part of persisted candidate rows, but
# they are deliberately no longer MAP-Elites dimensions.  Selecting one
# highest-scoring candidate made the immutable published anchor describe every
# policy, hiding the rest of the rendered batch.
COSET_ACTION_FAMILY_METRIC = "coset_action_family"
COSET_SUBGROUP_NORMALITY_METRIC = "coset_subgroup_normality"
COSET_SUPPORT_ORBIT_METRIC = "coset_support_orbit"
COSET_MAP_SCHEMA_METRIC = "coset_map_schema_version"

COSET_NONNORMAL_LANE_METRIC = "coset_nonnormal_lane_bucket"
COSET_NORMAL_LANE_METRIC = "coset_normal_lane_bucket"
COSET_BATCH_ORBIT_PROFILE_METRIC = "coset_batch_orbit_profile_bucket"

COSET_FEATURE_DIMENSIONS = (
    COSET_NONNORMAL_LANE_METRIC,
    COSET_NORMAL_LANE_METRIC,
    COSET_BATCH_ORBIT_PROFILE_METRIC,
)
COSET_FEATURE_BINS = {
    COSET_NONNORMAL_LANE_METRIC: 16,
    COSET_NORMAL_LANE_METRIC: 16,
    COSET_BATCH_ORBIT_PROFILE_METRIC: 8,
}

COSET_SUPPORT_ORBIT_BINS = 8
COSET_DESCRIPTOR_KIND = "qcode-coset-batch-map-descriptor-v3"

MAX_TOTAL_SUPPORT_WEIGHT = 6
PRODUCTION_LEFT_WEIGHT = 3
PRODUCTION_RIGHT_WEIGHT = 3
MAX_GENERATED_CANDIDATES = 384
DEFAULT_PER_ACTION_QUOTA = 96
TARGET_FOM = 12.0

# Stage-1 proof search is a resumable sequence of threshold decisions, not a
# one-shot distance estimate.  Schema v2 replaces the historical fixed
# ``max_weight=4`` probe.  A bounded, normality-balanced frontier may advance
# multiple sequential rungs in one evaluator call; committed evidence is
# hydrated from the source-bound run ledger before new work is attempted.
COSET_PROOF_LADDER_SCHEMA_VERSION = 2
COSET_PROOF_LADDER_VERSION_METRIC = "qcode_coset_proof_ladder_version"
COSET_PROOF_LADDER_CONFIG_KEY = "qcode_coset_stage1_proof_ladder"
COSET_PROOF_LADDER_START_WEIGHT = 4
COSET_PROOF_LADDER_WEIGHT_STEP = 2
COSET_PROOF_MAX_CANDIDATES_PER_BATCH = 8
COSET_PROOF_MAX_NEW_STEPS_PER_BATCH = 24
COSET_PROOF_BATCH_WALL_TIMEOUT_S = 720.0
COSET_PROOF_STEP_HARD_TIMEOUT_S = 30.0
COSET_PROOF_CACHE_DIRECTORY = ".coset-stage1-proof-cache-v2"
ACTION_FAMILY_BINS = {
    "nonnormal-coset": 0,
    "normal-regular": 1,
}


def proof_ladder_config_contract() -> dict[str, Any]:
    """Return the exact fail-closed YAML marker for this scoring contract."""

    return {
        "enabled": True,
        "schema_version": COSET_PROOF_LADDER_SCHEMA_VERSION,
        "start_weight": COSET_PROOF_LADDER_START_WEIGHT,
        "weight_step": COSET_PROOF_LADDER_WEIGHT_STEP,
        "max_candidates_per_batch": COSET_PROOF_MAX_CANDIDATES_PER_BATCH,
        "max_new_steps_per_batch": COSET_PROOF_MAX_NEW_STEPS_PER_BATCH,
        "batch_wall_timeout_s": COSET_PROOF_BATCH_WALL_TIMEOUT_S,
        "step_hard_timeout_s": COSET_PROOF_STEP_HARD_TIMEOUT_S,
        "cache_directory": COSET_PROOF_CACHE_DIRECTORY,
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
        or not 0 <= family_bin < len(ACTION_FAMILY_BINS)
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
    raw = provider(catalog_id=catalog.V2_CATALOG_ID)
    if not isinstance(raw, (list, tuple)) or not raw:
        raise RuntimeError("coset action catalog is empty")
    return raw


@lru_cache(maxsize=1)
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
    return int(digest[:8], 16) % COSET_SUPPORT_ORBIT_BINS


def _require_sha256(value: Any, *, label: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{label} must be a lowercase SHA-256 digest")
    return value


def _action_catalog_identity() -> dict[str, Any]:
    from evaluation.coset_action_catalog import (
        V2_CATALOG_ID,
        action_catalog_identity,
    )

    identity = action_catalog_identity(V2_CATALOG_ID)
    if (
        identity.get("catalog_id") != V2_CATALOG_ID
        or identity.get("schema_version") != 2
    ):
        raise ValueError("coset action catalog v2 identity changed")
    return {
        "catalog_id": V2_CATALOG_ID,
        "sha256": _require_sha256(
            identity.get("sha256"),
            label="coset action catalog identity",
        ),
    }


def _action_catalog_sha256() -> str:
    return str(_action_catalog_identity()["sha256"])


def coset_batch_map_descriptor(
    candidates: Sequence[Mapping[str, Any]],
    *,
    policy_sha256: str,
) -> dict[str, Any]:
    """Build the stable schema-v3 MAP descriptor for one rendered policy.

    Coordinates depend only on the typed policy identity and the immutable
    renderer output.  In particular, no static-code build, oracle outcome,
    timeout, fitness, or worker completion order can move a policy between
    cells.  Full lane candidate identities are retained in the artifact so a
    coordinate can be independently replayed instead of trusting its bucket.
    """

    policy_sha256 = _require_sha256(policy_sha256, label="policy_sha256")
    if not isinstance(candidates, Sequence) or isinstance(
        candidates, (str, bytes, bytearray)
    ):
        raise TypeError("descriptor candidates must be a sequence")
    if len(candidates) != MAX_GENERATED_CANDIDATES:
        raise ValueError(
            "descriptor requires the exact production candidate batch"
        )

    views = action_search_views()
    if {view.subgroup_normal for view in views} != {False, True}:
        raise RuntimeError("descriptor v3 requires both normality classes")
    expected_quotas = quota_by_normality(views, MAX_GENERATED_CANDIDATES)
    lanes: dict[str, list[dict[str, Any]]] = {
        view.action_id: [] for view in views
    }
    observed_digests: set[str] = set()
    ordered_digests: list[str] = []
    for index, raw in enumerate(candidates):
        try:
            normalized = normalize_candidate(raw)
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                f"descriptor candidate {index} is invalid"
            ) from exc
        if raw != normalized:
            raise ValueError(
                f"descriptor candidate {index} is not canonical"
            )
        action_id = normalized["action_id"]
        if action_id not in lanes:
            raise ValueError("descriptor candidate uses an unknown action")
        digest = candidate_digest(normalized)
        if digest in observed_digests:
            raise ValueError("descriptor candidate batch contains duplicates")
        observed_digests.add(digest)
        ordered_digests.append(digest)
        lanes[action_id].append(normalized)
    if {
        action_id: len(rows) for action_id, rows in lanes.items()
    } != expected_quotas:
        raise ValueError("descriptor candidate batch violates action quotas")

    catalog_identity = _action_catalog_identity()
    catalog_id = str(catalog_identity["catalog_id"])
    catalog_sha256 = str(catalog_identity["sha256"])
    lane_artifacts: list[dict[str, Any]] = []
    coordinates: dict[str, int] = {}
    aggregate_histogram = [0] * COSET_SUPPORT_ORBIT_BINS
    ordered_views = sorted(views, key=lambda item: item.action_id)
    for lane_index, view in enumerate(ordered_views):
        rows = lanes[view.action_id]
        candidate_sha256 = [candidate_digest(row) for row in rows]
        orbit_histogram = [0] * COSET_SUPPORT_ORBIT_BINS
        for row in rows:
            orbit = support_orbit_bin(row)
            orbit_histogram[orbit] += 1
            aggregate_histogram[orbit] += 1
        lane_payload = {
            "schema_version": COSET_MAP_SCHEMA_VERSION,
            "representation_id": COSET_REPRESENTATION_ID,
            "action_catalog_id": catalog_id,
            "action_catalog_sha256": catalog_sha256,
            "action_lane_index": lane_index,
            "action_family_bin": view.action_family_bin,
            "action_id": view.action_id,
            "subgroup_normal": view.subgroup_normal,
            "quota": expected_quotas[view.action_id],
            "candidate_sha256": candidate_sha256,
        }
        lane_sha256 = canonical_json_sha256(lane_payload)
        metric = (
            COSET_NORMAL_LANE_METRIC
            if view.subgroup_normal
            else COSET_NONNORMAL_LANE_METRIC
        )
        lane_artifacts.append({
            **lane_payload,
            "candidate_count": len(rows),
            "orbit_histogram": orbit_histogram,
            "lane_sha256": lane_sha256,
            "class_metric": metric,
        })

    # Forty-five nonnormal action lanes share one MAP dimension.  Hash the
    # complete ordered lane identity/quota list for each class before deriving
    # its coordinate; assigning a bucket per action would silently overwrite
    # the previous 44 coordinates and make most of the rendered batch invisible.
    class_artifacts: list[dict[str, Any]] = []
    for subgroup_normal, metric in (
        (False, COSET_NONNORMAL_LANE_METRIC),
        (True, COSET_NORMAL_LANE_METRIC),
    ):
        class_lanes = [
            lane
            for lane in lane_artifacts
            if lane["subgroup_normal"] is subgroup_normal
        ]
        if not class_lanes:
            raise RuntimeError(
                f"descriptor v3 has no {subgroup_normal=} action lane"
            )
        class_payload = {
            "schema_version": COSET_MAP_SCHEMA_VERSION,
            "representation_id": COSET_REPRESENTATION_ID,
            "action_catalog_id": catalog_id,
            "action_catalog_sha256": catalog_sha256,
            "subgroup_normal": subgroup_normal,
            "metric": metric,
            "lanes": [
                {
                    "action_lane_index": lane["action_lane_index"],
                    "action_family_bin": lane["action_family_bin"],
                    "action_id": lane["action_id"],
                    "quota": lane["quota"],
                    "lane_sha256": lane["lane_sha256"],
                }
                for lane in class_lanes
            ],
        }
        class_sha256 = canonical_json_sha256(class_payload)
        bucket = int(class_sha256[:16], 16) % COSET_FEATURE_BINS[metric]
        coordinates[metric] = bucket
        class_artifacts.append({
            **class_payload,
            "action_count": len(class_lanes),
            "candidate_count": sum(
                int(lane["candidate_count"]) for lane in class_lanes
            ),
            "class_sha256": class_sha256,
            "bucket": bucket,
        })

    batch_payload = {
        "schema_version": COSET_MAP_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_catalog_id": catalog_id,
        "action_catalog_sha256": catalog_sha256,
        "policy_sha256": policy_sha256,
        "ordered_candidate_sha256": ordered_digests,
    }
    batch_sha256 = canonical_json_sha256(batch_payload)
    orbit_profile_payload = {
        "schema_version": COSET_MAP_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_catalog_id": catalog_id,
        "action_catalog_sha256": catalog_sha256,
        "aggregate_orbit_histogram": aggregate_histogram,
        "lanes": [
            {
                "action_id": lane["action_id"],
                "action_lane_index": lane["action_lane_index"],
                "quota": lane["quota"],
                "candidate_count": lane["candidate_count"],
                "orbit_histogram": lane["orbit_histogram"],
                "lane_sha256": lane["lane_sha256"],
            }
            for lane in lane_artifacts
        ],
    }
    orbit_profile_sha256 = canonical_json_sha256(orbit_profile_payload)
    orbit_bucket = (
        int(orbit_profile_sha256[:16], 16)
        % COSET_FEATURE_BINS[COSET_BATCH_ORBIT_PROFILE_METRIC]
    )
    coordinates[COSET_BATCH_ORBIT_PROFILE_METRIC] = orbit_bucket
    if set(coordinates) != set(COSET_FEATURE_DIMENSIONS):
        raise RuntimeError("descriptor v2 did not populate every coordinate")

    artifact = {
        "kind": COSET_DESCRIPTOR_KIND,
        "schema_version": COSET_MAP_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_catalog_id": catalog_id,
        "action_catalog_sha256": catalog_sha256,
        "policy_sha256": policy_sha256,
        "dimensions": list(COSET_FEATURE_DIMENSIONS),
        "bins": dict(COSET_FEATURE_BINS),
        "coordinates": {
            name: coordinates[name] for name in COSET_FEATURE_DIMENSIONS
        },
        "lanes": lane_artifacts,
        "classes": class_artifacts,
        "batch": {
            **batch_payload,
            "candidate_count": len(candidates),
            "batch_sha256": batch_sha256,
            "aggregate_orbit_histogram": aggregate_histogram,
            "orbit_profile_sha256": orbit_profile_sha256,
            "orbit_profile_bucket": orbit_bucket,
        },
    }
    artifact["descriptor_sha256"] = canonical_json_sha256(artifact)
    return artifact


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
        # Preserve the historical 288/96 split for the exact two-action
        # catalog.  Expanded catalogs instead allocate by class cardinality,
        # while retaining at least one normal control in a finite oracle batch.
        if len(views) == 2 and all(len(groups[normal]) == 1 for normal in present):
            normal_budget = max(1, total_limit // 4) if total_limit > 1 else 0
        else:
            normal_budget = (
                max(1, round(total_limit * len(groups[True]) / len(views)))
                if total_limit > 1
                else 0
            )
            normal_budget = min(normal_budget, total_limit - 1)
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
    "COSET_BATCH_ORBIT_PROFILE_METRIC",
    "COSET_CANDIDATE_SCHEMA_VERSION",
    "COSET_EVALUATOR_KIND",
    "COSET_FEATURE_BINS",
    "COSET_FEATURE_DIMENSIONS",
    "COSET_MAP_SCHEMA_METRIC",
    "COSET_MAP_SCHEMA_VERSION",
    "COSET_NONNORMAL_LANE_METRIC",
    "COSET_NORMAL_LANE_METRIC",
    "COSET_REPRESENTATION_ID",
    "COSET_SUBGROUP_NORMALITY_METRIC",
    "COSET_SUPPORT_ORBIT_METRIC",
    "COSET_SUPPORT_ORBIT_BINS",
    "DEFAULT_PER_ACTION_QUOTA",
    "COSET_PROOF_BATCH_WALL_TIMEOUT_S",
    "COSET_PROOF_CACHE_DIRECTORY",
    "COSET_PROOF_LADDER_CONFIG_KEY",
    "COSET_PROOF_LADDER_SCHEMA_VERSION",
    "COSET_PROOF_LADDER_VERSION_METRIC",
    "COSET_PROOF_LADDER_START_WEIGHT",
    "COSET_PROOF_LADDER_WEIGHT_STEP",
    "COSET_PROOF_MAX_CANDIDATES_PER_BATCH",
    "COSET_PROOF_MAX_NEW_STEPS_PER_BATCH",
    "COSET_PROOF_STEP_HARD_TIMEOUT_S",
    "MAX_GENERATED_CANDIDATES",
    "MAX_TOTAL_SUPPORT_WEIGHT",
    "PRODUCTION_LEFT_WEIGHT",
    "PRODUCTION_RIGHT_WEIGHT",
    "TARGET_FOM",
    "action_search_view",
    "action_search_views",
    "candidate_digest",
    "canonical_json_sha256",
    "coset_batch_map_descriptor",
    "normalize_action_descriptor",
    "normalize_candidate",
    "quota_by_normality",
    "proof_ladder_config_contract",
    "support_orbit_bin",
]
