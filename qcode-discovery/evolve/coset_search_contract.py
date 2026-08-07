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

# The v2 names above are frozen compatibility aliases.  Renderer v3 is a new
# checkpoint epoch: candidates carry their renderer identity and an explicit
# support split, while the old 3+3 representation continues to reject every
# such field.  Never change the v2 constants to point at this epoch.
COSET_CANDIDATE_SCHEMA_VERSION_V3 = 3
COSET_REPRESENTATION_ID_V3 = "css-coset-two-block-actions-v3"
COSET_MAP_SCHEMA_VERSION_V3 = 4
COSET_DESCRIPTOR_KIND_V3 = "qcode-coset-batch-map-descriptor-v4"
COSET_RENDERER_REGISTRY_SCHEMA_VERSION = 1
COSET_RENDERER_REGISTRY_KIND = "qcode-trusted-coset-renderer-registry-v1"
COSET_RENDERER_DESCRIPTOR_SCHEMA_VERSION = 1
COSET_CATALOG_MANIFEST_SCHEMA_VERSION = 1
COSET_CATALOG_REGISTRY_SCHEMA_VERSION = 1
COSET_CATALOG_REGISTRY_KIND = "qcode-trusted-coset-catalog-registry-v1"
COSET_RENDERER_PROPOSAL_SCHEMA_VERSION = 1
COSET_RENDERER_PROPOSAL_KIND = "qcode-coset-renderer-proposal-v1"
COSET_RENDERER_ACTIVATION_SCHEMA_VERSION = 1
COSET_RENDERER_ACTIVATION_KIND = "qcode-coset-renderer-activation-v1"
COSET_RENDERER_ACTIVATION_JSON_ENV = "QCODE_COSET_RENDERER_ACTIVATION_JSON"
COSET_RENDERER_V2_ID = "catalog-pair-walk-v2"
COSET_RENDERER_V3_ID = "catalog-combination-walk-v3"
COSET_ACTION_CATALOG_V2_MANIFEST_ID = "coset-action-catalog-v2-installed"
COSET_RENDERER_V2_CHECKPOINT_GROUP = (
    "coset-two-block-catalog-v2-dsl-map-v3-proof-ladder-v3"
)
COSET_RENDERER_V3_CHECKPOINT_GROUP = (
    "coset-two-block-catalog-v2-renderer-v3-map-v4-proof-ladder-v3"
)
TRUSTED_COSET_CATALOG_KINDS = ("action", "cover", "protograph")
TRUSTED_COSET_SUPPORT_SPLITS = (
    (2, 4),
    (4, 2),
    (2, 3),
    (3, 2),
    (3, 3),
)

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
COSET_SUPPORT_SPLIT_METRIC = "coset_support_split_bucket"

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
COSET_FEATURE_DIMENSIONS_V3 = (
    *COSET_FEATURE_DIMENSIONS,
    COSET_SUPPORT_SPLIT_METRIC,
)
COSET_FEATURE_BINS_V3 = {
    **COSET_FEATURE_BINS,
    COSET_SUPPORT_SPLIT_METRIC: len(TRUSTED_COSET_SUPPORT_SPLITS),
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
# one-shot distance estimate.  Schema v3 separates the strict scalar FOM goal
# from the broader challenge/Pareto gate and adds a run-global, advisory proof
# frontier.  The frontier never grants proof credit: every selected candidate
# is rebuilt and every cached SAT/UNSAT decision is replayed against the
# source-bound matrices before it can affect fitness or candidate state.
COSET_PROOF_LADDER_SCHEMA_VERSION = 3
COSET_PROOF_LADDER_VERSION_METRIC = "qcode_coset_proof_ladder_version"
COSET_PROOF_LADDER_CONFIG_KEY = "qcode_coset_stage1_proof_ladder"
COSET_PROOF_TARGET_MODE = "scalar-fom-strict-v1"
COSET_PROOF_LADDER_START_WEIGHT = 4
COSET_PROOF_LADDER_WEIGHT_STEP = 2
COSET_PROOF_MAX_CANDIDATES_PER_BATCH = 24
COSET_PROOF_MAX_NEW_STEPS_PER_BATCH = 24
COSET_PROOF_BATCH_WALL_TIMEOUT_S = 720.0
COSET_PROOF_RETRY_TIMEOUTS_S = (7.5, 15.0, 30.0, 120.0)
COSET_PROOF_STEP_HARD_TIMEOUT_S = max(COSET_PROOF_RETRY_TIMEOUTS_S)
COSET_PROOF_GLOBAL_FRONTIER_INJECTIONS = 4
COSET_PROOF_CACHE_DIRECTORY = ".coset-stage1-proof-cache-v3"
ACTION_FAMILY_BINS = {
    "nonnormal-coset": 0,
    "normal-regular": 1,
}


def proof_ladder_config_contract() -> dict[str, Any]:
    """Return the exact fail-closed YAML marker for this scoring contract."""

    return {
        "enabled": True,
        "schema_version": COSET_PROOF_LADDER_SCHEMA_VERSION,
        "target_mode": COSET_PROOF_TARGET_MODE,
        "start_weight": COSET_PROOF_LADDER_START_WEIGHT,
        "weight_step": COSET_PROOF_LADDER_WEIGHT_STEP,
        "max_candidates_per_batch": COSET_PROOF_MAX_CANDIDATES_PER_BATCH,
        "max_new_steps_per_batch": COSET_PROOF_MAX_NEW_STEPS_PER_BATCH,
        "batch_wall_timeout_s": COSET_PROOF_BATCH_WALL_TIMEOUT_S,
        "step_hard_timeout_s": COSET_PROOF_STEP_HARD_TIMEOUT_S,
        "retry_timeouts_s": list(COSET_PROOF_RETRY_TIMEOUTS_S),
        "global_frontier_injections": (
            COSET_PROOF_GLOBAL_FRONTIER_INJECTIONS
        ),
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


@dataclass(frozen=True, slots=True)
class TrustedCosetRendererDescriptor:
    """Source-owned renderer/catalog contract; it never stores a callable.

    Extending the search to another action, cover, or protograph catalog
    requires adding a reviewed descriptor and a corresponding explicit code
    branch.  A policy string can select only an ID already present here; it
    cannot provide a module, import path, template, or executable hook.
    """

    descriptor_id: str
    policy_schema_version: int
    candidate_schema_version: int
    representation_id: str
    catalog_kind: str
    catalog_id: str
    catalog_schema_version: int
    map_schema_version: int
    map_descriptor_kind: str
    checkpoint_compatibility_group: str
    support_splits: tuple[tuple[int, int], ...]
    feature_dimensions: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class TrustedCosetCatalogManifest:
    """One installed, source-owned catalog identity.

    ``handler_id`` is interpreted only by an explicit dispatcher branch.  It
    is never imported, evaluated, or called by name.  Installing a future
    cover/protograph therefore requires both a reviewed manifest here and a
    reviewed renderer branch; reviewer JSON alone cannot make code executable.
    """

    manifest_id: str
    catalog_kind: str
    catalog_id: str
    catalog_schema_version: int
    catalog_sha256: str
    handler_id: str


@dataclass(frozen=True, slots=True)
class TrustedCosetRendererActivation:
    """Validated proposal bound to installed registry bytes."""

    proposal_sha256: str
    renderer_descriptor_id: str
    renderer_descriptor_sha256: str
    renderer_registry_sha256: str
    catalog_manifest_id: str
    catalog_manifest_sha256: str
    catalog_registry_sha256: str
    catalog_handler_id: str
    approved_support_splits: tuple[tuple[int, int], ...]


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


def _strict_support_split(value: Any) -> tuple[int, int]:
    if (
        type(value) is not list
        or len(value) != 2
        or any(type(item) is not int for item in value)
    ):
        raise ValueError("coset support_split must be a two-integer JSON list")
    split = (value[0], value[1])
    if split not in TRUSTED_COSET_SUPPORT_SPLITS:
        raise ValueError("coset support_split is not renderer-whitelisted")
    return split


def normalize_candidate_v3(raw: Mapping[str, Any]) -> dict[str, Any]:
    """Validate one renderer-v3 action candidate as inert catalog data."""

    if not isinstance(raw, Mapping):
        raise ValueError("coset candidate must be a mapping")
    allowed = {
        "schema_version",
        "representation_id",
        "renderer_descriptor_id",
        "action_id",
        "support_split",
        "left_support",
        "right_support",
    }
    unknown = set(raw) - allowed
    missing = allowed - set(raw)
    if unknown or missing:
        raise ValueError(
            "coset v3 candidate fields are not exact; "
            f"missing={sorted(missing)}, unknown={sorted(unknown)}"
        )
    if raw.get("schema_version") != COSET_CANDIDATE_SCHEMA_VERSION_V3:
        raise ValueError("coset v3 candidate schema is incompatible")
    if raw.get("representation_id") != COSET_REPRESENTATION_ID_V3:
        raise ValueError("coset v3 candidate representation is incompatible")
    if raw.get("renderer_descriptor_id") != COSET_RENDERER_V3_ID:
        raise ValueError("coset v3 candidate renderer is incompatible")
    split = _strict_support_split(raw.get("support_split"))
    action_id = raw.get("action_id")
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("coset v3 candidate action_id is invalid")
    view = action_search_view(action_id)
    left = _strict_string_tuple(raw.get("left_support"), label="left_support")
    right = _strict_string_tuple(raw.get("right_support"), label="right_support")
    if (len(left), len(right)) != split:
        raise ValueError("coset v3 candidate supports disagree with support_split")
    if sum(split) > MAX_TOTAL_SUPPORT_WEIGHT:
        raise ValueError("total coset support weight exceeds six")
    if view.left_identity_id not in left or view.right_identity_id not in right:
        raise ValueError("coset supports must contain their fixed identities")
    if not set(left) <= set(view.left_element_ids):
        raise ValueError("left_support contains an element outside the action")
    if not set(right) <= set(view.right_element_ids):
        raise ValueError("right_support contains an element outside the action")
    left_order = {
        value: index for index, value in enumerate(view.left_element_ids)
    }
    right_order = {
        value: index for index, value in enumerate(view.right_element_ids)
    }
    return {
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION_V3,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": COSET_RENDERER_V3_ID,
        "action_id": view.action_id,
        "support_split": list(split),
        "left_support": sorted(left, key=left_order.__getitem__),
        "right_support": sorted(right, key=right_order.__getitem__),
    }


def normalize_coset_candidate(raw: Mapping[str, Any]) -> dict[str, Any]:
    """Dispatch only between source-registered candidate representations."""

    if not isinstance(raw, Mapping):
        raise ValueError("coset candidate must be a mapping")
    identity = (raw.get("schema_version"), raw.get("representation_id"))
    if identity == (COSET_CANDIDATE_SCHEMA_VERSION, COSET_REPRESENTATION_ID):
        return normalize_candidate(raw)
    if identity == (
        COSET_CANDIDATE_SCHEMA_VERSION_V3,
        COSET_REPRESENTATION_ID_V3,
    ):
        return normalize_candidate_v3(raw)
    raise ValueError("coset candidate representation is not registered")


def coset_candidate_digest(candidate: Mapping[str, Any]) -> str:
    return canonical_json_sha256(normalize_coset_candidate(candidate))


def coset_support_orbit_bin(candidate: Mapping[str, Any]) -> int:
    normalized = normalize_coset_candidate(candidate)
    digest = canonical_json_sha256({
        "representation_id": normalized["representation_id"],
        "support_split": normalized.get("support_split", [3, 3]),
        "left_support": normalized["left_support"],
        "right_support": normalized["right_support"],
    })
    return int(digest[:8], 16) % COSET_SUPPORT_ORBIT_BINS


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


def _require_inert_json(value: Any, *, label: str) -> None:
    """Accept only exact built-in JSON values at proposal trust boundaries."""

    if type(value) in {str, int, bool} or value is None:
        return
    if type(value) is list:
        for index, item in enumerate(value):
            _require_inert_json(item, label=f"{label}[{index}]")
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise ValueError(f"{label} contains a non-string key")
            _require_inert_json(item, label=f"{label}.{key}")
        return
    raise ValueError(f"{label} must contain only inert JSON values")


def _catalog_manifest_payload(
    manifest: TrustedCosetCatalogManifest,
) -> dict[str, Any]:
    if type(manifest) is not TrustedCosetCatalogManifest:
        raise TypeError("catalog manifest must be a trusted registry value")
    if manifest.catalog_kind not in TRUSTED_COSET_CATALOG_KINDS:
        raise RuntimeError("catalog manifest kind is not trusted")
    return {
        "schema_version": COSET_CATALOG_MANIFEST_SCHEMA_VERSION,
        "manifest_id": manifest.manifest_id,
        "catalog_kind": manifest.catalog_kind,
        "catalog_id": manifest.catalog_id,
        "catalog_schema_version": manifest.catalog_schema_version,
        "catalog_sha256": _require_sha256(
            manifest.catalog_sha256,
            label="catalog manifest identity",
        ),
        "handler_id": manifest.handler_id,
    }


@lru_cache(maxsize=1)
def trusted_coset_catalog_manifests(
) -> tuple[TrustedCosetCatalogManifest, ...]:
    """Return installed manifests; unlisted cover/protograph IDs are inert."""

    identity = _action_catalog_identity()
    manifests = (
        TrustedCosetCatalogManifest(
            manifest_id=COSET_ACTION_CATALOG_V2_MANIFEST_ID,
            catalog_kind="action",
            catalog_id=str(identity["catalog_id"]),
            catalog_schema_version=2,
            catalog_sha256=str(identity["sha256"]),
            handler_id="action-catalog-v2-static",
        ),
    )
    if len({item.manifest_id for item in manifests}) != len(manifests):
        raise RuntimeError("trusted coset catalog registry has duplicate IDs")
    return tuple(sorted(manifests, key=lambda item: item.manifest_id))


def trusted_coset_catalog_manifest(
    manifest_id: str,
) -> TrustedCosetCatalogManifest:
    matches = [
        item for item in trusted_coset_catalog_manifests()
        if item.manifest_id == manifest_id
    ]
    if len(matches) != 1:
        raise ValueError("coset catalog manifest is not installed")
    return matches[0]


def trusted_coset_catalog_manifest_document(
    manifest_id: str,
) -> dict[str, Any]:
    payload = _catalog_manifest_payload(
        trusted_coset_catalog_manifest(manifest_id)
    )
    payload["manifest_sha256"] = canonical_json_sha256(payload)
    return payload


def trusted_coset_catalog_registry_document() -> dict[str, Any]:
    payload = {
        "kind": COSET_CATALOG_REGISTRY_KIND,
        "schema_version": COSET_CATALOG_REGISTRY_SCHEMA_VERSION,
        "manifests": [
            trusted_coset_catalog_manifest_document(item.manifest_id)
            for item in trusted_coset_catalog_manifests()
        ],
    }
    payload["registry_sha256"] = canonical_json_sha256(payload)
    return payload


def _renderer_descriptor_payload(
    descriptor: TrustedCosetRendererDescriptor,
) -> dict[str, Any]:
    if type(descriptor) is not TrustedCosetRendererDescriptor:
        raise TypeError("renderer descriptor must be a trusted registry value")
    if descriptor.catalog_kind not in TRUSTED_COSET_CATALOG_KINDS:
        raise RuntimeError("trusted renderer has an unsupported catalog kind")
    return {
        "schema_version": COSET_RENDERER_DESCRIPTOR_SCHEMA_VERSION,
        "descriptor_id": descriptor.descriptor_id,
        "policy_schema_version": descriptor.policy_schema_version,
        "candidate_schema_version": descriptor.candidate_schema_version,
        "representation_id": descriptor.representation_id,
        "catalog_kind": descriptor.catalog_kind,
        "catalog_id": descriptor.catalog_id,
        "catalog_schema_version": descriptor.catalog_schema_version,
        "catalog_sha256": _action_catalog_sha256(),
        "map_schema_version": descriptor.map_schema_version,
        "map_descriptor_kind": descriptor.map_descriptor_kind,
        "checkpoint_compatibility_group": (
            descriptor.checkpoint_compatibility_group
        ),
        "support_splits": [list(split) for split in descriptor.support_splits],
        "feature_dimensions": list(descriptor.feature_dimensions),
    }


@lru_cache(maxsize=1)
def trusted_coset_renderer_descriptors(
) -> tuple[TrustedCosetRendererDescriptor, ...]:
    """Return the complete source-owned registry in stable ID order."""

    catalog_id = str(_action_catalog_identity()["catalog_id"])
    descriptors = (
        TrustedCosetRendererDescriptor(
            descriptor_id=COSET_RENDERER_V2_ID,
            policy_schema_version=2,
            candidate_schema_version=COSET_CANDIDATE_SCHEMA_VERSION,
            representation_id=COSET_REPRESENTATION_ID,
            catalog_kind="action",
            catalog_id=catalog_id,
            catalog_schema_version=2,
            map_schema_version=COSET_MAP_SCHEMA_VERSION,
            map_descriptor_kind=COSET_DESCRIPTOR_KIND,
            checkpoint_compatibility_group=(
                COSET_RENDERER_V2_CHECKPOINT_GROUP
            ),
            support_splits=((3, 3),),
            feature_dimensions=COSET_FEATURE_DIMENSIONS,
        ),
        TrustedCosetRendererDescriptor(
            descriptor_id=COSET_RENDERER_V3_ID,
            policy_schema_version=3,
            candidate_schema_version=COSET_CANDIDATE_SCHEMA_VERSION_V3,
            representation_id=COSET_REPRESENTATION_ID_V3,
            catalog_kind="action",
            catalog_id=catalog_id,
            catalog_schema_version=2,
            map_schema_version=COSET_MAP_SCHEMA_VERSION_V3,
            map_descriptor_kind=COSET_DESCRIPTOR_KIND_V3,
            checkpoint_compatibility_group=(
                COSET_RENDERER_V3_CHECKPOINT_GROUP
            ),
            support_splits=TRUSTED_COSET_SUPPORT_SPLITS,
            feature_dimensions=COSET_FEATURE_DIMENSIONS_V3,
        ),
    )
    if len({item.descriptor_id for item in descriptors}) != len(descriptors):
        raise RuntimeError("trusted coset renderer registry has duplicate IDs")
    if len({item.representation_id for item in descriptors}) != len(descriptors):
        raise RuntimeError(
            "trusted coset renderer registry has duplicate representations"
        )
    return tuple(sorted(descriptors, key=lambda item: item.descriptor_id))


def trusted_coset_renderer_descriptor(
    *,
    descriptor_id: str | None = None,
    representation_id: str | None = None,
) -> TrustedCosetRendererDescriptor:
    """Resolve exactly one reviewed descriptor; unknown IDs fail closed."""

    if (descriptor_id is None) == (representation_id is None):
        raise ValueError(
            "select a renderer by exactly one descriptor or representation ID"
        )
    matches = [
        item
        for item in trusted_coset_renderer_descriptors()
        if (
            item.descriptor_id == descriptor_id
            if descriptor_id is not None
            else item.representation_id == representation_id
        )
    ]
    if len(matches) != 1:
        raise ValueError("coset renderer descriptor is not registered")
    return matches[0]


def trusted_coset_renderer_descriptor_document(
    descriptor_id: str,
) -> dict[str, Any]:
    descriptor = trusted_coset_renderer_descriptor(descriptor_id=descriptor_id)
    payload = _renderer_descriptor_payload(descriptor)
    payload["descriptor_sha256"] = canonical_json_sha256(payload)
    return payload


def trusted_coset_renderer_registry_document() -> dict[str, Any]:
    """Return a self-hashed, data-only registry suitable for artifact binding."""

    payload = {
        "kind": COSET_RENDERER_REGISTRY_KIND,
        "schema_version": COSET_RENDERER_REGISTRY_SCHEMA_VERSION,
        "descriptors": [
            trusted_coset_renderer_descriptor_document(item.descriptor_id)
            for item in trusted_coset_renderer_descriptors()
        ],
    }
    payload["registry_sha256"] = canonical_json_sha256(payload)
    return payload


_COSET_RENDERER_PROPOSAL_FIELDS = frozenset({
    "schema_version",
    "kind",
    "renderer_descriptor_id",
    "renderer_descriptor_sha256",
    "renderer_registry_sha256",
    "catalog_manifest_id",
    "catalog_manifest_sha256",
    "catalog_registry_sha256",
    "catalog_kind",
    "catalog_id",
    "support_splits",
})


def coset_renderer_proposal_document(
    *,
    renderer_descriptor_id: str = COSET_RENDERER_V3_ID,
    catalog_manifest_id: str = COSET_ACTION_CATALOG_V2_MANIFEST_ID,
    support_splits: Sequence[Sequence[int]] = TRUSTED_COSET_SUPPORT_SPLITS,
) -> dict[str, Any]:
    """Build inert reviewer proposal data from installed registry identities."""

    descriptor = trusted_coset_renderer_descriptor_document(
        renderer_descriptor_id
    )
    renderer_registry = trusted_coset_renderer_registry_document()
    manifest = trusted_coset_catalog_manifest_document(catalog_manifest_id)
    catalog_registry = trusted_coset_catalog_registry_document()
    return {
        "schema_version": COSET_RENDERER_PROPOSAL_SCHEMA_VERSION,
        "kind": COSET_RENDERER_PROPOSAL_KIND,
        "renderer_descriptor_id": descriptor["descriptor_id"],
        "renderer_descriptor_sha256": descriptor["descriptor_sha256"],
        "renderer_registry_sha256": renderer_registry["registry_sha256"],
        "catalog_manifest_id": manifest["manifest_id"],
        "catalog_manifest_sha256": manifest["manifest_sha256"],
        "catalog_registry_sha256": catalog_registry["registry_sha256"],
        "catalog_kind": manifest["catalog_kind"],
        "catalog_id": manifest["catalog_id"],
        "support_splits": [list(split) for split in support_splits],
    }


def _normalize_renderer_proposal(
    raw: Mapping[str, Any],
) -> tuple[dict[str, Any], TrustedCosetRendererDescriptor,
           TrustedCosetCatalogManifest, tuple[tuple[int, int], ...]]:
    """Validate reviewer data against installed, source-owned registries."""

    if type(raw) is not dict:
        raise ValueError("coset renderer proposal must be a JSON object")
    _require_inert_json(raw, label="coset renderer proposal")
    if set(raw) != _COSET_RENDERER_PROPOSAL_FIELDS:
        raise ValueError("coset renderer proposal fields are not exact")
    if (
        raw.get("schema_version") != COSET_RENDERER_PROPOSAL_SCHEMA_VERSION
        or raw.get("kind") != COSET_RENDERER_PROPOSAL_KIND
    ):
        raise ValueError("coset renderer proposal schema is incompatible")
    descriptor_id = raw.get("renderer_descriptor_id")
    manifest_id = raw.get("catalog_manifest_id")
    if type(descriptor_id) is not str or type(manifest_id) is not str:
        raise ValueError("coset renderer proposal IDs are invalid")
    descriptor = trusted_coset_renderer_descriptor(
        descriptor_id=descriptor_id
    )
    descriptor_document = trusted_coset_renderer_descriptor_document(
        descriptor_id
    )
    renderer_registry = trusted_coset_renderer_registry_document()
    manifest = trusted_coset_catalog_manifest(manifest_id)
    manifest_document = trusted_coset_catalog_manifest_document(manifest_id)
    catalog_registry = trusted_coset_catalog_registry_document()
    exact_bindings = {
        "renderer_descriptor_sha256": descriptor_document[
            "descriptor_sha256"
        ],
        "renderer_registry_sha256": renderer_registry["registry_sha256"],
        "catalog_manifest_sha256": manifest_document["manifest_sha256"],
        "catalog_registry_sha256": catalog_registry["registry_sha256"],
        "catalog_kind": manifest.catalog_kind,
        "catalog_id": manifest.catalog_id,
    }
    for name, expected in exact_bindings.items():
        if raw.get(name) != expected:
            raise ValueError(f"coset renderer proposal {name} changed")
    if (
        descriptor.catalog_kind != manifest.catalog_kind
        or descriptor.catalog_id != manifest.catalog_id
        or descriptor.catalog_schema_version
        != manifest.catalog_schema_version
        or descriptor_document["catalog_sha256"]
        != manifest.catalog_sha256
    ):
        raise ValueError("renderer descriptor and catalog manifest disagree")
    split_rows = raw.get("support_splits")
    if type(split_rows) is not list or not split_rows:
        raise ValueError("coset renderer proposal support_splits is invalid")
    splits: list[tuple[int, int]] = []
    for row in split_rows:
        if (
            type(row) is not list
            or len(row) != 2
            or any(type(item) is not int for item in row)
        ):
            raise ValueError("proposal support split is not a two-int list")
        split = (row[0], row[1])
        if split not in descriptor.support_splits:
            raise ValueError("proposal support split is not renderer-approved")
        splits.append(split)
    descriptor_order = {
        split: index for index, split in enumerate(descriptor.support_splits)
    }
    if (
        len(set(splits)) != len(splits)
        or [descriptor_order[split] for split in splits]
        != sorted(descriptor_order[split] for split in splits)
    ):
        raise ValueError(
            "proposal support_splits must be unique and registry-ordered"
        )
    normalized = dict(raw)
    normalized["support_splits"] = [list(split) for split in splits]
    return normalized, descriptor, manifest, tuple(splits)


def activate_coset_renderer_proposal(
    raw: Mapping[str, Any],
) -> TrustedCosetRendererActivation:
    """Activate only a proposal backed by an installed static handler.

    This is the proposal -> validation -> activation gate used by an
    automated reviewer.  The only installed handler today is the action-v2
    catalog.  Merely writing ``catalog_kind=cover`` or ``protograph`` cannot
    pass this function and can never select a module or callable.
    """

    proposal, descriptor, manifest, splits = _normalize_renderer_proposal(raw)
    if manifest.handler_id != "action-catalog-v2-static":
        raise ValueError("installed catalog has no trusted renderer handler")
    if descriptor.descriptor_id != COSET_RENDERER_V3_ID:
        raise ValueError("proposal activation requires renderer v3")
    descriptor_document = trusted_coset_renderer_descriptor_document(
        descriptor.descriptor_id
    )
    renderer_registry = trusted_coset_renderer_registry_document()
    manifest_document = trusted_coset_catalog_manifest_document(
        manifest.manifest_id
    )
    catalog_registry = trusted_coset_catalog_registry_document()
    return TrustedCosetRendererActivation(
        proposal_sha256=canonical_json_sha256(proposal),
        renderer_descriptor_id=descriptor.descriptor_id,
        renderer_descriptor_sha256=descriptor_document[
            "descriptor_sha256"
        ],
        renderer_registry_sha256=renderer_registry["registry_sha256"],
        catalog_manifest_id=manifest.manifest_id,
        catalog_manifest_sha256=manifest_document["manifest_sha256"],
        catalog_registry_sha256=catalog_registry["registry_sha256"],
        catalog_handler_id=manifest.handler_id,
        approved_support_splits=splits,
    )


@lru_cache(maxsize=1)
def default_coset_renderer_activation() -> TrustedCosetRendererActivation:
    """Return the source-owned activation consumed by every v3 launch."""

    return activate_coset_renderer_proposal(coset_renderer_proposal_document())


def coset_renderer_activation_document(
    activation: TrustedCosetRendererActivation,
) -> dict[str, Any]:
    """Serialize and revalidate a trusted activation as a self-hashed artifact."""

    if type(activation) is not TrustedCosetRendererActivation:
        raise ValueError("coset renderer activation object is invalid")
    descriptor = trusted_coset_renderer_descriptor_document(
        activation.renderer_descriptor_id
    )
    renderer_registry = trusted_coset_renderer_registry_document()
    manifest = trusted_coset_catalog_manifest_document(
        activation.catalog_manifest_id
    )
    catalog_registry = trusted_coset_catalog_registry_document()
    exact = {
        "renderer_descriptor_sha256": descriptor["descriptor_sha256"],
        "renderer_registry_sha256": renderer_registry["registry_sha256"],
        "catalog_manifest_sha256": manifest["manifest_sha256"],
        "catalog_registry_sha256": catalog_registry["registry_sha256"],
        "catalog_handler_id": manifest["handler_id"],
    }
    for name, expected in exact.items():
        if getattr(activation, name) != expected:
            raise ValueError(f"coset renderer activation {name} changed")
    descriptor_value = trusted_coset_renderer_descriptor(
        descriptor_id=activation.renderer_descriptor_id
    )
    if (
        not activation.approved_support_splits
        or len(set(activation.approved_support_splits))
        != len(activation.approved_support_splits)
        or any(
            split not in descriptor_value.support_splits
            for split in activation.approved_support_splits
        )
    ):
        raise ValueError("coset renderer activation support splits are invalid")
    descriptor_order = {
        split: index
        for index, split in enumerate(descriptor_value.support_splits)
    }
    if [
        descriptor_order[split]
        for split in activation.approved_support_splits
    ] != sorted(
        descriptor_order[split]
        for split in activation.approved_support_splits
    ):
        raise ValueError("activation support splits are not registry-ordered")
    payload = {
        "schema_version": COSET_RENDERER_ACTIVATION_SCHEMA_VERSION,
        "kind": COSET_RENDERER_ACTIVATION_KIND,
        "proposal_sha256": _require_sha256(
            activation.proposal_sha256,
            label="activation proposal identity",
        ),
        "renderer_descriptor_id": activation.renderer_descriptor_id,
        "renderer_descriptor_sha256": activation.renderer_descriptor_sha256,
        "renderer_registry_sha256": activation.renderer_registry_sha256,
        "catalog_manifest_id": activation.catalog_manifest_id,
        "catalog_manifest_sha256": activation.catalog_manifest_sha256,
        "catalog_registry_sha256": activation.catalog_registry_sha256,
        "catalog_handler_id": activation.catalog_handler_id,
        "approved_support_splits": [
            list(split) for split in activation.approved_support_splits
        ],
    }
    payload["activation_sha256"] = canonical_json_sha256(payload)
    return payload


def trusted_coset_renderer_activation_from_document(
    raw: Mapping[str, Any],
) -> TrustedCosetRendererActivation:
    """Rehydrate only a self-hashed activation backed by live registries."""

    fields = {
        "schema_version",
        "kind",
        "proposal_sha256",
        "renderer_descriptor_id",
        "renderer_descriptor_sha256",
        "renderer_registry_sha256",
        "catalog_manifest_id",
        "catalog_manifest_sha256",
        "catalog_registry_sha256",
        "catalog_handler_id",
        "approved_support_splits",
        "activation_sha256",
    }
    if type(raw) is not dict or set(raw) != fields:
        raise ValueError("coset renderer activation fields are not exact")
    _require_inert_json(raw, label="coset renderer activation")
    if (
        raw.get("schema_version") != COSET_RENDERER_ACTIVATION_SCHEMA_VERSION
        or raw.get("kind") != COSET_RENDERER_ACTIVATION_KIND
    ):
        raise ValueError("coset renderer activation schema is incompatible")
    expected_sha256 = canonical_json_sha256({
        name: raw[name] for name in fields if name != "activation_sha256"
    })
    if raw.get("activation_sha256") != expected_sha256:
        raise ValueError("coset renderer activation self-hash changed")
    split_rows = raw.get("approved_support_splits")
    if type(split_rows) is not list:
        raise ValueError("activation approved_support_splits is invalid")
    splits: list[tuple[int, int]] = []
    for row in split_rows:
        if (
            type(row) is not list
            or len(row) != 2
            or any(type(item) is not int for item in row)
        ):
            raise ValueError("activation support split is invalid")
        splits.append((row[0], row[1]))
    activation = TrustedCosetRendererActivation(
        proposal_sha256=_require_sha256(
            raw.get("proposal_sha256"), label="activation proposal identity"
        ),
        renderer_descriptor_id=str(raw.get("renderer_descriptor_id")),
        renderer_descriptor_sha256=str(
            raw.get("renderer_descriptor_sha256")
        ),
        renderer_registry_sha256=str(raw.get("renderer_registry_sha256")),
        catalog_manifest_id=str(raw.get("catalog_manifest_id")),
        catalog_manifest_sha256=str(raw.get("catalog_manifest_sha256")),
        catalog_registry_sha256=str(raw.get("catalog_registry_sha256")),
        catalog_handler_id=str(raw.get("catalog_handler_id")),
        approved_support_splits=tuple(splits),
    )
    if coset_renderer_activation_document(activation) != raw:
        raise ValueError("coset renderer activation registry binding changed")
    return activation


def coset_renderer_portfolio_contract(
    representation_id: str,
) -> dict[str, Any]:
    """Expose only inert launch metadata for one registered representation."""

    descriptor = trusted_coset_renderer_descriptor(
        representation_id=representation_id
    )
    bins = (
        COSET_FEATURE_BINS
        if descriptor.map_schema_version == COSET_MAP_SCHEMA_VERSION
        else COSET_FEATURE_BINS_V3
    )
    return {
        "representation_id": descriptor.representation_id,
        "renderer_descriptor_id": descriptor.descriptor_id,
        "map_schema_version": descriptor.map_schema_version,
        "checkpoint_compatibility_group": (
            descriptor.checkpoint_compatibility_group
        ),
        "feature_dimensions": list(descriptor.feature_dimensions),
        "feature_bins": {
            name: bins[name] for name in descriptor.feature_dimensions
        },
        "num_islands": (
            4 if descriptor.map_schema_version == COSET_MAP_SCHEMA_VERSION else 5
        ),
    }


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


def coset_batch_map_descriptor_v3(
    candidates: Sequence[Mapping[str, Any]],
    *,
    policy_sha256: str,
    renderer_activation: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Seal one renderer-v3 batch, including its whitelisted support split."""

    policy_sha256 = _require_sha256(policy_sha256, label="policy_sha256")
    if not isinstance(candidates, Sequence) or isinstance(
        candidates, (str, bytes, bytearray)
    ):
        raise TypeError("descriptor candidates must be a sequence")
    if len(candidates) != MAX_GENERATED_CANDIDATES:
        raise ValueError(
            "renderer-v3 descriptor requires the exact production batch"
        )
    views = action_search_views()
    expected_quotas = quota_by_normality(views, MAX_GENERATED_CANDIDATES)
    lanes: dict[str, list[dict[str, Any]]] = {
        view.action_id: [] for view in views
    }
    normalized_rows: list[dict[str, Any]] = []
    observed_digests: set[str] = set()
    for index, raw in enumerate(candidates):
        try:
            normalized = normalize_candidate_v3(raw)
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                f"renderer-v3 descriptor candidate {index} is invalid"
            ) from exc
        if raw != normalized:
            raise ValueError(
                f"renderer-v3 descriptor candidate {index} is not canonical"
            )
        digest = coset_candidate_digest(normalized)
        if digest in observed_digests:
            raise ValueError("renderer-v3 candidate batch contains duplicates")
        observed_digests.add(digest)
        normalized_rows.append(normalized)
        lanes[normalized["action_id"]].append(normalized)
    if {
        action_id: len(rows) for action_id, rows in lanes.items()
    } != expected_quotas:
        raise ValueError("renderer-v3 candidate batch violates action quotas")
    split_values = {
        tuple(row["support_split"]) for row in normalized_rows
    }
    if len(split_values) != 1:
        raise ValueError("renderer-v3 production policy must use one support split")
    support_split = next(iter(split_values))
    if support_split not in TRUSTED_COSET_SUPPORT_SPLITS:
        raise ValueError("renderer-v3 batch uses an unregistered support split")

    descriptor_document = trusted_coset_renderer_descriptor_document(
        COSET_RENDERER_V3_ID
    )
    registry_document = trusted_coset_renderer_registry_document()
    if renderer_activation is None:
        activation_value = default_coset_renderer_activation()
    else:
        activation_value = trusted_coset_renderer_activation_from_document(
            renderer_activation
        )
    activation_document = coset_renderer_activation_document(
        activation_value
    )
    if list(support_split) not in activation_document[
        "approved_support_splits"
    ]:
        raise ValueError("renderer-v3 split is not activated")
    catalog_identity = _action_catalog_identity()
    ordered_views = tuple(sorted(views, key=lambda item: item.action_id))
    aggregate_histogram = [0] * COSET_SUPPORT_ORBIT_BINS
    lane_artifacts: list[dict[str, Any]] = []
    for lane_index, view in enumerate(ordered_views):
        rows = lanes[view.action_id]
        orbit_histogram = [0] * COSET_SUPPORT_ORBIT_BINS
        candidate_sha256 = []
        for row in rows:
            digest = coset_candidate_digest(row)
            candidate_sha256.append(digest)
            orbit = coset_support_orbit_bin(row)
            orbit_histogram[orbit] += 1
            aggregate_histogram[orbit] += 1
        lane_payload = {
            "schema_version": COSET_MAP_SCHEMA_VERSION_V3,
            "renderer_descriptor_id": COSET_RENDERER_V3_ID,
            "representation_id": COSET_REPRESENTATION_ID_V3,
            "action_lane_index": lane_index,
            "action_family_bin": view.action_family_bin,
            "action_id": view.action_id,
            "subgroup_normal": view.subgroup_normal,
            "support_split": list(support_split),
            "quota": expected_quotas[view.action_id],
            "candidate_sha256": candidate_sha256,
        }
        lane_sha256 = canonical_json_sha256(lane_payload)
        lane_artifacts.append({
            **lane_payload,
            "candidate_count": len(rows),
            "orbit_histogram": orbit_histogram,
            "lane_sha256": lane_sha256,
        })

    coordinates: dict[str, int] = {}
    class_artifacts: list[dict[str, Any]] = []
    for subgroup_normal, metric in (
        (False, COSET_NONNORMAL_LANE_METRIC),
        (True, COSET_NORMAL_LANE_METRIC),
    ):
        selected = [
            lane for lane in lane_artifacts
            if lane["subgroup_normal"] is subgroup_normal
        ]
        if not selected:
            raise RuntimeError("renderer-v3 descriptor lost a normality class")
        class_payload = {
            "schema_version": COSET_MAP_SCHEMA_VERSION_V3,
            "renderer_descriptor_id": COSET_RENDERER_V3_ID,
            "subgroup_normal": subgroup_normal,
            "metric": metric,
            "lanes": [
                {
                    "action_lane_index": lane["action_lane_index"],
                    "action_id": lane["action_id"],
                    "quota": lane["quota"],
                    "lane_sha256": lane["lane_sha256"],
                }
                for lane in selected
            ],
        }
        class_sha256 = canonical_json_sha256(class_payload)
        bucket = int(class_sha256[:16], 16) % COSET_FEATURE_BINS_V3[metric]
        coordinates[metric] = bucket
        class_artifacts.append({
            **class_payload,
            "class_sha256": class_sha256,
            "bucket": bucket,
        })

    orbit_payload = {
        "schema_version": COSET_MAP_SCHEMA_VERSION_V3,
        "renderer_descriptor_id": COSET_RENDERER_V3_ID,
        "support_split": list(support_split),
        "aggregate_orbit_histogram": aggregate_histogram,
        "lane_sha256": [lane["lane_sha256"] for lane in lane_artifacts],
    }
    orbit_sha256 = canonical_json_sha256(orbit_payload)
    coordinates[COSET_BATCH_ORBIT_PROFILE_METRIC] = (
        int(orbit_sha256[:16], 16)
        % COSET_FEATURE_BINS_V3[COSET_BATCH_ORBIT_PROFILE_METRIC]
    )
    coordinates[COSET_SUPPORT_SPLIT_METRIC] = (
        TRUSTED_COSET_SUPPORT_SPLITS.index(support_split)
    )
    ordered_digests = [
        coset_candidate_digest(row) for row in normalized_rows
    ]
    batch_payload = {
        "schema_version": COSET_MAP_SCHEMA_VERSION_V3,
        "renderer_descriptor_id": COSET_RENDERER_V3_ID,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "policy_sha256": policy_sha256,
        "renderer_activation_sha256": activation_document[
            "activation_sha256"
        ],
        "support_split": list(support_split),
        "ordered_candidate_sha256": ordered_digests,
    }
    batch_sha256 = canonical_json_sha256(batch_payload)
    artifact = {
        "kind": COSET_DESCRIPTOR_KIND_V3,
        "schema_version": COSET_MAP_SCHEMA_VERSION_V3,
        "renderer_descriptor": descriptor_document,
        "renderer_registry_sha256": registry_document["registry_sha256"],
        "renderer_activation": activation_document,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "catalog_kind": "action",
        "action_catalog_id": catalog_identity["catalog_id"],
        "action_catalog_sha256": catalog_identity["sha256"],
        "policy_sha256": policy_sha256,
        "support_split": list(support_split),
        "dimensions": list(COSET_FEATURE_DIMENSIONS_V3),
        "bins": dict(COSET_FEATURE_BINS_V3),
        "coordinates": {
            name: coordinates[name] for name in COSET_FEATURE_DIMENSIONS_V3
        },
        "lanes": lane_artifacts,
        "classes": class_artifacts,
        "batch": {
            **batch_payload,
            "candidate_count": len(normalized_rows),
            "batch_sha256": batch_sha256,
            "aggregate_orbit_histogram": aggregate_histogram,
            "orbit_profile_sha256": orbit_sha256,
        },
    }
    artifact["descriptor_sha256"] = canonical_json_sha256(artifact)
    return artifact


def coset_batch_map_descriptor_registered(
    candidates: Sequence[Mapping[str, Any]],
    *,
    policy_sha256: str,
    renderer_activation: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Dispatch map sealing by an exact registered candidate identity."""

    if not candidates:
        raise ValueError("cannot describe an empty coset candidate batch")
    first = candidates[0]
    if not isinstance(first, Mapping):
        raise ValueError("coset descriptor candidate is not a mapping")
    representation_id = first.get("representation_id")
    if representation_id == COSET_REPRESENTATION_ID:
        if renderer_activation is not None:
            raise ValueError("renderer-v2 does not accept a v3 activation")
        return coset_batch_map_descriptor(
            candidates, policy_sha256=policy_sha256
        )
    if representation_id == COSET_REPRESENTATION_ID_V3:
        return coset_batch_map_descriptor_v3(
            candidates,
            policy_sha256=policy_sha256,
            renderer_activation=renderer_activation,
        )
    raise ValueError("coset batch representation is not registered")


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
    "TrustedCosetCatalogManifest",
    "TrustedCosetRendererActivation",
    "TrustedCosetRendererDescriptor",
    "ACTION_FAMILY_BINS",
    "COSET_ACTION_FAMILY_METRIC",
    "COSET_BATCH_ORBIT_PROFILE_METRIC",
    "COSET_CANDIDATE_SCHEMA_VERSION",
    "COSET_CANDIDATE_SCHEMA_VERSION_V3",
    "COSET_ACTION_CATALOG_V2_MANIFEST_ID",
    "COSET_CATALOG_MANIFEST_SCHEMA_VERSION",
    "COSET_CATALOG_REGISTRY_KIND",
    "COSET_CATALOG_REGISTRY_SCHEMA_VERSION",
    "COSET_EVALUATOR_KIND",
    "COSET_FEATURE_BINS",
    "COSET_FEATURE_BINS_V3",
    "COSET_FEATURE_DIMENSIONS",
    "COSET_FEATURE_DIMENSIONS_V3",
    "COSET_MAP_SCHEMA_METRIC",
    "COSET_MAP_SCHEMA_VERSION",
    "COSET_MAP_SCHEMA_VERSION_V3",
    "COSET_NONNORMAL_LANE_METRIC",
    "COSET_NORMAL_LANE_METRIC",
    "COSET_REPRESENTATION_ID",
    "COSET_REPRESENTATION_ID_V3",
    "COSET_RENDERER_V2_ID",
    "COSET_RENDERER_V3_ID",
    "COSET_RENDERER_V2_CHECKPOINT_GROUP",
    "COSET_RENDERER_V3_CHECKPOINT_GROUP",
    "COSET_RENDERER_ACTIVATION_KIND",
    "COSET_RENDERER_ACTIVATION_JSON_ENV",
    "COSET_RENDERER_ACTIVATION_SCHEMA_VERSION",
    "COSET_RENDERER_PROPOSAL_KIND",
    "COSET_RENDERER_PROPOSAL_SCHEMA_VERSION",
    "COSET_SUPPORT_SPLIT_METRIC",
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
    "TRUSTED_COSET_CATALOG_KINDS",
    "TRUSTED_COSET_SUPPORT_SPLITS",
    "action_search_view",
    "action_search_views",
    "candidate_digest",
    "coset_candidate_digest",
    "canonical_json_sha256",
    "activate_coset_renderer_proposal",
    "coset_batch_map_descriptor",
    "coset_batch_map_descriptor_registered",
    "coset_batch_map_descriptor_v3",
    "coset_renderer_portfolio_contract",
    "coset_renderer_activation_document",
    "coset_renderer_proposal_document",
    "default_coset_renderer_activation",
    "coset_support_orbit_bin",
    "normalize_action_descriptor",
    "normalize_candidate",
    "normalize_candidate_v3",
    "normalize_coset_candidate",
    "quota_by_normality",
    "proof_ladder_config_contract",
    "support_orbit_bin",
    "trusted_coset_renderer_descriptor",
    "trusted_coset_renderer_descriptor_document",
    "trusted_coset_renderer_descriptors",
    "trusted_coset_renderer_registry_document",
    "trusted_coset_renderer_activation_from_document",
    "trusted_coset_catalog_manifest",
    "trusted_coset_catalog_manifest_document",
    "trusted_coset_catalog_manifests",
    "trusted_coset_catalog_registry_document",
]
