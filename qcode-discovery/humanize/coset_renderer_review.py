"""Fail-closed bridge from reviewer focus data to trusted coset activation.

The reviewer can propose only inert identifiers.  This module resolves those
identifiers against source-owned registries and either seals an activation for
the immediately following Stage-1 round or emits a representation-expansion
handoff.  It never imports or executes reviewer-selected code.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from typing import Any

from evolve.coset_search_contract import (
    COSET_ACTION_CATALOG_V2_MANIFEST_ID,
    COSET_RENDERER_V3_ID,
    TRUSTED_COSET_CATALOG_KINDS,
    activate_coset_renderer_proposal,
    canonical_json_sha256,
    coset_renderer_activation_document,
    coset_renderer_proposal_document,
    trusted_coset_catalog_manifest,
    trusted_coset_renderer_descriptor,
)


_LEGACY_REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION = 1
_LEGACY_REVIEWER_RENDERER_RESOLUTION_KIND = (
    "qcode-reviewer-coset-renderer-resolution-v1"
)
_LEGACY_REVIEWER_RENDERER_HANDOFF_SCHEMA_VERSION = 1
_LEGACY_REVIEWER_RENDERER_HANDOFF_KIND = (
    "qcode-coset-representation-expansion-handoff-v1"
)
_LEGACY_REVIEWER_RENDERER_PROPOSAL_SCHEMA_VERSION = 1
_LEGACY_REVIEWER_RENDERER_PROPOSAL_KIND = (
    "qcode-reviewer-renderer-proposal-v1"
)
REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION = 2
REVIEWER_RENDERER_RESOLUTION_KIND = (
    "qcode-reviewer-coset-renderer-resolution-v2"
)
REVIEWER_RENDERER_HANDOFF_SCHEMA_VERSION = 2
REVIEWER_RENDERER_HANDOFF_KIND = (
    "qcode-coset-representation-expansion-handoff-v2"
)
REVIEWER_RENDERER_PROPOSAL_SCHEMA_VERSION = 2
REVIEWER_RENDERER_PROPOSAL_KIND = "qcode-reviewer-renderer-proposal-v2"
REVIEWER_RENDERER_FOCUS_DIMENSIONS = frozenset({
    "renderer_descriptor_id",
    "catalog_manifest_id",
    "catalog_kind",
    "support_split_type",
})
REVIEWER_RENDERER_HANDOFF_REASONS = frozenset({
    "ambiguous_reviewer_proposal",
    "catalog_kind_mismatch",
    "catalog_manifest_not_installed",
    "incomplete_reviewer_proposal",
    "renderer_activation_rejected",
    "renderer_descriptor_not_installed",
    "support_split_complement_empty",
    "support_split_not_installed",
})
_SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}\Z")
_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_SUPPORT_SPLIT = re.compile(r"([1-6])\+([1-6])\Z")
_REVIEWER_DIRECTIONS = frozenset({"increase", "decrease", "maintain"})


class ReviewerRendererResolutionError(ValueError):
    """A sealed renderer resolution is malformed or cannot be replayed."""


def _sha256(value: Any, *, label: str) -> str:
    if type(value) is not str or _SHA256.fullmatch(value) is None:
        raise ReviewerRendererResolutionError(
            f"{label} must be a lowercase SHA-256 digest"
        )
    return value


def _round(value: Any, *, label: str) -> int:
    if type(value) is not int or value < 1:
        raise ReviewerRendererResolutionError(
            f"{label} must be a positive integer"
        )
    return value


def _safe_id(value: Any, *, label: str) -> str:
    if type(value) is not str or _SAFE_ID.fullmatch(value) is None:
        raise ReviewerRendererResolutionError(f"{label} is not a safe ID")
    return value


def _normalized_reviewer_proposal_v1(
    search_action: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str | None]:
    """Replay the direction-blind proposal emitted by historical controllers."""

    if not isinstance(search_action, Mapping):
        raise ReviewerRendererResolutionError("search_action must be an object")
    focus = search_action.get("focus")
    if type(focus) is not list:
        raise ReviewerRendererResolutionError("search_action.focus is invalid")
    selected: dict[str, list[str]] = {
        dimension: [] for dimension in REVIEWER_RENDERER_FOCUS_DIMENSIONS
    }
    for item in focus:
        if type(item) is not dict:
            raise ReviewerRendererResolutionError("reviewer focus row is invalid")
        dimension = item.get("dimension")
        if dimension not in selected:
            continue
        value = item.get("value")
        if type(value) is not str:
            raise ReviewerRendererResolutionError(
                "reviewer renderer focus value is invalid"
            )
        selected[dimension].append(value)
    if not any(selected.values()):
        return None, None
    if any(len(values) != 1 for values in selected.values() if values):
        return None, "ambiguous_reviewer_proposal"

    identity_fields = (
        "renderer_descriptor_id",
        "catalog_manifest_id",
        "catalog_kind",
    )
    has_identity = any(selected[name] for name in identity_fields)
    if has_identity and any(not selected[name] for name in identity_fields):
        return None, "incomplete_reviewer_proposal"
    descriptor_id = (
        selected["renderer_descriptor_id"][0]
        if has_identity
        else COSET_RENDERER_V3_ID
    )
    manifest_id = (
        selected["catalog_manifest_id"][0]
        if has_identity
        else COSET_ACTION_CATALOG_V2_MANIFEST_ID
    )
    catalog_kind = (
        selected["catalog_kind"][0] if has_identity else "action"
    )
    _safe_id(descriptor_id, label="renderer_descriptor_id")
    _safe_id(manifest_id, label="catalog_manifest_id")
    if catalog_kind not in TRUSTED_COSET_CATALOG_KINDS:
        raise ReviewerRendererResolutionError("catalog_kind is invalid")
    split_values = selected["support_split_type"]
    if len(split_values) != 1:
        return None, (
            "ambiguous_reviewer_proposal"
            if split_values
            else "incomplete_reviewer_proposal"
        )
    match = _SUPPORT_SPLIT.fullmatch(split_values[0])
    if match is None:
        raise ReviewerRendererResolutionError("support_split_type is invalid")
    return {
        "schema_version": _LEGACY_REVIEWER_RENDERER_PROPOSAL_SCHEMA_VERSION,
        "kind": _LEGACY_REVIEWER_RENDERER_PROPOSAL_KIND,
        "renderer_descriptor_id": descriptor_id,
        "catalog_manifest_id": manifest_id,
        "catalog_kind": catalog_kind,
        "support_split": [int(match.group(1)), int(match.group(2))],
    }, None


def _normalized_reviewer_proposal(
    search_action: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str | None]:
    """Bind renderer focus values and their executable direction."""

    if not isinstance(search_action, Mapping):
        raise ReviewerRendererResolutionError("search_action must be an object")
    focus = search_action.get("focus")
    if type(focus) is not list:
        raise ReviewerRendererResolutionError("search_action.focus is invalid")
    selected: dict[str, list[tuple[str, str]]] = {
        dimension: [] for dimension in REVIEWER_RENDERER_FOCUS_DIMENSIONS
    }
    for item in focus:
        if type(item) is not dict:
            raise ReviewerRendererResolutionError("reviewer focus row is invalid")
        dimension = item.get("dimension")
        if dimension not in selected:
            continue
        value = item.get("value")
        direction = item.get("direction")
        if type(value) is not str:
            raise ReviewerRendererResolutionError(
                "reviewer renderer focus value is invalid"
            )
        if type(direction) is not str or direction not in _REVIEWER_DIRECTIONS:
            raise ReviewerRendererResolutionError(
                "reviewer renderer focus direction is invalid"
            )
        selected[dimension].append((value, direction))
    if not any(selected.values()):
        return None, None
    if any(len(values) != 1 for values in selected.values() if values):
        return None, "ambiguous_reviewer_proposal"

    identity_fields = (
        "renderer_descriptor_id",
        "catalog_manifest_id",
        "catalog_kind",
    )
    has_identity = any(selected[name] for name in identity_fields)
    if has_identity and any(not selected[name] for name in identity_fields):
        return None, "incomplete_reviewer_proposal"
    descriptor_id = (
        selected["renderer_descriptor_id"][0][0]
        if has_identity
        else COSET_RENDERER_V3_ID
    )
    manifest_id = (
        selected["catalog_manifest_id"][0][0]
        if has_identity
        else COSET_ACTION_CATALOG_V2_MANIFEST_ID
    )
    catalog_kind = (
        selected["catalog_kind"][0][0] if has_identity else "action"
    )
    _safe_id(descriptor_id, label="renderer_descriptor_id")
    _safe_id(manifest_id, label="catalog_manifest_id")
    if catalog_kind not in TRUSTED_COSET_CATALOG_KINDS:
        raise ReviewerRendererResolutionError("catalog_kind is invalid")
    split_values = selected["support_split_type"]
    if len(split_values) != 1:
        return None, (
            "ambiguous_reviewer_proposal"
            if split_values
            else "incomplete_reviewer_proposal"
        )
    split_value, split_direction = split_values[0]
    match = _SUPPORT_SPLIT.fullmatch(split_value)
    if match is None:
        raise ReviewerRendererResolutionError("support_split_type is invalid")
    return {
        "schema_version": REVIEWER_RENDERER_PROPOSAL_SCHEMA_VERSION,
        "kind": REVIEWER_RENDERER_PROPOSAL_KIND,
        "renderer_descriptor_id": descriptor_id,
        "catalog_manifest_id": manifest_id,
        "catalog_kind": catalog_kind,
        "support_split": [int(match.group(1)), int(match.group(2))],
        "support_split_direction": split_direction,
    }, None


def _resolution_payload(
    *,
    source_round: int,
    target_round: int,
    review_artifact_sha256: str,
    reviewer_proposal: dict[str, Any] | None,
    status: str,
    renderer_proposal: dict[str, Any] | None,
    renderer_activation: dict[str, Any] | None,
    handoff: dict[str, Any] | None,
    legacy: bool,
) -> dict[str, Any]:
    schema_version = (
        _LEGACY_REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION
        if legacy
        else REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION
    )
    kind = (
        _LEGACY_REVIEWER_RENDERER_RESOLUTION_KIND
        if legacy
        else REVIEWER_RENDERER_RESOLUTION_KIND
    )
    payload = {
        "schema_version": schema_version,
        "kind": kind,
        "source_round": source_round,
        "target_round": target_round,
        "review_artifact_sha256": review_artifact_sha256,
        "reviewer_proposal": reviewer_proposal,
        "reviewer_proposal_sha256": (
            canonical_json_sha256(reviewer_proposal)
            if reviewer_proposal is not None
            else None
        ),
        "status": status,
        "renderer_proposal": renderer_proposal,
        "renderer_activation": renderer_activation,
        "renderer_activation_sha256": (
            renderer_activation["activation_sha256"]
            if renderer_activation is not None
            else None
        ),
        "representation_expansion_handoff": handoff,
    }
    payload["resolution_sha256"] = canonical_json_sha256(payload)
    return payload


def _handoff(
    *,
    reason: str,
    source_round: int,
    target_round: int,
    review_artifact_sha256: str,
    reviewer_proposal: dict[str, Any] | None,
    legacy: bool,
) -> dict[str, Any]:
    if reason not in REVIEWER_RENDERER_HANDOFF_REASONS:
        raise ReviewerRendererResolutionError("handoff reason is invalid")
    handoff = {
        "schema_version": (
            _LEGACY_REVIEWER_RENDERER_HANDOFF_SCHEMA_VERSION
            if legacy
            else REVIEWER_RENDERER_HANDOFF_SCHEMA_VERSION
        ),
        "kind": (
            _LEGACY_REVIEWER_RENDERER_HANDOFF_KIND
            if legacy
            else REVIEWER_RENDERER_HANDOFF_KIND
        ),
        "status": "representation_expansion_handoff",
        "reason": reason,
        "source_round": source_round,
        "target_round": target_round,
        "review_artifact_sha256": review_artifact_sha256,
        "reviewer_proposal_sha256": (
            canonical_json_sha256(reviewer_proposal)
            if reviewer_proposal is not None
            else None
        ),
        "execution_permitted": False,
    }
    handoff["handoff_sha256"] = canonical_json_sha256(handoff)
    return _resolution_payload(
        source_round=source_round,
        target_round=target_round,
        review_artifact_sha256=review_artifact_sha256,
        reviewer_proposal=reviewer_proposal,
        status="representation_expansion_handoff",
        renderer_proposal=None,
        renderer_activation=None,
        handoff=handoff,
        legacy=legacy,
    )


def _resolve_reviewer_renderer_action(
    search_action: Mapping[str, Any],
    *,
    source_round: int,
    target_round: int,
    review_artifact_sha256: str,
    legacy: bool,
) -> dict[str, Any] | None:
    """Seal the next-round activation or a non-executable handoff."""

    source_round = _round(source_round, label="source_round")
    target_round = _round(target_round, label="target_round")
    if target_round != source_round + 1:
        raise ReviewerRendererResolutionError(
            "renderer activation must target the immediately following round"
        )
    review_artifact_sha256 = _sha256(
        review_artifact_sha256,
        label="review_artifact_sha256",
    )
    normalizer = (
        _normalized_reviewer_proposal_v1
        if legacy
        else _normalized_reviewer_proposal
    )
    reviewer_proposal, extraction_error = normalizer(search_action)
    if reviewer_proposal is None and extraction_error is None:
        return None
    if extraction_error is not None:
        return _handoff(
            reason=extraction_error,
            source_round=source_round,
            target_round=target_round,
            review_artifact_sha256=review_artifact_sha256,
            reviewer_proposal=reviewer_proposal,
            legacy=legacy,
        )
    assert reviewer_proposal is not None
    descriptor_id = reviewer_proposal["renderer_descriptor_id"]
    manifest_id = reviewer_proposal["catalog_manifest_id"]
    try:
        descriptor = trusted_coset_renderer_descriptor(
            descriptor_id=descriptor_id
        )
    except ValueError:
        reason = "renderer_descriptor_not_installed"
    else:
        try:
            manifest = trusted_coset_catalog_manifest(manifest_id)
        except ValueError:
            reason = "catalog_manifest_not_installed"
        else:
            split = tuple(reviewer_proposal["support_split"])
            if reviewer_proposal["catalog_kind"] != manifest.catalog_kind:
                reason = "catalog_kind_mismatch"
            elif (
                descriptor.catalog_kind != manifest.catalog_kind
                or descriptor.catalog_id != manifest.catalog_id
            ):
                reason = "catalog_kind_mismatch"
            elif split not in descriptor.support_splits:
                reason = "support_split_not_installed"
            else:
                support_splits = (split,)
                if (
                    not legacy
                    and reviewer_proposal["support_split_direction"]
                    == "decrease"
                ):
                    support_splits = tuple(
                        installed_split
                        for installed_split in descriptor.support_splits
                        if installed_split != split
                    )
                    if not support_splits:
                        return _handoff(
                            reason="support_split_complement_empty",
                            source_round=source_round,
                            target_round=target_round,
                            review_artifact_sha256=review_artifact_sha256,
                            reviewer_proposal=reviewer_proposal,
                            legacy=legacy,
                        )
                try:
                    proposal = coset_renderer_proposal_document(
                        renderer_descriptor_id=descriptor_id,
                        catalog_manifest_id=manifest_id,
                        support_splits=support_splits,
                    )
                    activation = coset_renderer_activation_document(
                        activate_coset_renderer_proposal(proposal)
                    )
                except (TypeError, ValueError):
                    reason = "renderer_activation_rejected"
                else:
                    return _resolution_payload(
                        source_round=source_round,
                        target_round=target_round,
                        review_artifact_sha256=review_artifact_sha256,
                        reviewer_proposal=reviewer_proposal,
                        status="activated",
                        renderer_proposal=proposal,
                        renderer_activation=activation,
                        handoff=None,
                        legacy=legacy,
                    )
    return _handoff(
        reason=reason,
        source_round=source_round,
        target_round=target_round,
        review_artifact_sha256=review_artifact_sha256,
        reviewer_proposal=reviewer_proposal,
        legacy=legacy,
    )


def resolve_reviewer_renderer_action(
    search_action: Mapping[str, Any],
    *,
    source_round: int,
    target_round: int,
    review_artifact_sha256: str,
) -> dict[str, Any] | None:
    """Seal a direction-aware v2 activation for the next round."""

    return _resolve_reviewer_renderer_action(
        search_action,
        source_round=source_round,
        target_round=target_round,
        review_artifact_sha256=review_artifact_sha256,
        legacy=False,
    )


def validate_reviewer_renderer_resolution(
    value: Mapping[str, Any],
    *,
    search_action: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay a sealed resolution against the current installed registries."""

    if type(value) is not dict:
        raise ReviewerRendererResolutionError("renderer resolution is invalid")
    schema_version = value.get("schema_version")
    kind = value.get("kind")
    if (
        type(schema_version) is int
        and schema_version == _LEGACY_REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION
        and kind == _LEGACY_REVIEWER_RENDERER_RESOLUTION_KIND
    ):
        legacy = True
    elif (
        type(schema_version) is int
        and schema_version == REVIEWER_RENDERER_RESOLUTION_SCHEMA_VERSION
        and kind == REVIEWER_RENDERER_RESOLUTION_KIND
    ):
        legacy = False
    else:
        raise ReviewerRendererResolutionError(
            "renderer resolution schema is incompatible"
        )
    expected = _resolve_reviewer_renderer_action(
        search_action,
        source_round=value.get("source_round"),
        target_round=value.get("target_round"),
        review_artifact_sha256=value.get("review_artifact_sha256"),
        legacy=legacy,
    )
    if expected is None or value != expected:
        raise ReviewerRendererResolutionError(
            "renderer resolution does not replay exactly"
        )
    return dict(value)


__all__ = [
    "REVIEWER_RENDERER_FOCUS_DIMENSIONS",
    "REVIEWER_RENDERER_HANDOFF_KIND",
    "REVIEWER_RENDERER_HANDOFF_REASONS",
    "REVIEWER_RENDERER_RESOLUTION_KIND",
    "ReviewerRendererResolutionError",
    "resolve_reviewer_renderer_action",
    "validate_reviewer_renderer_resolution",
]
