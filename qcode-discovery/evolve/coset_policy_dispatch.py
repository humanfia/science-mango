"""Static dispatcher for source-registered coset JSON renderers.

Policy data never supplies an import path or callable.  This module has one
reviewed branch per renderer epoch and fails closed for every other identity.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any

from evolve import coset_policy_dsl as policy_v2
from evolve import coset_policy_dsl_v3 as policy_v3
from evolve.coset_search_contract import (
    COSET_RENDERER_V2_ID,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID,
    COSET_REPRESENTATION_ID_V3,
    TrustedCosetRendererActivation,
    TrustedCosetRendererDescriptor,
    coset_renderer_activation_document,
    default_coset_renderer_activation,
    trusted_coset_renderer_descriptor,
)


class CosetPolicyDispatchError(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class RegisteredPolicyRender:
    descriptor: TrustedCosetRendererDescriptor
    policy: Any
    document: dict[str, Any]
    policy_sha256: str
    candidates: tuple[dict[str, Any], ...]
    activation: dict[str, Any] | None


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CosetPolicyDispatchError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise CosetPolicyDispatchError(f"non-finite JSON number: {value}")


def _peek_document(payload: str | bytes) -> dict[str, Any]:
    if type(payload) is bytes:
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise CosetPolicyDispatchError("policy is not UTF-8") from exc
    elif type(payload) is str:
        text = payload
    else:
        raise CosetPolicyDispatchError("policy payload must be text or bytes")
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_constant,
        )
    except CosetPolicyDispatchError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise CosetPolicyDispatchError("policy is not strict JSON") from exc
    if type(value) is not dict:
        raise CosetPolicyDispatchError("policy root must be a JSON object")
    return value


def _registered_identity(document: dict[str, Any]) -> str:
    identity = (
        document.get("schema_version"),
        document.get("kind"),
        document.get("representation_id"),
        document.get("renderer_descriptor_id", document.get("renderer")),
    )
    if identity == (
        policy_v2.POLICY_SCHEMA_VERSION,
        policy_v2.POLICY_KIND,
        COSET_REPRESENTATION_ID,
        COSET_RENDERER_V2_ID,
    ):
        return COSET_RENDERER_V2_ID
    if identity == (
        policy_v3.POLICY_SCHEMA_VERSION,
        policy_v3.POLICY_KIND,
        COSET_REPRESENTATION_ID_V3,
        COSET_RENDERER_V3_ID,
    ):
        return COSET_RENDERER_V3_ID
    raise CosetPolicyDispatchError("policy renderer identity is not registered")


def _parse_and_render_static(
    payload: str | bytes,
    document: dict[str, Any],
    renderer_id: str,
    *,
    activation: dict[str, Any] | None,
) -> RegisteredPolicyRender:
    try:
        if renderer_id == COSET_RENDERER_V2_ID:
            policy = policy_v2.parse_policy(payload)
            canonical = policy_v2.policy_document(policy)
            digest = policy_v2.policy_digest(policy)
            candidates = policy_v2.render_candidates(policy)
        elif renderer_id == COSET_RENDERER_V3_ID:
            policy = policy_v3.parse_policy(payload)
            canonical = policy_v3.policy_document(policy)
            digest = policy_v3.policy_digest(policy)
            candidates = policy_v3.render_candidates(policy)
        else:  # Exhaustiveness guard if the registry grows without a handler.
            raise CosetPolicyDispatchError(
                "registered renderer has no trusted implementation"
            )
    except (
        policy_v2.CosetPolicyError,
        policy_v3.CosetPolicyV3Error,
    ) as exc:
        raise CosetPolicyDispatchError(str(exc)) from exc
    if canonical != document:
        raise CosetPolicyDispatchError("policy text is not canonicalizable")
    descriptor = trusted_coset_renderer_descriptor(
        descriptor_id=renderer_id
    )
    return RegisteredPolicyRender(
        descriptor=descriptor,
        policy=policy,
        document=canonical,
        policy_sha256=digest,
        candidates=tuple(candidates),
        activation=activation,
    )


def parse_and_render_registered_policy(
    payload: str | bytes,
) -> RegisteredPolicyRender:
    """Parse through a static branch; v3 consumes its source activation."""

    document = _peek_document(payload)
    renderer_id = _registered_identity(document)
    if renderer_id == COSET_RENDERER_V3_ID:
        return parse_and_render_activated_policy(
            payload,
            default_coset_renderer_activation(),
        )
    return _parse_and_render_static(
        payload,
        document,
        renderer_id,
        activation=None,
    )


def canonical_registered_policy_json(render: RegisteredPolicyRender) -> str:
    if type(render) is not RegisteredPolicyRender:
        raise CosetPolicyDispatchError("registered render value is invalid")
    return json.dumps(
        render.document,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def parse_and_render_activated_policy(
    payload: str | bytes,
    activation: TrustedCosetRendererActivation,
) -> RegisteredPolicyRender:
    """Execute the one static handler selected by a validated activation.

    The activation is registry data, not a module or callable selector.  A
    future catalog remains unusable until this dispatcher gains a reviewed
    explicit branch for its source-owned ``handler_id``.
    """

    activation_document = coset_renderer_activation_document(activation)
    document = _peek_document(payload)
    renderer_id = _registered_identity(document)
    rendered = _parse_and_render_static(
        payload,
        document,
        renderer_id,
        activation=activation_document,
    )
    if rendered.descriptor.descriptor_id != (
        activation.renderer_descriptor_id
    ):
        raise CosetPolicyDispatchError(
            "activated renderer and policy descriptor disagree"
        )
    if activation.catalog_handler_id != "action-catalog-v2-static":
        raise CosetPolicyDispatchError(
            "activated catalog has no trusted dispatch branch"
        )
    split = getattr(rendered.policy, "support_split", (3, 3))
    if split not in activation.approved_support_splits:
        raise CosetPolicyDispatchError(
            "policy support split is not approved by the activation"
        )
    return rendered


__all__ = [
    "CosetPolicyDispatchError",
    "RegisteredPolicyRender",
    "canonical_registered_policy_json",
    "parse_and_render_activated_policy",
    "parse_and_render_registered_policy",
]
