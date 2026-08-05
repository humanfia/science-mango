"""Typed, data-only policy DSL for coset two-block candidate search.

The policy language is strict JSON, not Python.  A policy may select only the
source-bound action IDs and numeric indices into the nonidentity elements
exposed by ``evolve.coset_search_contract``.  Identity anchors never enter the
DSL.  The trusted renderer owns candidate construction, the production 3+3
support split, catalog traversal, quotas, deduplication, and output ordering.

This module deliberately contains no ``eval``, ``exec``, dynamic import, code
template, or user-selected callable.  Text accepted by :func:`parse_policy`
is decoded with :mod:`json` and then checked against an exact schema before it
can influence rendering.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from math import comb, gcd
from typing import Any

from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION,
    COSET_REPRESENTATION_ID,
    MAX_GENERATED_CANDIDATES,
    PRODUCTION_LEFT_WEIGHT,
    PRODUCTION_RIGHT_WEIGHT,
    ActionSearchView,
    action_search_views,
    candidate_digest,
    canonical_json_sha256,
    normalize_candidate,
    quota_by_normality,
)


POLICY_SCHEMA_VERSION = 1
POLICY_KIND = "qcode-coset-policy-dsl-v1"
RENDERER_KIND = "catalog-pair-walk-v1"
REQUIRED_ACTION_VIEW_COUNT = 2

MAX_POLICY_BYTES = 262_144
MAX_ACTION_POLICIES = 8
MAX_EXPLICIT_SUPPORTS_PER_ACTION = MAX_GENERATED_CANDIDATES
MAX_TOTAL_EXPLICIT_SUPPORTS = MAX_GENERATED_CANDIDATES
MAX_PAIR_SPACE = 100_000_000

_ROOT_FIELDS = frozenset({
    "schema_version",
    "kind",
    "representation_id",
    "action_catalog_sha256",
    "renderer",
    "support_split",
    "candidate_limit",
    "actions",
})
_ACTION_FIELDS = frozenset({
    "action_id",
    "quota",
    "include_published",
    "supports",
    "walk",
})
_SUPPORT_FIELDS = frozenset({"left", "right"})
_WALK_FIELDS = frozenset({"enabled", "offset", "stride"})


class CosetPolicyError(ValueError):
    """The supplied data is not a valid coset policy."""


@dataclass(frozen=True, slots=True)
class SupportDeclaration:
    """Two nonidentity catalog indices per side; identities are renderer-owned."""

    left: tuple[int, int]
    right: tuple[int, int]


@dataclass(frozen=True, slots=True)
class PairWalk:
    """A bounded traversal of the catalog pair-of-pairs space."""

    enabled: bool
    offset: int
    stride: int


@dataclass(frozen=True, slots=True)
class ActionPolicy:
    """Declarative policy for exactly one immutable action view."""

    action_id: str
    quota: int
    include_published: bool
    supports: tuple[SupportDeclaration, ...]
    walk: PairWalk


@dataclass(frozen=True, slots=True)
class CosetPolicy:
    """Fully validated policy ready for the trusted renderer."""

    action_catalog_sha256: str
    candidate_limit: int
    actions: tuple[ActionPolicy, ...]


def _catalog_sha256() -> str:
    from evaluation.coset_action_catalog import action_catalog_sha256

    value = action_catalog_sha256()
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise CosetPolicyError("coset action catalog SHA-256 is invalid")
    return value


def _views_by_id() -> dict[str, ActionSearchView]:
    views = action_search_views()
    if len(views) != REQUIRED_ACTION_VIEW_COUNT:
        raise CosetPolicyError(
            "coset policy v1 requires exactly the two source-bound action views"
        )
    if len(views) > MAX_ACTION_POLICIES:
        raise CosetPolicyError("coset action view count exceeds the DSL cap")
    return {view.action_id: view for view in views}


def _exact_object(value: Any, fields: frozenset[str], *, label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise CosetPolicyError(f"{label} must be a JSON object")
    observed = set(value)
    if observed != fields:
        missing = sorted(fields - observed)
        unknown = sorted(observed - fields)
        raise CosetPolicyError(
            f"{label} fields are not exact; missing={missing}, unknown={unknown}"
        )
    return value


def _require_declarative_json(value: Any, *, label: str = "coset policy") -> None:
    """Reject exotic Python objects even on the in-process validation API."""

    value_type = type(value)
    if value_type in {str, int, bool}:
        return
    if value_type is list:
        for index, item in enumerate(value):
            _require_declarative_json(item, label=f"{label}[{index}]")
        return
    if value_type is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise CosetPolicyError(f"{label} contains a non-string object key")
            _require_declarative_json(item, label=f"{label}.{key}")
        return
    raise CosetPolicyError(
        f"{label} must contain only JSON strings, integers, booleans, lists, and objects"
    )


def _strict_int(
    value: Any,
    *,
    label: str,
    minimum: int,
    maximum: int,
) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise CosetPolicyError(
            f"{label} must be an integer in [{minimum}, {maximum}]"
        )
    return value


def _strict_bool(value: Any, *, label: str) -> bool:
    if type(value) is not bool:
        raise CosetPolicyError(f"{label} must be a boolean")
    return value


def _pair_space(view: ActionSearchView) -> tuple[tuple[str, ...], tuple[str, ...], int]:
    left = tuple(
        element
        for element in view.left_element_ids
        if element != view.left_identity_id
    )
    right = tuple(
        element
        for element in view.right_element_ids
        if element != view.right_identity_id
    )
    if len(left) < 2 or len(right) < 2:
        raise CosetPolicyError(
            f"action {view.action_id} cannot provide a production 3+3 support"
        )
    size = comb(len(left), 2) * comb(len(right), 2)
    if size < 1 or size > MAX_PAIR_SPACE:
        raise CosetPolicyError(
            f"action {view.action_id} pair space exceeds the renderer cap"
        )
    return left, right, size


def _candidate(
    view: ActionSearchView,
    left: tuple[str, ...] | list[str],
    right: tuple[str, ...] | list[str],
) -> dict[str, Any]:
    return normalize_candidate({
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": view.action_id,
        "left_support": list(left),
        "right_support": list(right),
    })


def _support_declaration(
    raw: Any,
    *,
    view: ActionSearchView,
    index: int,
) -> SupportDeclaration:
    row = _exact_object(
        raw,
        _SUPPORT_FIELDS,
        label=f"action {view.action_id} support {index}",
    )
    left_indices = row["left"]
    right_indices = row["right"]
    if type(left_indices) is not list or type(right_indices) is not list:
        raise CosetPolicyError("coset support index sides must be JSON lists")
    # The fixed identity is intentionally absent from the DSL.  Exactly two
    # nonidentity indices on each side render to the production 3+3 support.
    if len(left_indices) != 2 or len(right_indices) != 2:
        raise CosetPolicyError(
            "coset support must declare exactly two nonidentity indices per side"
        )
    left_elements, right_elements, _ = _pair_space(view)
    if any(type(item) is not int for item in (*left_indices, *right_indices)):
        raise CosetPolicyError("coset support indices must be integers")
    if (
        len(set(left_indices)) != 2
        or len(set(right_indices)) != 2
        or any(not 0 <= item < len(left_elements) for item in left_indices)
        or any(not 0 <= item < len(right_elements) for item in right_indices)
    ):
        raise CosetPolicyError("coset support indices are duplicate or out of range")
    left_indices = sorted(left_indices)
    right_indices = sorted(right_indices)
    try:
        normalized = _candidate(
            view,
            (
                view.left_identity_id,
                *(left_elements[index] for index in left_indices),
            ),
            (
                view.right_identity_id,
                *(right_elements[index] for index in right_indices),
            ),
        )
    except (TypeError, ValueError) as exc:
        raise CosetPolicyError(
            f"action {view.action_id} support {index} is invalid: {exc}"
        ) from exc
    if (
        len(normalized["left_support"]) != PRODUCTION_LEFT_WEIGHT
        or len(normalized["right_support"]) != PRODUCTION_RIGHT_WEIGHT
    ):
        raise CosetPolicyError("trusted support renderer violated the 3+3 contract")
    return SupportDeclaration(
        left=(left_indices[0], left_indices[1]),
        right=(right_indices[0], right_indices[1]),
    )


def _candidate_from_declaration(
    view: ActionSearchView,
    support: SupportDeclaration,
) -> dict[str, Any]:
    left, right, _ = _pair_space(view)
    return _candidate(
        view,
        (
            view.left_identity_id,
            *(left[index] for index in support.left),
        ),
        (
            view.right_identity_id,
            *(right[index] for index in support.right),
        ),
    )


def _walk(raw: Any, *, view: ActionSearchView) -> PairWalk:
    row = _exact_object(raw, _WALK_FIELDS, label=f"action {view.action_id} walk")
    enabled = _strict_bool(row["enabled"], label="walk.enabled")
    left, right, pair_space = _pair_space(view)
    del left, right
    if not enabled:
        if row["offset"] != 0 or row["stride"] != 1:
            raise CosetPolicyError(
                "a disabled pair walk must use canonical offset=0 and stride=1"
            )
        return PairWalk(enabled=False, offset=0, stride=1)
    offset = _strict_int(
        row["offset"],
        label="walk.offset",
        minimum=0,
        maximum=pair_space - 1,
    )
    stride = _strict_int(
        row["stride"],
        label="walk.stride",
        minimum=1,
        maximum=pair_space - 1,
    )
    if gcd(stride, pair_space) != 1:
        raise CosetPolicyError(
            f"action {view.action_id} walk.stride must be coprime to its pair space"
        )
    return PairWalk(enabled=True, offset=offset, stride=stride)


def _published_candidate(view: ActionSearchView) -> dict[str, Any] | None:
    if (
        view.published_left_support is None
        or view.published_right_support is None
    ):
        return None
    return _candidate(
        view,
        view.published_left_support,
        view.published_right_support,
    )


def _action_policy(raw: Any, *, view: ActionSearchView) -> ActionPolicy:
    row = _exact_object(raw, _ACTION_FIELDS, label=f"action {view.action_id}")
    if row["action_id"] != view.action_id:
        raise CosetPolicyError("coset action policy is bound to the wrong action_id")
    quota = _strict_int(
        row["quota"],
        label=f"action {view.action_id} quota",
        minimum=1,
        maximum=MAX_GENERATED_CANDIDATES,
    )
    include_published = _strict_bool(
        row["include_published"],
        label=f"action {view.action_id} include_published",
    )
    published = _published_candidate(view)
    if include_published and published is None:
        raise CosetPolicyError(
            f"action {view.action_id} has no published support to include"
        )
    supports_raw = row["supports"]
    if type(supports_raw) is not list:
        raise CosetPolicyError(f"action {view.action_id} supports must be a JSON list")
    if len(supports_raw) > MAX_EXPLICIT_SUPPORTS_PER_ACTION:
        raise CosetPolicyError(
            f"action {view.action_id} explicit support cap exceeded"
        )
    supports = tuple(
        _support_declaration(item, view=view, index=index)
        for index, item in enumerate(supports_raw)
    )
    supports = tuple(sorted(supports, key=lambda item: (item.left, item.right)))
    support_keys = {(item.left, item.right) for item in supports}
    if len(support_keys) != len(supports):
        raise CosetPolicyError(f"action {view.action_id} contains duplicate supports")
    if published is not None and include_published:
        if candidate_digest(published) in {
            candidate_digest(_candidate_from_declaration(view, item))
            for item in supports
        }:
            raise CosetPolicyError(
                f"action {view.action_id} repeats its published support"
            )
    walk = _walk(row["walk"], view=view)
    anchor_count = len(supports) + int(include_published)
    if anchor_count > quota:
        raise CosetPolicyError(
            f"action {view.action_id} declares more anchors than its quota"
        )
    if not walk.enabled and anchor_count != quota:
        raise CosetPolicyError(
            f"action {view.action_id} needs an enabled walk to fill its quota"
        )
    return ActionPolicy(
        action_id=view.action_id,
        quota=quota,
        include_published=include_published,
        supports=supports,
        walk=walk,
    )


def normalize_policy(document: Any) -> CosetPolicy:
    """Validate a built-in JSON object and return immutable typed data."""

    _require_declarative_json(document)
    root = _exact_object(document, _ROOT_FIELDS, label="coset policy")
    if root["schema_version"] != POLICY_SCHEMA_VERSION:
        raise CosetPolicyError("coset policy schema_version is incompatible")
    if root["kind"] != POLICY_KIND:
        raise CosetPolicyError("coset policy kind is incompatible")
    if root["representation_id"] != COSET_REPRESENTATION_ID:
        raise CosetPolicyError("coset policy representation_id is incompatible")
    if root["renderer"] != RENDERER_KIND:
        raise CosetPolicyError("coset policy renderer is incompatible")
    if root["support_split"] != [
        PRODUCTION_LEFT_WEIGHT,
        PRODUCTION_RIGHT_WEIGHT,
    ]:
        raise CosetPolicyError("coset policy support_split must be exactly [3, 3]")
    catalog_sha256 = _catalog_sha256()
    if root["action_catalog_sha256"] != catalog_sha256:
        raise CosetPolicyError("coset policy action catalog binding changed")
    candidate_limit = _strict_int(
        root["candidate_limit"],
        label="candidate_limit",
        minimum=REQUIRED_ACTION_VIEW_COUNT,
        maximum=MAX_GENERATED_CANDIDATES,
    )

    actions_raw = root["actions"]
    if type(actions_raw) is not list:
        raise CosetPolicyError("coset policy actions must be a JSON list")
    if len(actions_raw) != REQUIRED_ACTION_VIEW_COUNT:
        raise CosetPolicyError("coset policy must declare exactly two action lanes")
    views = _views_by_id()
    action_rows: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(actions_raw):
        if type(raw) is not dict:
            raise CosetPolicyError(f"coset action {index} must be a JSON object")
        action_id = raw.get("action_id")
        if type(action_id) is not str or action_id not in views:
            raise CosetPolicyError(f"unknown coset action_id: {action_id!r}")
        if action_id in action_rows:
            raise CosetPolicyError(f"duplicate coset action_id: {action_id}")
        action_rows[action_id] = raw
    if set(action_rows) != set(views):
        raise CosetPolicyError("coset policy does not cover the exact action catalog")

    actions = tuple(
        _action_policy(action_rows[action_id], view=views[action_id])
        for action_id in sorted(views)
    )
    if sum(action.quota for action in actions) != candidate_limit:
        raise CosetPolicyError("candidate_limit must equal the sum of action quotas")
    if sum(len(action.supports) for action in actions) > MAX_TOTAL_EXPLICIT_SUPPORTS:
        raise CosetPolicyError("total explicit support cap exceeded")
    return CosetPolicy(
        action_catalog_sha256=catalog_sha256,
        candidate_limit=candidate_limit,
        actions=actions,
    )


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CosetPolicyError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise CosetPolicyError(f"non-finite JSON number is forbidden: {value}")


def parse_policy(payload: str | bytes) -> CosetPolicy:
    """Parse a production policy without interpreting any value as code.

    ``normalize_policy`` intentionally remains usable for bounded historical
    migrations and trusted test helpers.  Text entering through this untrusted
    boundary has the narrower production contract: the renderer must receive
    the full fixed-size portfolio, the catalog-derived lane quotas, and the
    immutable published-anchor selection.
    """

    if type(payload) is bytes:
        encoded = payload
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise CosetPolicyError("coset policy is not valid UTF-8") from exc
    elif type(payload) is str:
        text = payload
        try:
            encoded = payload.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise CosetPolicyError("coset policy is not valid Unicode") from exc
    else:
        raise CosetPolicyError("coset policy payload must be JSON text or bytes")
    if not encoded or len(encoded) > MAX_POLICY_BYTES:
        raise CosetPolicyError(
            f"coset policy payload must contain 1..{MAX_POLICY_BYTES} bytes"
        )
    try:
        document = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
        )
    except CosetPolicyError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise CosetPolicyError(f"coset policy is not strict JSON: {exc}") from exc
    try:
        policy = normalize_policy(document)
    except CosetPolicyError:
        raise
    except RecursionError as exc:
        raise CosetPolicyError("coset policy nesting exceeds the JSON cap") from exc

    if policy.candidate_limit != MAX_GENERATED_CANDIDATES:
        raise CosetPolicyError(
            "production coset policy candidate_limit must be exactly "
            f"{MAX_GENERATED_CANDIDATES}"
        )
    views = _views_by_id()
    expected_quotas = quota_by_normality(
        tuple(views[action_id] for action_id in sorted(views)),
        MAX_GENERATED_CANDIDATES,
    )
    for action in policy.actions:
        expected_quota = expected_quotas[action.action_id]
        if action.quota != expected_quota:
            raise CosetPolicyError(
                f"production action {action.action_id} quota must be exactly "
                f"{expected_quota}"
            )
        expected_published = _published_candidate(views[action.action_id]) is not None
        if action.include_published is not expected_published:
            raise CosetPolicyError(
                f"production action {action.action_id} include_published must be "
                f"exactly {str(expected_published).lower()}"
            )
    return policy


def _policy_document_unchecked(policy: CosetPolicy) -> dict[str, Any]:
    if type(policy) is not CosetPolicy:
        raise CosetPolicyError("policy_document requires a validated CosetPolicy")
    if (
        type(policy.actions) is not tuple
        or any(type(action) is not ActionPolicy for action in policy.actions)
        or any(type(action.supports) is not tuple for action in policy.actions)
        or any(type(action.walk) is not PairWalk for action in policy.actions)
        or any(
            type(support) is not SupportDeclaration
            for action in policy.actions
            for support in action.supports
        )
    ):
        raise CosetPolicyError("typed coset policy contains an invalid object")
    return {
        "schema_version": POLICY_SCHEMA_VERSION,
        "kind": POLICY_KIND,
        "representation_id": COSET_REPRESENTATION_ID,
        "action_catalog_sha256": policy.action_catalog_sha256,
        "renderer": RENDERER_KIND,
        "support_split": [PRODUCTION_LEFT_WEIGHT, PRODUCTION_RIGHT_WEIGHT],
        "candidate_limit": policy.candidate_limit,
        "actions": [
            {
                "action_id": action.action_id,
                "quota": action.quota,
                "include_published": action.include_published,
                "supports": [
                    {"left": list(item.left), "right": list(item.right)}
                    for item in action.supports
                ],
                "walk": {
                    "enabled": action.walk.enabled,
                    "offset": action.walk.offset,
                    "stride": action.walk.stride,
                },
            }
            for action in policy.actions
        ],
    }


def policy_document(policy: CosetPolicy) -> dict[str, Any]:
    """Return the one canonical JSON-compatible representation of a policy."""

    document = _policy_document_unchecked(policy)
    if normalize_policy(document) != policy:
        raise CosetPolicyError("typed coset policy is not in canonical validated form")
    return document


def canonical_policy_json(policy: CosetPolicy) -> str:
    """Render normalized policy data to deterministic canonical JSON."""

    return json.dumps(
        policy_document(policy),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def policy_digest(policy: CosetPolicy) -> str:
    """Return the SHA-256 identity of the canonical policy document."""

    return canonical_json_sha256(policy_document(policy))


def _pair_at(elements: tuple[str, ...], index: int) -> tuple[str, str]:
    """Return a lexicographic two-combination without materializing all pairs."""

    remaining = index
    for left_index in range(len(elements) - 1):
        row_size = len(elements) - left_index - 1
        if remaining < row_size:
            return elements[left_index], elements[left_index + 1 + remaining]
        remaining -= row_size
    raise CosetPolicyError("pair-walk index escaped the catalog pair space")


def _render_action(
    policy: ActionPolicy,
    view: ActionSearchView,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()

    def add(candidate: dict[str, Any]) -> None:
        digest = candidate_digest(candidate)
        if digest not in seen:
            seen.add(digest)
            rows.append(candidate)

    if policy.include_published:
        published = _published_candidate(view)
        if published is None:  # Defensive replay check after validation.
            raise CosetPolicyError(
                f"action {view.action_id} lost its published support"
            )
        add(published)
    for support in policy.supports:
        add(_candidate_from_declaration(view, support))

    if policy.walk.enabled and len(rows) < policy.quota:
        left, right, pair_space = _pair_space(view)
        right_pairs = comb(len(right), 2)
        cursor = policy.walk.offset
        for _ in range(pair_space):
            left_index, right_index = divmod(cursor, right_pairs)
            left_pair = _pair_at(left, left_index)
            right_pair = _pair_at(right, right_index)
            add(_candidate(
                view,
                (view.left_identity_id, *left_pair),
                (view.right_identity_id, *right_pair),
            ))
            if len(rows) == policy.quota:
                break
            cursor = (cursor + policy.walk.stride) % pair_space
    if len(rows) != policy.quota:
        raise CosetPolicyError(
            f"action {view.action_id} rendered {len(rows)} rows, expected {policy.quota}"
        )
    return rows


def render_candidates(policy: CosetPolicy) -> list[dict[str, Any]]:
    """Deterministically render exact catalog-bound 3+3 candidates."""

    if type(policy) is not CosetPolicy:
        raise CosetPolicyError("render_candidates requires a validated CosetPolicy")
    if policy.action_catalog_sha256 != _catalog_sha256():
        raise CosetPolicyError("coset action catalog changed after policy validation")
    # Frozen dataclasses are public value types; replay the exact JSON schema
    # here so manually constructed instances cannot bypass parser invariants.
    policy_document(policy)
    views = _views_by_id()
    lanes = {
        action.action_id: _render_action(action, views[action.action_id])
        for action in policy.actions
    }
    output: list[dict[str, Any]] = []
    ordered_ids = [action.action_id for action in policy.actions]
    for offset in range(max(map(len, lanes.values()), default=0)):
        for action_id in ordered_ids:
            lane = lanes[action_id]
            if offset < len(lane):
                output.append(lane[offset])
    if len(output) != policy.candidate_limit:
        raise CosetPolicyError("trusted renderer violated the candidate cap")
    if len({candidate_digest(item) for item in output}) != len(output):
        raise CosetPolicyError("trusted renderer produced duplicate candidates")
    return output


def render_candidate_jsonl(policy: CosetPolicy) -> str:
    """Render candidates as canonical JSONL with one final newline."""

    return "".join(
        json.dumps(
            row,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ) + "\n"
        for row in render_candidates(policy)
    )


def policy_from_candidates(rows: list[dict[str, Any]] | tuple[dict[str, Any], ...]) -> CosetPolicy:
    """Canonicalize an exact normalized candidate set into a no-walk policy.

    This is the migration lane for existing checkpoint programs.  Duplicate
    candidates are removed by their contract digest, every remaining support
    is encoded as four compact nonidentity catalog indices, and rendering the
    returned policy reproduces the exact candidate set without executing the
    source program that originally produced it.
    """

    if type(rows) not in {list, tuple}:
        raise CosetPolicyError("candidate migration input must be a list or tuple")
    if not rows or len(rows) > MAX_GENERATED_CANDIDATES:
        raise CosetPolicyError(
            f"candidate migration input must contain 1..{MAX_GENERATED_CANDIDATES} rows"
        )
    views = _views_by_id()
    unique: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(rows):
        if type(raw) is not dict:
            raise CosetPolicyError(f"candidate migration row {index} is not an object")
        _require_declarative_json(raw, label=f"candidate migration row {index}")
        try:
            normalized = normalize_candidate(raw)
        except (TypeError, ValueError) as exc:
            raise CosetPolicyError(
                f"candidate migration row {index} violates the coset contract: {exc}"
            ) from exc
        if raw != normalized:
            raise CosetPolicyError(
                f"candidate migration row {index} is not already normalized"
            )
        unique.setdefault(candidate_digest(normalized), normalized)

    declarations: dict[str, set[SupportDeclaration]] = {
        action_id: set() for action_id in views
    }
    for candidate in unique.values():
        action_id = candidate["action_id"]
        view = views[action_id]
        left_elements, right_elements, _ = _pair_space(view)
        left_index = {element: index for index, element in enumerate(left_elements)}
        right_index = {element: index for index, element in enumerate(right_elements)}
        left = tuple(
            left_index[element]
            for element in candidate["left_support"]
            if element != view.left_identity_id
        )
        right = tuple(
            right_index[element]
            for element in candidate["right_support"]
            if element != view.right_identity_id
        )
        if len(left) != 2 or len(right) != 2:
            raise CosetPolicyError("candidate migration escaped the production 3+3 split")
        declarations[action_id].add(SupportDeclaration(
            left=(left[0], left[1]),
            right=(right[0], right[1]),
        ))
    if any(not items for items in declarations.values()):
        raise CosetPolicyError(
            "candidate migration must cover both source-bound action lanes"
        )
    candidate_limit = sum(len(items) for items in declarations.values())
    if candidate_limit != len(unique):
        raise CosetPolicyError("candidate migration changed the candidate identity set")
    policy = CosetPolicy(
        action_catalog_sha256=_catalog_sha256(),
        candidate_limit=candidate_limit,
        actions=tuple(
            ActionPolicy(
                action_id=action_id,
                quota=len(declarations[action_id]),
                include_published=False,
                supports=tuple(sorted(
                    declarations[action_id],
                    key=lambda item: (item.left, item.right),
                )),
                walk=PairWalk(enabled=False, offset=0, stride=1),
            )
            for action_id in sorted(views)
        ),
    )
    # Replay through the public exact-schema validator.  This also guarantees
    # the emitted policy remains JSON-only if these dataclasses evolve.
    validated = normalize_policy(policy_document(policy))
    if {
        candidate_digest(item) for item in render_candidates(validated)
    } != set(unique):
        raise CosetPolicyError("candidate migration replay changed the candidate set")
    return validated


def _default_walk(view: ActionSearchView) -> PairWalk:
    _, _, pair_space = _pair_space(view)
    seed = int(canonical_json_sha256({
        "policy_kind": POLICY_KIND,
        "renderer": RENDERER_KIND,
        "action_catalog_sha256": _catalog_sha256(),
        "action_id": view.action_id,
    })[:16], 16)
    offset = seed % pair_space
    stride = 2 * (seed % max(1, pair_space // 2)) + 1
    while stride >= pair_space or gcd(stride, pair_space) != 1:
        stride = (stride + 2) % pair_space
        if stride == 0:
            stride = 1
    return PairWalk(enabled=True, offset=offset, stride=stride)


def default_policy(candidate_limit: int = MAX_GENERATED_CANDIDATES) -> CosetPolicy:
    """Build the deterministic two-lane baseline policy for the current catalog."""

    candidate_limit = _strict_int(
        candidate_limit,
        label="candidate_limit",
        minimum=REQUIRED_ACTION_VIEW_COUNT,
        maximum=MAX_GENERATED_CANDIDATES,
    )
    views_by_id = _views_by_id()
    views = tuple(views_by_id[key] for key in sorted(views_by_id))
    quotas = quota_by_normality(views, candidate_limit)
    policy = CosetPolicy(
        action_catalog_sha256=_catalog_sha256(),
        candidate_limit=candidate_limit,
        actions=tuple(
            ActionPolicy(
                action_id=view.action_id,
                quota=quotas[view.action_id],
                include_published=_published_candidate(view) is not None,
                supports=(),
                walk=_default_walk(view),
            )
            for view in views
        ),
    )
    return normalize_policy(_policy_document_unchecked(policy))


__all__ = [
    "ActionPolicy",
    "CosetPolicy",
    "CosetPolicyError",
    "MAX_ACTION_POLICIES",
    "MAX_EXPLICIT_SUPPORTS_PER_ACTION",
    "MAX_PAIR_SPACE",
    "MAX_POLICY_BYTES",
    "MAX_TOTAL_EXPLICIT_SUPPORTS",
    "POLICY_KIND",
    "POLICY_SCHEMA_VERSION",
    "PairWalk",
    "RENDERER_KIND",
    "REQUIRED_ACTION_VIEW_COUNT",
    "SupportDeclaration",
    "canonical_policy_json",
    "default_policy",
    "normalize_policy",
    "parse_policy",
    "policy_digest",
    "policy_document",
    "policy_from_candidates",
    "render_candidate_jsonl",
    "render_candidates",
]
