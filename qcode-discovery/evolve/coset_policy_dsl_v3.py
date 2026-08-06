"""Versioned, data-only renderer for catalog-bound coset support search.

Renderer v3 expands the trusted support vocabulary without expanding the
execution vocabulary.  An evolved program remains strict JSON and can select
only one source-registered descriptor, one of five support splits, catalog
action IDs, integer support indices, and bounded integer walk parameters.
Identity elements, catalog objects, combination unranking, candidate schemas,
deduplication, and output ordering remain trusted source code.

There is deliberately no ``eval``, ``exec``, dynamic import, module name,
callable, Python expression, or code template in this language.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from math import comb, gcd
from typing import Any, Mapping, Sequence

from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION_V3,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID_V3,
    MAX_GENERATED_CANDIDATES,
    TRUSTED_COSET_SUPPORT_SPLITS,
    ActionSearchView,
    action_search_view,
    action_search_views,
    canonical_json_sha256,
    coset_candidate_digest,
    normalize_coset_candidate,
    quota_by_normality,
    trusted_coset_renderer_descriptor_document,
    trusted_coset_renderer_registry_document,
)


POLICY_SCHEMA_VERSION = 3
POLICY_KIND = "qcode-coset-policy-dsl-v3"
RENDERER_DESCRIPTOR_ID = COSET_RENDERER_V3_ID
REQUIRED_ACTION_VIEW_COUNT = 46
MAX_POLICY_BYTES = 262_144
MAX_ACTION_POLICIES = 64
MAX_EXPLICIT_SUPPORTS_PER_ACTION = MAX_GENERATED_CANDIDATES
MAX_TOTAL_EXPLICIT_SUPPORTS = MAX_GENERATED_CANDIDATES
MAX_COMBINATION_SPACE = (1 << 63) - 1

_ROOT_FIELDS = frozenset({
    "schema_version",
    "kind",
    "representation_id",
    "renderer_descriptor_id",
    "renderer_descriptor_sha256",
    "renderer_registry_sha256",
    "catalog_kind",
    "action_catalog_id",
    "action_catalog_sha256",
    "support_split",
    "candidate_limit",
    "actions",
})
_ACTION_FIELDS = frozenset({"action_id", "quota", "supports", "walk"})
_SUPPORT_FIELDS = frozenset({"left", "right"})
_WALK_FIELDS = frozenset({"enabled", "offset", "stride"})


class CosetPolicyV3Error(ValueError):
    """The supplied value is not a valid renderer-v3 policy."""


@dataclass(frozen=True, slots=True)
class SupportDeclaration:
    left: tuple[int, ...]
    right: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class CombinationWalk:
    enabled: bool
    offset: int
    stride: int


@dataclass(frozen=True, slots=True)
class ActionPolicy:
    action_id: str
    quota: int
    supports: tuple[SupportDeclaration, ...]
    walk: CombinationWalk


@dataclass(frozen=True, slots=True)
class CosetPolicyV3:
    renderer_descriptor_sha256: str
    renderer_registry_sha256: str
    action_catalog_id: str
    action_catalog_sha256: str
    support_split: tuple[int, int]
    candidate_limit: int
    actions: tuple[ActionPolicy, ...]


def _descriptor() -> dict[str, Any]:
    value = trusted_coset_renderer_descriptor_document(RENDERER_DESCRIPTOR_ID)
    if (
        value.get("policy_schema_version") != POLICY_SCHEMA_VERSION
        or value.get("candidate_schema_version")
        != COSET_CANDIDATE_SCHEMA_VERSION_V3
        or value.get("representation_id") != COSET_REPRESENTATION_ID_V3
        or value.get("catalog_kind") != "action"
        or value.get("support_splits")
        != [list(split) for split in TRUSTED_COSET_SUPPORT_SPLITS]
    ):
        raise CosetPolicyV3Error("trusted renderer descriptor changed")
    return value


def _registry_sha256() -> str:
    value = trusted_coset_renderer_registry_document().get("registry_sha256")
    if not _valid_sha256(value):
        raise CosetPolicyV3Error("trusted renderer registry identity is invalid")
    return str(value)


def _valid_sha256(value: Any) -> bool:
    return (
        type(value) is str
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _views_by_id() -> dict[str, ActionSearchView]:
    views = action_search_views()
    if len(views) != REQUIRED_ACTION_VIEW_COUNT:
        raise CosetPolicyV3Error(
            "renderer v3 requires exactly 46 source-bound action views"
        )
    if len(views) > MAX_ACTION_POLICIES:
        raise CosetPolicyV3Error("action view count exceeds the renderer cap")
    return {view.action_id: view for view in views}


def _exact_object(
    value: Any,
    fields: frozenset[str],
    *,
    label: str,
) -> dict[str, Any]:
    if type(value) is not dict:
        raise CosetPolicyV3Error(f"{label} must be a JSON object")
    observed = set(value)
    if observed != fields:
        raise CosetPolicyV3Error(
            f"{label} fields are not exact; "
            f"missing={sorted(fields - observed)}, "
            f"unknown={sorted(observed - fields)}"
        )
    return value


def _require_declarative_json(value: Any, *, label: str = "policy") -> None:
    if type(value) in {str, int, bool}:
        return
    if type(value) is list:
        for index, item in enumerate(value):
            _require_declarative_json(item, label=f"{label}[{index}]")
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise CosetPolicyV3Error(f"{label} has a non-string key")
            _require_declarative_json(item, label=f"{label}.{key}")
        return
    raise CosetPolicyV3Error(
        f"{label} must contain only inert built-in JSON values"
    )


def _strict_int(
    value: Any,
    *,
    label: str,
    minimum: int,
    maximum: int,
) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise CosetPolicyV3Error(
            f"{label} must be an integer in [{minimum}, {maximum}]"
        )
    return value


def _support_split(value: Any) -> tuple[int, int]:
    if (
        type(value) is not list
        or len(value) != 2
        or any(type(item) is not int for item in value)
    ):
        raise CosetPolicyV3Error("support_split must be a two-integer JSON list")
    result = (value[0], value[1])
    if result not in TRUSTED_COSET_SUPPORT_SPLITS:
        raise CosetPolicyV3Error("support_split is not renderer-whitelisted")
    return result


def _nonidentity(view: ActionSearchView, side: str) -> tuple[str, ...]:
    if side == "left":
        values = view.left_element_ids
        identity = view.left_identity_id
    elif side == "right":
        values = view.right_element_ids
        identity = view.right_identity_id
    else:  # Trusted internal call only.
        raise AssertionError("unknown support side")
    return tuple(item for item in values if item != identity)


def _combination_space(
    view: ActionSearchView,
    split: tuple[int, int],
) -> tuple[tuple[str, ...], tuple[str, ...], int]:
    left = _nonidentity(view, "left")
    right = _nonidentity(view, "right")
    left_choose = split[0] - 1
    right_choose = split[1] - 1
    if len(left) < left_choose or len(right) < right_choose:
        raise CosetPolicyV3Error(
            f"action {view.action_id} cannot provide support split "
            f"{split[0]}+{split[1]}"
        )
    size = comb(len(left), left_choose) * comb(len(right), right_choose)
    if not 1 <= size <= MAX_COMBINATION_SPACE:
        raise CosetPolicyV3Error(
            f"action {view.action_id} combination space exceeds the cap"
        )
    return left, right, size


def _candidate(
    view: ActionSearchView,
    split: tuple[int, int],
    left: Sequence[str],
    right: Sequence[str],
) -> dict[str, Any]:
    return normalize_coset_candidate({
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION_V3,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": RENDERER_DESCRIPTOR_ID,
        "action_id": view.action_id,
        "support_split": list(split),
        "left_support": list(left),
        "right_support": list(right),
    })


def _published_candidate(
    view: ActionSearchView,
    split: tuple[int, int],
) -> dict[str, Any] | None:
    left = view.published_left_support
    right = view.published_right_support
    if left is None or right is None or (len(left), len(right)) != split:
        return None
    return _candidate(view, split, left, right)


def _support_declaration(
    raw: Any,
    *,
    view: ActionSearchView,
    split: tuple[int, int],
    index: int,
) -> SupportDeclaration:
    row = _exact_object(
        raw,
        _SUPPORT_FIELDS,
        label=f"action {view.action_id} support {index}",
    )
    left_indices = row["left"]
    right_indices = row["right"]
    required = (split[0] - 1, split[1] - 1)
    if (
        type(left_indices) is not list
        or type(right_indices) is not list
        or (len(left_indices), len(right_indices)) != required
    ):
        raise CosetPolicyV3Error(
            "support indices do not match the selected support_split"
        )
    if any(type(item) is not int for item in (*left_indices, *right_indices)):
        raise CosetPolicyV3Error("support indices must be integers")
    left_elements, right_elements, _ = _combination_space(view, split)
    if (
        len(set(left_indices)) != len(left_indices)
        or len(set(right_indices)) != len(right_indices)
        or any(not 0 <= item < len(left_elements) for item in left_indices)
        or any(not 0 <= item < len(right_elements) for item in right_indices)
    ):
        raise CosetPolicyV3Error("support indices are duplicate or out of range")
    left_tuple = tuple(sorted(left_indices))
    right_tuple = tuple(sorted(right_indices))
    try:
        _candidate_from_declaration(
            view,
            split,
            SupportDeclaration(left=left_tuple, right=right_tuple),
        )
    except (TypeError, ValueError) as exc:
        raise CosetPolicyV3Error(
            f"action {view.action_id} support {index} is invalid: {exc}"
        ) from exc
    return SupportDeclaration(left=left_tuple, right=right_tuple)


def _candidate_from_declaration(
    view: ActionSearchView,
    split: tuple[int, int],
    support: SupportDeclaration,
) -> dict[str, Any]:
    left = _nonidentity(view, "left")
    right = _nonidentity(view, "right")
    return _candidate(
        view,
        split,
        (view.left_identity_id, *(left[index] for index in support.left)),
        (view.right_identity_id, *(right[index] for index in support.right)),
    )


def _walk(
    raw: Any,
    *,
    view: ActionSearchView,
    split: tuple[int, int],
) -> CombinationWalk:
    row = _exact_object(raw, _WALK_FIELDS, label=f"action {view.action_id} walk")
    if type(row["enabled"]) is not bool:
        raise CosetPolicyV3Error("walk.enabled must be a boolean")
    _left, _right, space = _combination_space(view, split)
    if not row["enabled"]:
        if row["offset"] != 0 or row["stride"] != 1:
            raise CosetPolicyV3Error(
                "a disabled walk must use canonical offset=0 and stride=1"
            )
        return CombinationWalk(enabled=False, offset=0, stride=1)
    offset = _strict_int(
        row["offset"], label="walk.offset", minimum=0, maximum=space - 1
    )
    stride = _strict_int(
        row["stride"], label="walk.stride", minimum=1, maximum=space - 1
    )
    if gcd(stride, space) != 1:
        raise CosetPolicyV3Error(
            f"action {view.action_id} walk.stride must be coprime to its space"
        )
    return CombinationWalk(enabled=True, offset=offset, stride=stride)


def _anchor_digests(
    action: ActionPolicy,
    view: ActionSearchView,
    split: tuple[int, int],
) -> set[str]:
    result: set[str] = set()
    published = _published_candidate(view, split)
    if published is not None:
        result.add(coset_candidate_digest(published))
    for support in action.supports:
        result.add(coset_candidate_digest(
            _candidate_from_declaration(view, split, support)
        ))
    return result


def _action_policy(
    raw: Any,
    *,
    view: ActionSearchView,
    split: tuple[int, int],
) -> ActionPolicy:
    row = _exact_object(raw, _ACTION_FIELDS, label=f"action {view.action_id}")
    if row["action_id"] != view.action_id:
        raise CosetPolicyV3Error("action policy is bound to the wrong action_id")
    quota = _strict_int(
        row["quota"],
        label=f"action {view.action_id} quota",
        minimum=1,
        maximum=MAX_GENERATED_CANDIDATES,
    )
    if type(row["supports"]) is not list:
        raise CosetPolicyV3Error("action supports must be a JSON list")
    if len(row["supports"]) > MAX_EXPLICIT_SUPPORTS_PER_ACTION:
        raise CosetPolicyV3Error("action explicit support cap exceeded")
    supports = tuple(sorted(
        (
            _support_declaration(item, view=view, split=split, index=index)
            for index, item in enumerate(row["supports"])
        ),
        key=lambda item: (item.left, item.right),
    ))
    if len({(item.left, item.right) for item in supports}) != len(supports):
        raise CosetPolicyV3Error("action contains duplicate supports")
    walk = _walk(row["walk"], view=view, split=split)
    action = ActionPolicy(
        action_id=view.action_id,
        quota=quota,
        supports=supports,
        walk=walk,
    )
    anchor_count = len(_anchor_digests(action, view, split))
    if anchor_count > quota:
        raise CosetPolicyV3Error("action declares more unique anchors than quota")
    if not walk.enabled and anchor_count != quota:
        raise CosetPolicyV3Error(
            "action needs an enabled walk to fill its quota"
        )
    return action


def normalize_policy(document: Any) -> CosetPolicyV3:
    _require_declarative_json(document)
    root = _exact_object(document, _ROOT_FIELDS, label="coset v3 policy")
    descriptor = _descriptor()
    registry_sha256 = _registry_sha256()
    exact_bindings = {
        "schema_version": POLICY_SCHEMA_VERSION,
        "kind": POLICY_KIND,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": RENDERER_DESCRIPTOR_ID,
        "renderer_descriptor_sha256": descriptor["descriptor_sha256"],
        "renderer_registry_sha256": registry_sha256,
        "catalog_kind": "action",
        "action_catalog_id": descriptor["catalog_id"],
        "action_catalog_sha256": descriptor["catalog_sha256"],
    }
    for field, expected in exact_bindings.items():
        if root[field] != expected:
            raise CosetPolicyV3Error(f"coset v3 policy {field} changed")
    split = _support_split(root["support_split"])
    candidate_limit = _strict_int(
        root["candidate_limit"],
        label="candidate_limit",
        minimum=REQUIRED_ACTION_VIEW_COUNT,
        maximum=MAX_GENERATED_CANDIDATES,
    )
    if type(root["actions"]) is not list:
        raise CosetPolicyV3Error("actions must be a JSON list")
    if len(root["actions"]) != REQUIRED_ACTION_VIEW_COUNT:
        raise CosetPolicyV3Error("policy must declare exactly 46 action lanes")
    views = _views_by_id()
    action_rows: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(root["actions"]):
        if type(raw) is not dict:
            raise CosetPolicyV3Error(f"action {index} must be a JSON object")
        action_id = raw.get("action_id")
        if type(action_id) is not str or action_id not in views:
            raise CosetPolicyV3Error(f"unknown action_id: {action_id!r}")
        if action_id in action_rows:
            raise CosetPolicyV3Error(f"duplicate action_id: {action_id}")
        action_rows[action_id] = raw
    if set(action_rows) != set(views):
        raise CosetPolicyV3Error("policy does not cover the exact action catalog")
    actions = tuple(
        _action_policy(action_rows[action_id], view=views[action_id], split=split)
        for action_id in sorted(views)
    )
    if sum(action.quota for action in actions) != candidate_limit:
        raise CosetPolicyV3Error("candidate_limit disagrees with action quotas")
    if sum(len(action.supports) for action in actions) > (
        MAX_TOTAL_EXPLICIT_SUPPORTS
    ):
        raise CosetPolicyV3Error("total explicit support cap exceeded")
    return CosetPolicyV3(
        renderer_descriptor_sha256=descriptor["descriptor_sha256"],
        renderer_registry_sha256=registry_sha256,
        action_catalog_id=descriptor["catalog_id"],
        action_catalog_sha256=descriptor["catalog_sha256"],
        support_split=split,
        candidate_limit=candidate_limit,
        actions=actions,
    )


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CosetPolicyV3Error(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise CosetPolicyV3Error(f"non-finite JSON number is forbidden: {value}")


def parse_policy(payload: str | bytes) -> CosetPolicyV3:
    if type(payload) is bytes:
        encoded = payload
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise CosetPolicyV3Error("policy is not valid UTF-8") from exc
    elif type(payload) is str:
        text = payload
        try:
            encoded = payload.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise CosetPolicyV3Error("policy is not valid Unicode") from exc
    else:
        raise CosetPolicyV3Error("policy payload must be JSON text or bytes")
    if not encoded or len(encoded) > MAX_POLICY_BYTES:
        raise CosetPolicyV3Error(
            f"policy payload must contain 1..{MAX_POLICY_BYTES} bytes"
        )
    try:
        document = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
        )
    except CosetPolicyV3Error:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise CosetPolicyV3Error(f"policy is not strict JSON: {exc}") from exc
    policy = normalize_policy(document)
    if policy.candidate_limit != MAX_GENERATED_CANDIDATES:
        raise CosetPolicyV3Error(
            f"production candidate_limit must be exactly {MAX_GENERATED_CANDIDATES}"
        )
    views = _views_by_id()
    expected = quota_by_normality(
        tuple(views[action_id] for action_id in sorted(views)),
        MAX_GENERATED_CANDIDATES,
    )
    for action in policy.actions:
        if action.quota != expected[action.action_id]:
            raise CosetPolicyV3Error(
                f"production action {action.action_id} quota changed"
            )
    return policy


def _policy_document_unchecked(policy: CosetPolicyV3) -> dict[str, Any]:
    if type(policy) is not CosetPolicyV3:
        raise CosetPolicyV3Error("policy_document requires CosetPolicyV3")
    return {
        "schema_version": POLICY_SCHEMA_VERSION,
        "kind": POLICY_KIND,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": RENDERER_DESCRIPTOR_ID,
        "renderer_descriptor_sha256": policy.renderer_descriptor_sha256,
        "renderer_registry_sha256": policy.renderer_registry_sha256,
        "catalog_kind": "action",
        "action_catalog_id": policy.action_catalog_id,
        "action_catalog_sha256": policy.action_catalog_sha256,
        "support_split": list(policy.support_split),
        "candidate_limit": policy.candidate_limit,
        "actions": [
            {
                "action_id": action.action_id,
                "quota": action.quota,
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


def policy_document(policy: CosetPolicyV3) -> dict[str, Any]:
    document = _policy_document_unchecked(policy)
    if normalize_policy(document) != policy:
        raise CosetPolicyV3Error("typed policy is not canonical and valid")
    return document


def canonical_policy_json(policy: CosetPolicyV3) -> str:
    return json.dumps(
        policy_document(policy),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def policy_digest(policy: CosetPolicyV3) -> str:
    return canonical_json_sha256(policy_document(policy))


def _combination_at(
    elements: tuple[str, ...],
    choose: int,
    index: int,
) -> tuple[str, ...]:
    """Unrank a lexicographic combination without materializing its space."""

    if not 0 <= index < comb(len(elements), choose):
        raise CosetPolicyV3Error("combination-walk index escaped its space")
    result: list[str] = []
    cursor = 0
    remaining_index = index
    for position in range(choose):
        remaining_slots = choose - position - 1
        last = len(elements) - remaining_slots
        for candidate_index in range(cursor, last):
            suffixes = comb(
                len(elements) - candidate_index - 1,
                remaining_slots,
            )
            if remaining_index < suffixes:
                result.append(elements[candidate_index])
                cursor = candidate_index + 1
                break
            remaining_index -= suffixes
        else:  # pragma: no cover - guarded by the exact range check.
            raise CosetPolicyV3Error("combination unranking was inconsistent")
    return tuple(result)


def _render_action(
    policy: ActionPolicy,
    view: ActionSearchView,
    split: tuple[int, int],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()

    def add(candidate: dict[str, Any]) -> None:
        digest = coset_candidate_digest(candidate)
        if digest not in seen:
            seen.add(digest)
            rows.append(candidate)

    published = _published_candidate(view, split)
    if published is not None:
        add(published)
    for support in policy.supports:
        add(_candidate_from_declaration(view, split, support))
    if policy.walk.enabled and len(rows) < policy.quota:
        left, right, space = _combination_space(view, split)
        right_count = comb(len(right), split[1] - 1)
        cursor = policy.walk.offset
        for _ in range(space):
            left_index, right_index = divmod(cursor, right_count)
            left_support = _combination_at(left, split[0] - 1, left_index)
            right_support = _combination_at(right, split[1] - 1, right_index)
            add(_candidate(
                view,
                split,
                (view.left_identity_id, *left_support),
                (view.right_identity_id, *right_support),
            ))
            if len(rows) == policy.quota:
                break
            cursor = (cursor + policy.walk.stride) % space
    if len(rows) != policy.quota:
        raise CosetPolicyV3Error(
            f"action {view.action_id} rendered {len(rows)}, expected {policy.quota}"
        )
    return rows


def render_candidates(policy: CosetPolicyV3) -> list[dict[str, Any]]:
    if type(policy) is not CosetPolicyV3:
        raise CosetPolicyV3Error("render_candidates requires CosetPolicyV3")
    policy_document(policy)
    if policy.renderer_registry_sha256 != _registry_sha256():
        raise CosetPolicyV3Error("renderer registry changed after validation")
    views = _views_by_id()
    lanes = {
        action.action_id: _render_action(
            action,
            views[action.action_id],
            policy.support_split,
        )
        for action in policy.actions
    }
    output: list[dict[str, Any]] = []
    ordered_ids = [action.action_id for action in policy.actions]
    for offset in range(max(map(len, lanes.values()), default=0)):
        for action_id in ordered_ids:
            if offset < len(lanes[action_id]):
                output.append(lanes[action_id][offset])
    if len(output) != policy.candidate_limit:
        raise CosetPolicyV3Error("renderer violated the candidate cap")
    if len({coset_candidate_digest(row) for row in output}) != len(output):
        raise CosetPolicyV3Error("renderer produced duplicate candidates")
    return output


def render_candidate_jsonl(policy: CosetPolicyV3) -> str:
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


def _default_walk(
    view: ActionSearchView,
    split: tuple[int, int],
) -> CombinationWalk:
    _left, _right, space = _combination_space(view, split)
    seed = int.from_bytes(hashlib.sha256(
        (
            RENDERER_DESCRIPTOR_ID
            + "\0"
            + view.action_id
            + "\0"
            + f"{split[0]}+{split[1]}"
        ).encode("utf-8")
    ).digest(), "big")
    offset = seed % space
    stride = (seed // space) % space
    if stride == 0:
        stride = 1
    while gcd(stride, space) != 1:
        stride = 1 if stride == space - 1 else stride + 1
    return CombinationWalk(enabled=True, offset=offset, stride=stride)


def default_policy(
    candidate_limit: int = MAX_GENERATED_CANDIDATES,
    *,
    support_split: tuple[int, int] = (3, 3),
) -> CosetPolicyV3:
    if (
        isinstance(candidate_limit, bool)
        or not isinstance(candidate_limit, int)
        or not REQUIRED_ACTION_VIEW_COUNT
        <= candidate_limit
        <= MAX_GENERATED_CANDIDATES
    ):
        raise CosetPolicyV3Error("default candidate_limit is invalid")
    if support_split not in TRUSTED_COSET_SUPPORT_SPLITS:
        raise CosetPolicyV3Error("default support_split is not whitelisted")
    descriptor = _descriptor()
    views = action_search_views()
    quotas = quota_by_normality(views, candidate_limit)
    policy = CosetPolicyV3(
        renderer_descriptor_sha256=descriptor["descriptor_sha256"],
        renderer_registry_sha256=_registry_sha256(),
        action_catalog_id=descriptor["catalog_id"],
        action_catalog_sha256=descriptor["catalog_sha256"],
        support_split=support_split,
        candidate_limit=candidate_limit,
        actions=tuple(
            ActionPolicy(
                action_id=view.action_id,
                quota=quotas[view.action_id],
                supports=(),
                walk=_default_walk(view, support_split),
            )
            for view in sorted(views, key=lambda item: item.action_id)
        ),
    )
    policy_document(policy)
    return policy


def _v3_candidate_from_any(raw: Mapping[str, Any]) -> dict[str, Any]:
    representation = raw.get("representation_id")
    if representation == COSET_REPRESENTATION_ID_V3:
        return normalize_coset_candidate(raw)
    from evolve.coset_search_contract import (
        COSET_REPRESENTATION_ID,
        normalize_candidate,
    )

    if representation != COSET_REPRESENTATION_ID:
        raise CosetPolicyV3Error("migration candidate representation is unknown")
    legacy = normalize_candidate(raw)
    split = (len(legacy["left_support"]), len(legacy["right_support"]))
    if split not in TRUSTED_COSET_SUPPORT_SPLITS:
        raise CosetPolicyV3Error("migration candidate split is not whitelisted")
    return _candidate(
        action_search_view(legacy["action_id"]),
        split,
        legacy["left_support"],
        legacy["right_support"],
    )


def policy_from_candidates(
    rows: list[dict[str, Any]] | tuple[dict[str, Any], ...],
) -> CosetPolicyV3:
    """Build a no-walk v3 policy from one exact, single-split candidate set."""

    if type(rows) not in {list, tuple} or not rows:
        raise CosetPolicyV3Error("migration rows must be a nonempty list or tuple")
    if len(rows) > MAX_GENERATED_CANDIDATES:
        raise CosetPolicyV3Error("migration candidate cap exceeded")
    normalized = [_v3_candidate_from_any(row) for row in rows]
    split_values = {tuple(row["support_split"]) for row in normalized}
    if len(split_values) != 1:
        raise CosetPolicyV3Error("migration rows must use one support split")
    split = next(iter(split_values))
    by_action: dict[str, dict[str, dict[str, Any]]] = {
        view.action_id: {} for view in action_search_views()
    }
    for row in normalized:
        by_action[row["action_id"]][coset_candidate_digest(row)] = row
    if any(not lane for lane in by_action.values()):
        raise CosetPolicyV3Error("migration rows must cover every action lane")
    actions: list[ActionPolicy] = []
    for action_id in sorted(by_action):
        view = action_search_view(action_id)
        left_index = {
            value: index
            for index, value in enumerate(_nonidentity(view, "left"))
        }
        right_index = {
            value: index
            for index, value in enumerate(_nonidentity(view, "right"))
        }
        supports = []
        for row in sorted(
            by_action[action_id].values(),
            key=coset_candidate_digest,
        ):
            left = tuple(
                left_index[value]
                for value in row["left_support"]
                if value != view.left_identity_id
            )
            right = tuple(
                right_index[value]
                for value in row["right_support"]
                if value != view.right_identity_id
            )
            supports.append(SupportDeclaration(left=left, right=right))
        actions.append(ActionPolicy(
            action_id=action_id,
            quota=len(by_action[action_id]),
            supports=tuple(sorted(supports, key=lambda item: (item.left, item.right))),
            walk=CombinationWalk(enabled=False, offset=0, stride=1),
        ))
    descriptor = _descriptor()
    policy = CosetPolicyV3(
        renderer_descriptor_sha256=descriptor["descriptor_sha256"],
        renderer_registry_sha256=_registry_sha256(),
        action_catalog_id=descriptor["catalog_id"],
        action_catalog_sha256=descriptor["catalog_sha256"],
        support_split=split,
        candidate_limit=sum(action.quota for action in actions),
        actions=tuple(actions),
    )
    policy_document(policy)
    expected = {coset_candidate_digest(row) for row in normalized}
    observed = {coset_candidate_digest(row) for row in render_candidates(policy)}
    if observed != expected:
        raise CosetPolicyV3Error("migration policy did not replay its candidate set")
    return policy


def migrate_v2_policy(payload: str | bytes) -> CosetPolicyV3:
    """Explicitly migrate canonical v2 data; never resume a v2 checkpoint."""

    from evolve import coset_policy_dsl as legacy

    old_policy = legacy.parse_policy(payload)
    old_rows = legacy.render_candidates(old_policy)
    migrated = policy_from_candidates(old_rows)
    if migrated.support_split != (3, 3):
        raise CosetPolicyV3Error("v2 migration changed the fixed 3+3 split")
    return migrated


__all__ = [
    "ActionPolicy",
    "CombinationWalk",
    "CosetPolicyV3",
    "CosetPolicyV3Error",
    "POLICY_KIND",
    "POLICY_SCHEMA_VERSION",
    "RENDERER_DESCRIPTOR_ID",
    "SupportDeclaration",
    "canonical_policy_json",
    "default_policy",
    "migrate_v2_policy",
    "normalize_policy",
    "parse_policy",
    "policy_digest",
    "policy_document",
    "policy_from_candidates",
    "render_candidate_jsonl",
    "render_candidates",
]
