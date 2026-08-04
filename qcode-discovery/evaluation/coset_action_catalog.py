"""Frozen permutation-action catalog for two-block group-algebra codes.

The catalog deliberately contains concrete permutations rather than GAP
objects.  Loading it therefore has no network, subprocess, or optional GAP
dependency.  Generator closures are recomputed deterministically and sorted
lexicographically; the resulting stable element identifiers are the only
identifiers written into canonical candidate claims.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Mapping, Sequence
from copy import deepcopy
from dataclasses import dataclass
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
from types import MappingProxyType
from typing import Any


CATALOG_SCHEMA_VERSION = 1
CATALOG_KIND = "qcode-coset-two-block-action-catalog"
CATALOG_PATH = Path(__file__).with_name("coset_two_block_actions.v1.json")
MAX_ACTION_DEGREE = 512
MAX_CLOSURE_SIZE = 4096

Permutation = tuple[int, ...]


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key in action catalog: {key!r}")
        result[key] = value
    return result


def _require_exact_keys(
    value: Mapping[str, Any], required: set[str], *, where: str
) -> None:
    actual = set(value)
    if actual != required:
        missing = sorted(required - actual)
        unknown = sorted(actual - required)
        raise ValueError(
            f"{where} fields do not match schema; missing={missing}, "
            f"unknown={unknown}"
        )


def _strict_positive_int(value: Any, *, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{where} must be a positive integer")
    return int(value)


def _permutation(value: Any, degree: int, *, where: str) -> Permutation:
    if not isinstance(value, list) or len(value) != degree:
        raise ValueError(f"{where} must be a permutation of degree {degree}")
    if any(isinstance(item, bool) or not isinstance(item, int) for item in value):
        raise ValueError(f"{where} contains a non-integer coordinate")
    result = tuple(int(item) for item in value)
    if tuple(sorted(result)) != tuple(range(degree)):
        raise ValueError(f"{where} is not a bijection on [0, {degree})")
    return result


def compose_permutations(left: Permutation, right: Permutation) -> Permutation:
    """Compose permutations in the frozen row-to-column matrix convention.

    If ``P[p][i, p[i]] = 1``, this returns the permutation represented by
    ``P[left] @ P[right]``.
    """

    if len(left) != len(right):
        raise ValueError("cannot compose permutations of different degrees")
    return tuple(right[index] for index in left)


def inverse_permutation(permutation: Permutation) -> Permutation:
    inverse = [0] * len(permutation)
    for source, destination in enumerate(permutation):
        inverse[destination] = source
    return tuple(inverse)


def _commute(left: Permutation, right: Permutation) -> bool:
    return compose_permutations(left, right) == compose_permutations(right, left)


def _generator_closure(
    identity: Permutation,
    generators: tuple[Permutation, ...],
    *,
    expected_size: int,
    where: str,
) -> tuple[Permutation, ...]:
    """Close frozen generators and return lexicographically sorted elements."""

    discovered = {identity}
    pending: deque[Permutation] = deque([identity])
    while pending:
        current = pending.popleft()
        for generator in generators:
            product = compose_permutations(current, generator)
            if product in discovered:
                continue
            discovered.add(product)
            if len(discovered) > MAX_CLOSURE_SIZE:
                raise ValueError(
                    f"{where} closure exceeds safety limit {MAX_CLOSURE_SIZE}"
                )
            pending.append(product)
    if len(discovered) != expected_size:
        raise ValueError(
            f"{where} closure has {len(discovered)} elements; "
            f"expected {expected_size}"
        )
    return tuple(sorted(discovered))


@dataclass(frozen=True)
class ActionSide:
    """Validated closure of one side of a commuting permutation action."""

    name: str
    elements: tuple[Permutation, ...]
    element_ids: tuple[str, ...]
    id_to_permutation: Mapping[str, Permutation]
    permutation_to_id: Mapping[Permutation, str]
    aliases: Mapping[str, str]
    identity_id: str
    generator_ids: tuple[str, ...]
    expected_abelian: bool

    def resolve(self, element_id_or_alias: str) -> str:
        if element_id_or_alias in self.id_to_permutation:
            return element_id_or_alias
        try:
            return self.aliases[element_id_or_alias]
        except KeyError as exc:
            raise ValueError(
                f"unknown {self.name} action element {element_id_or_alias!r}"
            ) from exc


@dataclass(frozen=True)
class FrozenAction:
    action_id: str
    family: str
    bin_name: str
    block_size: int
    subgroup_normal: bool
    search_enabled: bool
    provenance: Mapping[str, Any]
    published_support: Mapping[str, Any] | None
    published_support_aliases: Mapping[str, Any] | None
    left: ActionSide
    right: ActionSide


def _parse_side(
    raw: Any, *, action_id: str, side_name: str, degree: int
) -> ActionSide:
    if not isinstance(raw, Mapping):
        raise ValueError(f"{action_id}.{side_name} must be a mapping")
    _require_exact_keys(
        raw,
        {
            "stable_id_prefix",
            "expected_closure_size",
            "expected_abelian",
            "identity",
            "generators",
        },
        where=f"{action_id}.{side_name}",
    )
    prefix = raw["stable_id_prefix"]
    if not isinstance(prefix, str) or not prefix or not prefix.isascii():
        raise ValueError(f"{action_id}.{side_name}.stable_id_prefix is invalid")
    expected_size = _strict_positive_int(
        raw["expected_closure_size"],
        where=f"{action_id}.{side_name}.expected_closure_size",
    )
    expected_abelian = raw["expected_abelian"]
    if not isinstance(expected_abelian, bool):
        raise ValueError(f"{action_id}.{side_name}.expected_abelian must be bool")

    def parse_named_permutation(item: Any, where: str) -> tuple[str, Permutation]:
        if not isinstance(item, Mapping):
            raise ValueError(f"{where} must be a mapping")
        _require_exact_keys(
            item,
            {"alias", "paper_index_alias", "upstream_block_alias", "permutation"},
            where=where,
        )
        alias = item["alias"]
        if not isinstance(alias, str) or not alias:
            raise ValueError(f"{where}.alias must be a nonempty string")
        paper_alias = item["paper_index_alias"]
        if paper_alias is not None and (
            isinstance(paper_alias, bool) or not isinstance(paper_alias, int)
        ):
            raise ValueError(f"{where}.paper_index_alias must be int or null")
        upstream_alias = item["upstream_block_alias"]
        if not isinstance(upstream_alias, str) or not upstream_alias:
            raise ValueError(f"{where}.upstream_block_alias must be nonempty")
        return alias, _permutation(item["permutation"], degree, where=where)

    identity_alias, identity = parse_named_permutation(
        raw["identity"], f"{action_id}.{side_name}.identity"
    )
    expected_identity = tuple(range(degree))
    if identity != expected_identity:
        raise ValueError(f"{action_id}.{side_name}.identity is not the identity")
    generators_raw = raw["generators"]
    if not isinstance(generators_raw, list) or not generators_raw:
        raise ValueError(f"{action_id}.{side_name}.generators must be nonempty")
    named_generators = tuple(
        parse_named_permutation(
            item, f"{action_id}.{side_name}.generators[{index}]"
        )
        for index, item in enumerate(generators_raw)
    )
    raw_aliases = [identity_alias, *(alias for alias, _ in named_generators)]
    if len(raw_aliases) != len(set(raw_aliases)):
        raise ValueError(f"{action_id}.{side_name} has duplicate aliases")
    generator_permutations = tuple(value for _, value in named_generators)
    closure = _generator_closure(
        identity,
        generator_permutations,
        expected_size=expected_size,
        where=f"{action_id}.{side_name}",
    )
    width = max(3, len(str(len(closure) - 1)))
    element_ids = tuple(f"{prefix}{index:0{width}d}" for index in range(len(closure)))
    permutation_to_id = MappingProxyType(dict(zip(closure, element_ids, strict=True)))
    id_to_permutation = MappingProxyType(dict(zip(element_ids, closure, strict=True)))
    aliases = {identity_alias: permutation_to_id[identity]}
    aliases.update(
        {
            alias: permutation_to_id[permutation]
            for alias, permutation in named_generators
        }
    )
    generator_ids = tuple(
        permutation_to_id[permutation] for permutation in generator_permutations
    )
    generators_are_abelian = all(
        _commute(first, second)
        for first in generator_permutations
        for second in generator_permutations
    )
    if generators_are_abelian != expected_abelian:
        raise ValueError(
            f"{action_id}.{side_name} expected_abelian={expected_abelian}, "
            f"observed {generators_are_abelian}"
        )
    return ActionSide(
        name=side_name,
        elements=closure,
        element_ids=element_ids,
        id_to_permutation=id_to_permutation,
        permutation_to_id=permutation_to_id,
        aliases=MappingProxyType(aliases),
        identity_id=permutation_to_id[identity],
        generator_ids=generator_ids,
        expected_abelian=expected_abelian,
    )


def _canonical_published_support(
    raw: Any,
    *,
    action_id: str,
    left: ActionSide,
    right: ActionSide,
) -> tuple[Mapping[str, Any] | None, Mapping[str, Any] | None]:
    if raw is None:
        return None, None
    if not isinstance(raw, Mapping):
        raise ValueError(f"{action_id}.published_support must be a mapping or null")
    required = {
        "left_support",
        "right_support",
        "reported_n",
        "reported_k",
        "reported_distance",
        "reported_distance_exact",
        "distance_evidence_status",
    }
    _require_exact_keys(raw, required, where=f"{action_id}.published_support")
    left_aliases = raw["left_support"]
    right_aliases = raw["right_support"]
    if not isinstance(left_aliases, list) or not all(
        isinstance(value, str) for value in left_aliases
    ):
        raise ValueError(f"{action_id}.published_support.left_support is invalid")
    if not isinstance(right_aliases, list) or not all(
        isinstance(value, str) for value in right_aliases
    ):
        raise ValueError(f"{action_id}.published_support.right_support is invalid")
    canonical = deepcopy(dict(raw))
    canonical["left_support"] = [left.resolve(value) for value in left_aliases]
    canonical["right_support"] = [right.resolve(value) for value in right_aliases]
    aliases = {
        "left_support": list(left_aliases),
        "right_support": list(right_aliases),
    }
    return MappingProxyType(canonical), MappingProxyType(aliases)


def _parse_action(raw: Any) -> FrozenAction:
    if not isinstance(raw, Mapping):
        raise ValueError("each catalog action must be a mapping")
    _require_exact_keys(
        raw,
        {
            "action_id",
            "family",
            "bin",
            "block_size",
            "subgroup_normal",
            "search_enabled",
            "provenance",
            "published_support",
            "left",
            "right",
        },
        where="catalog action",
    )
    action_id = raw["action_id"]
    family = raw["family"]
    bin_name = raw["bin"]
    if not all(isinstance(value, str) and value for value in (action_id, family, bin_name)):
        raise ValueError("action_id, family, and bin must be nonempty strings")
    degree = _strict_positive_int(raw["block_size"], where=f"{action_id}.block_size")
    if degree > MAX_ACTION_DEGREE:
        raise ValueError(f"{action_id}.block_size exceeds {MAX_ACTION_DEGREE}")
    subgroup_normal = raw["subgroup_normal"]
    search_enabled = raw["search_enabled"]
    if not isinstance(subgroup_normal, bool) or not isinstance(search_enabled, bool):
        raise ValueError(f"{action_id} boolean metadata is invalid")
    provenance = raw["provenance"]
    if not isinstance(provenance, Mapping):
        raise ValueError(f"{action_id}.provenance must be a mapping")
    left = _parse_side(raw["left"], action_id=action_id, side_name="left", degree=degree)
    right = _parse_side(raw["right"], action_id=action_id, side_name="right", degree=degree)

    # This is the defining condition that permits the two-block CSS formula.
    # Check the complete closures rather than merely trusting the generators.
    for left_permutation in left.elements:
        for right_permutation in right.elements:
            if not _commute(left_permutation, right_permutation):
                raise ValueError(f"{action_id} has noncommuting left/right actions")

    published, published_aliases = _canonical_published_support(
        raw["published_support"], action_id=action_id, left=left, right=right
    )
    return FrozenAction(
        action_id=action_id,
        family=family,
        bin_name=bin_name,
        block_size=degree,
        subgroup_normal=subgroup_normal,
        search_enabled=search_enabled,
        provenance=MappingProxyType(deepcopy(dict(provenance))),
        published_support=published,
        published_support_aliases=published_aliases,
        left=left,
        right=right,
    )


def _read_catalog() -> tuple[bytes, Mapping[str, FrozenAction]]:
    if CATALOG_PATH.is_symlink() or not CATALOG_PATH.is_file():
        raise RuntimeError(f"action catalog must be a regular file: {CATALOG_PATH}")
    payload = CATALOG_PATH.read_bytes()
    if len(payload) > 2_000_000:
        raise RuntimeError("action catalog exceeds the 2 MB safety limit")
    try:
        raw = json.loads(payload, object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"invalid action catalog JSON: {exc}") from exc
    if not isinstance(raw, Mapping):
        raise RuntimeError("action catalog root must be a mapping")
    _require_exact_keys(raw, {"schema_version", "kind", "actions"}, where="catalog")
    if raw["schema_version"] != CATALOG_SCHEMA_VERSION or isinstance(
        raw["schema_version"], bool
    ):
        raise RuntimeError(f"unsupported action catalog schema {raw['schema_version']!r}")
    if raw["kind"] != CATALOG_KIND:
        raise RuntimeError(f"unexpected action catalog kind {raw['kind']!r}")
    actions_raw = raw["actions"]
    if not isinstance(actions_raw, list) or not actions_raw:
        raise RuntimeError("action catalog must contain at least one action")
    actions: dict[str, FrozenAction] = {}
    for action_raw in actions_raw:
        action = _parse_action(action_raw)
        if action.action_id in actions:
            raise RuntimeError(f"duplicate action_id {action.action_id!r}")
        actions[action.action_id] = action
    return payload, MappingProxyType(actions)


# Eager loading is intentional: malformed closures, an accidental catalog
# replacement, or broken commutation fail at process startup, before search.
_CATALOG_BYTES, _ACTIONS = _read_catalog()
_CATALOG_SHA256 = sha256(_CATALOG_BYTES).hexdigest()


def action_catalog_sha256() -> str:
    """Return the SHA-256 of the exact frozen catalog bytes."""

    return _CATALOG_SHA256


def get_action(action_id: str) -> FrozenAction:
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("action_id must be a nonempty string")
    try:
        return _ACTIONS[action_id]
    except KeyError as exc:
        raise ValueError(f"unknown frozen action_id {action_id!r}") from exc


def resolve_element_ids(
    action_id: str, side: str, values: Sequence[str]
) -> tuple[str, ...]:
    action = get_action(action_id)
    if side not in {"left", "right"}:
        raise ValueError("side must be 'left' or 'right'")
    action_side = action.left if side == "left" else action.right
    return tuple(action_side.resolve(value) for value in values)


def permutation_for_element(action_id: str, side: str, element_id: str) -> Permutation:
    action = get_action(action_id)
    if side not in {"left", "right"}:
        raise ValueError("side must be 'left' or 'right'")
    action_side = action.left if side == "left" else action.right
    canonical_id = action_side.resolve(element_id)
    return action_side.id_to_permutation[canonical_id]


@lru_cache(maxsize=1)
def _descriptors() -> tuple[dict[str, Any], ...]:
    descriptors: list[dict[str, Any]] = []
    for action_family_bin, action in enumerate(_ACTIONS.values()):
        published_left = (
            list(action.published_support["left_support"])
            if action.published_support is not None
            else None
        )
        published_right = (
            list(action.published_support["right_support"])
            if action.published_support is not None
            else None
        )
        descriptors.append(
            {
                "action_id": action.action_id,
                "action_catalog_sha256": _CATALOG_SHA256,
                "family": action.family,
                "bin": action.bin_name,
                # Stage 1 MAP-Elites consumes a small integer bin.  The
                # catalog order is frozen by the source hash, so enumeration
                # is deterministic and does not depend on Python hashing.
                "action_family_bin": action_family_bin,
                "block_size": action.block_size,
                "subgroup_normal": action.subgroup_normal,
                "search_enabled": action.search_enabled,
                "left_element_ids": list(action.left.element_ids),
                "right_element_ids": list(action.right.element_ids),
                "left_identity_id": action.left.identity_id,
                "right_identity_id": action.right.identity_id,
                "left_generator_ids": list(action.left.generator_ids),
                "right_generator_ids": list(action.right.generator_ids),
                "left_aliases": dict(action.left.aliases),
                "right_aliases": dict(action.right.aliases),
                "left_closure_size": len(action.left.elements),
                "right_closure_size": len(action.right.elements),
                "left_abelian": action.left.expected_abelian,
                "right_abelian": action.right.expected_abelian,
                "published_left_support": published_left,
                "published_right_support": published_right,
                "published_support": (
                    deepcopy(dict(action.published_support))
                    if action.published_support is not None
                    else None
                ),
                "published_support_aliases": (
                    deepcopy(dict(action.published_support_aliases))
                    if action.published_support_aliases is not None
                    else None
                ),
                "provenance": deepcopy(dict(action.provenance)),
                "validation": {
                    "closure_sizes_verified": True,
                    "faithful_permutation_closures_verified": True,
                    "left_right_commutation_verified": True,
                },
            }
        )
    return tuple(descriptors)


def list_action_descriptors() -> tuple[dict[str, Any], ...]:
    """Return mutation-safe, JSON-compatible search action descriptors."""

    return deepcopy(_descriptors())


__all__ = [
    "CATALOG_KIND",
    "CATALOG_PATH",
    "CATALOG_SCHEMA_VERSION",
    "FrozenAction",
    "Permutation",
    "action_catalog_sha256",
    "compose_permutations",
    "get_action",
    "inverse_permutation",
    "list_action_descriptors",
    "permutation_for_element",
    "resolve_element_ids",
]
