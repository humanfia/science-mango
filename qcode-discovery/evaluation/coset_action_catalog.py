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
from pathlib import Path, PurePosixPath
from types import MappingProxyType
from typing import Any


CATALOG_KIND = "qcode-coset-two-block-action-catalog"
CATALOG_SCHEMA_VERSION = 1
CATALOG_V2_SCHEMA_VERSION = 2
LEGACY_CATALOG_ID = "coset-two-block-actions-v1"
V2_CATALOG_ID = "coset2bga-official-all-coset-actions-a828dc43-v2"
V2_CATALOG_SHA256 = (
    "2e06bd808426f3f2c6c7eb05db331f8649e43b7784050f44bb1572aaeea6772a"
)
CATALOG_PATH = Path(__file__).with_name("coset_two_block_actions.v1.json")
CATALOG_V2_PATH = Path(__file__).with_name("coset_two_block_actions.v2.json")
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


def _strict_sha256(value: Any, *, where: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{where} must be a lowercase SHA-256 digest")
    return value


def _safe_source_path(value: Any, *, where: str) -> str:
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError(f"{where} must be a nonempty POSIX path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "." in path.parts:
        raise ValueError(f"{where} must be a normalized relative POSIX path")
    return path.as_posix()


def _parse_v2_sources(
    raw: Any,
) -> tuple[tuple[Mapping[str, Any], ...], Mapping[tuple[str, str], str]]:
    if not isinstance(raw, list) or not raw:
        raise ValueError("catalog v2 sources must be a nonempty list")
    sources: list[Mapping[str, Any]] = []
    bindings: dict[tuple[str, str], str] = {}
    source_ids: set[str] = set()
    project_root = Path(__file__).resolve().parent.parent
    for index, item in enumerate(raw):
        where = f"catalog.sources[{index}]"
        if not isinstance(item, Mapping):
            raise ValueError(f"{where} must be a mapping")
        source_kind = item.get("kind")
        if source_kind == "git":
            _require_exact_keys(
                item,
                {
                    "source_id",
                    "kind",
                    "repository",
                    "revision",
                    "selection",
                    "files",
                },
                where=where,
            )
        elif source_kind == "frozen-catalog":
            _require_exact_keys(
                item,
                {"source_id", "kind", "path", "sha256"},
                where=where,
            )
        else:
            raise ValueError(f"{where}.kind is unsupported")
        source_id = item["source_id"]
        if not isinstance(source_id, str) or not source_id or not source_id.isascii():
            raise ValueError(f"{where}.source_id is invalid")
        if source_id in source_ids:
            raise ValueError(f"duplicate catalog source_id {source_id!r}")
        source_ids.add(source_id)
        canonical = deepcopy(dict(item))
        if source_kind == "git":
            repository = item["repository"]
            revision = item["revision"]
            selection = item["selection"]
            if (
                not isinstance(repository, str)
                or not repository.startswith("https://github.com/")
            ):
                raise ValueError(f"{where}.repository must be an HTTPS GitHub URL")
            if (
                not isinstance(revision, str)
                or len(revision) != 40
                or any(character not in "0123456789abcdef" for character in revision)
            ):
                raise ValueError(f"{where}.revision must be a full Git commit")
            if not isinstance(selection, str) or not selection:
                raise ValueError(f"{where}.selection must be nonempty")
            files = item["files"]
            if not isinstance(files, list) or not files:
                raise ValueError(f"{where}.files must be a nonempty list")
            observed_paths: set[str] = set()
            canonical_files: list[dict[str, str]] = []
            for file_index, source_file in enumerate(files):
                file_where = f"{where}.files[{file_index}]"
                if not isinstance(source_file, Mapping):
                    raise ValueError(f"{file_where} must be a mapping")
                _require_exact_keys(
                    source_file, {"path", "sha256"}, where=file_where
                )
                path = _safe_source_path(source_file["path"], where=f"{file_where}.path")
                digest = _strict_sha256(
                    source_file["sha256"], where=f"{file_where}.sha256"
                )
                if path in observed_paths:
                    raise ValueError(f"{where} contains duplicate path {path!r}")
                observed_paths.add(path)
                key = (source_id, path)
                if key in bindings:
                    raise ValueError(f"duplicate source binding {key!r}")
                bindings[key] = digest
                canonical_files.append({"path": path, "sha256": digest})
            canonical["files"] = canonical_files
        else:
            path = _safe_source_path(item["path"], where=f"{where}.path")
            digest = _strict_sha256(item["sha256"], where=f"{where}.sha256")
            source_path = (project_root / path).resolve()
            try:
                source_path.relative_to(project_root)
            except ValueError as exc:
                raise ValueError(f"{where}.path escapes the project") from exc
            if source_path.is_symlink() or not source_path.is_file():
                raise ValueError(f"{where}.path is not a regular local file")
            if sha256(source_path.read_bytes()).hexdigest() != digest:
                raise ValueError(f"{where}.sha256 does not match the local file")
            bindings[(source_id, path)] = digest
            canonical["path"] = path
            canonical["sha256"] = digest
        sources.append(MappingProxyType(canonical))
    return tuple(sources), MappingProxyType(bindings)


def _parse_source_bindings(
    raw: Any,
    *,
    action_id: str,
    source_index: Mapping[tuple[str, str], str],
) -> tuple[Mapping[str, Any], ...]:
    if not isinstance(raw, list) or not raw:
        raise ValueError(f"{action_id}.source_bindings must be a nonempty list")
    result: list[Mapping[str, Any]] = []
    observed: set[tuple[str, str]] = set()
    for index, item in enumerate(raw):
        where = f"{action_id}.source_bindings[{index}]"
        if not isinstance(item, Mapping):
            raise ValueError(f"{where} must be a mapping")
        _require_exact_keys(item, {"source_id", "path", "sha256"}, where=where)
        source_id = item["source_id"]
        if not isinstance(source_id, str) or not source_id:
            raise ValueError(f"{where}.source_id is invalid")
        path = _safe_source_path(item["path"], where=f"{where}.path")
        digest = _strict_sha256(item["sha256"], where=f"{where}.sha256")
        key = (source_id, path)
        if key in observed:
            raise ValueError(f"{action_id} contains a duplicate source binding")
        observed.add(key)
        if source_index.get(key) != digest:
            raise ValueError(
                f"{where} does not exactly join the catalog source manifest"
            )
        result.append(MappingProxyType({
            "source_id": source_id,
            "path": path,
            "sha256": digest,
        }))
    return tuple(result)


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
    source_paths: frozenset[str]

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
    source_bindings: tuple[Mapping[str, Any], ...]
    provenance: Mapping[str, Any]
    published_support: Mapping[str, Any] | None
    published_support_aliases: Mapping[str, Any] | None
    left: ActionSide
    right: ActionSide


@dataclass(frozen=True)
class FrozenActionCatalog:
    """One immutable, independently addressable action catalog."""

    catalog_id: str
    schema_version: int
    path: Path
    sha256: str
    sources: tuple[Mapping[str, Any], ...]
    actions: Mapping[str, FrozenAction]


def _parse_side(
    raw: Any,
    *,
    action_id: str,
    side_name: str,
    degree: int,
    allowed_source_paths: frozenset[str] | None = None,
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

    used_source_paths: set[str] = set()

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
        if allowed_source_paths is not None:
            source_path, separator, block_name = upstream_alias.partition("#")
            if not separator or not block_name or source_path not in allowed_source_paths:
                raise ValueError(
                    f"{where}.upstream_block_alias is outside source_bindings"
                )
            used_source_paths.add(source_path)
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
        source_paths=frozenset(used_source_paths),
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


def _parse_action(
    raw: Any,
    *,
    schema_version: int = CATALOG_SCHEMA_VERSION,
    source_index: Mapping[tuple[str, str], str] | None = None,
) -> FrozenAction:
    if not isinstance(raw, Mapping):
        raise ValueError("each catalog action must be a mapping")
    required = {
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
    }
    if schema_version == CATALOG_V2_SCHEMA_VERSION:
        required.add("source_bindings")
    _require_exact_keys(raw, required, where="catalog action")
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
    source_bindings: tuple[Mapping[str, Any], ...] = ()
    allowed_source_paths: frozenset[str] | None = None
    if schema_version == CATALOG_V2_SCHEMA_VERSION:
        if source_index is None:
            raise ValueError("catalog v2 action parsing requires a source manifest")
        source_bindings = _parse_source_bindings(
            raw["source_bindings"],
            action_id=action_id,
            source_index=source_index,
        )
        allowed_source_paths = frozenset(
            binding["path"] for binding in source_bindings
        )
    left = _parse_side(
        raw["left"],
        action_id=action_id,
        side_name="left",
        degree=degree,
        allowed_source_paths=allowed_source_paths,
    )
    right = _parse_side(
        raw["right"],
        action_id=action_id,
        side_name="right",
        degree=degree,
        allowed_source_paths=allowed_source_paths,
    )
    if search_enabled and (len(left.elements) < 3 or len(right.elements) < 3):
        raise ValueError(
            f"{action_id} cannot supply two nonidentity elements on each side"
        )
    if allowed_source_paths is not None and (
        left.source_paths | right.source_paths
    ) != allowed_source_paths:
        raise ValueError(
            f"{action_id}.source_bindings are not exactly used by its frozen blocks"
        )

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
        source_bindings=source_bindings,
        provenance=MappingProxyType(deepcopy(dict(provenance))),
        published_support=published,
        published_support_aliases=published_aliases,
        left=left,
        right=right,
    )


def _read_catalog_file(path: Path) -> FrozenActionCatalog:
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"action catalog must be a regular file: {path}")
    payload = path.read_bytes()
    if len(payload) > 2_000_000:
        raise RuntimeError("action catalog exceeds the 2 MB safety limit")
    try:
        raw = json.loads(payload, object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"invalid action catalog JSON: {exc}") from exc
    if not isinstance(raw, Mapping):
        raise RuntimeError("action catalog root must be a mapping")
    schema_version = raw.get("schema_version")
    if isinstance(schema_version, bool) or schema_version not in {
        CATALOG_SCHEMA_VERSION,
        CATALOG_V2_SCHEMA_VERSION,
    }:
        raise RuntimeError(f"unsupported action catalog schema {schema_version!r}")
    sources: tuple[Mapping[str, Any], ...] = ()
    source_index: Mapping[tuple[str, str], str] | None = None
    if schema_version == CATALOG_SCHEMA_VERSION:
        _require_exact_keys(
            raw, {"schema_version", "kind", "actions"}, where="catalog"
        )
        catalog_id = LEGACY_CATALOG_ID
    else:
        _require_exact_keys(
            raw,
            {"schema_version", "kind", "catalog_id", "sources", "actions"},
            where="catalog",
        )
        catalog_id = raw["catalog_id"]
        if catalog_id != V2_CATALOG_ID:
            raise RuntimeError(f"unexpected catalog v2 identity {catalog_id!r}")
        if sha256(payload).hexdigest() != V2_CATALOG_SHA256:
            raise RuntimeError("catalog v2 bytes do not match its reviewed identity")
        try:
            sources, source_index = _parse_v2_sources(raw["sources"])
        except ValueError as exc:
            raise RuntimeError(f"invalid catalog v2 source manifest: {exc}") from exc
    if raw["kind"] != CATALOG_KIND:
        raise RuntimeError(f"unexpected action catalog kind {raw['kind']!r}")
    actions_raw = raw["actions"]
    if not isinstance(actions_raw, list) or not actions_raw:
        raise RuntimeError("action catalog must contain at least one action")
    actions: dict[str, FrozenAction] = {}
    for action_raw in actions_raw:
        action = _parse_action(
            action_raw,
            schema_version=int(schema_version),
            source_index=source_index,
        )
        if action.action_id in actions:
            raise RuntimeError(f"duplicate action_id {action.action_id!r}")
        actions[action.action_id] = action
    if source_index is not None:
        used_bindings = {
            (binding["source_id"], binding["path"])
            for action in actions.values()
            for binding in action.source_bindings
        }
        if used_bindings != set(source_index):
            raise RuntimeError(
                "catalog v2 source manifest is not exactly covered by action bindings"
            )
    return FrozenActionCatalog(
        catalog_id=catalog_id,
        schema_version=int(schema_version),
        path=path,
        sha256=sha256(payload).hexdigest(),
        sources=sources,
        actions=MappingProxyType(actions),
    )


# Eager loading is intentional: malformed closures, an accidental catalog
# replacement, broken provenance joins, or broken commutation fail at process
# startup, before search.  The legacy default remains v1; v2 callers must pin
# ``V2_CATALOG_ID`` or its exact SHA-256 explicitly.
_LEGACY_CATALOG = _read_catalog_file(CATALOG_PATH)
_V2_CATALOG = _read_catalog_file(CATALOG_V2_PATH)
_CATALOGS_BY_ID = MappingProxyType({
    _LEGACY_CATALOG.catalog_id: _LEGACY_CATALOG,
    _V2_CATALOG.catalog_id: _V2_CATALOG,
})
_CATALOGS_BY_SHA256 = MappingProxyType({
    _LEGACY_CATALOG.sha256: _LEGACY_CATALOG,
    _V2_CATALOG.sha256: _V2_CATALOG,
})
if len(_CATALOGS_BY_SHA256) != len(_CATALOGS_BY_ID):
    raise RuntimeError("versioned action catalogs unexpectedly share one digest")

# Private compatibility aliases for historical in-process users.
_ACTIONS = _LEGACY_CATALOG.actions
_CATALOG_SHA256 = _LEGACY_CATALOG.sha256


def get_catalog(
    *,
    catalog_id: str | None = None,
    catalog_sha256: str | None = None,
) -> FrozenActionCatalog:
    """Resolve an immutable catalog without a mutable process-global selector."""

    if catalog_id is None and catalog_sha256 is None:
        return _LEGACY_CATALOG
    by_id = None
    by_sha = None
    if catalog_id is not None:
        if not isinstance(catalog_id, str) or not catalog_id:
            raise ValueError("catalog_id must be a nonempty string")
        by_id = _CATALOGS_BY_ID.get(catalog_id)
        if by_id is None:
            raise ValueError(f"unknown frozen action catalog_id {catalog_id!r}")
    if catalog_sha256 is not None:
        _strict_sha256(catalog_sha256, where="catalog_sha256")
        by_sha = _CATALOGS_BY_SHA256.get(catalog_sha256)
        if by_sha is None:
            raise ValueError(
                f"unknown frozen action catalog SHA-256 {catalog_sha256!r}"
            )
    if by_id is not None and by_sha is not None and by_id is not by_sha:
        raise ValueError("catalog_id and catalog_sha256 select different catalogs")
    selected = by_id if by_id is not None else by_sha
    if selected is None:  # Defensive; every supplied selector was checked above.
        raise RuntimeError("catalog selector resolution failed")
    return selected


def load_action_catalog(path: Path) -> FrozenActionCatalog:
    """Strictly load one catalog file without registering it process-wide."""

    if not isinstance(path, Path):
        raise TypeError("catalog path must be a pathlib.Path")
    return _read_catalog_file(path)


def action_catalog_sha256(catalog_id: str = LEGACY_CATALOG_ID) -> str:
    """Return the SHA-256 of the exact frozen catalog bytes."""

    return get_catalog(catalog_id=catalog_id).sha256


def action_catalog_identity(
    catalog_id: str = LEGACY_CATALOG_ID,
) -> dict[str, Any]:
    """Return a JSON-safe versioned catalog identity."""

    catalog = get_catalog(catalog_id=catalog_id)
    return {
        "catalog_id": catalog.catalog_id,
        "schema_version": catalog.schema_version,
        "kind": CATALOG_KIND,
        "sha256": catalog.sha256,
    }


def get_action(
    action_id: str,
    *,
    catalog_id: str | None = None,
    catalog_sha256: str | None = None,
) -> FrozenAction:
    if not isinstance(action_id, str) or not action_id:
        raise ValueError("action_id must be a nonempty string")
    catalog = get_catalog(catalog_id=catalog_id, catalog_sha256=catalog_sha256)
    try:
        return catalog.actions[action_id]
    except KeyError as exc:
        raise ValueError(f"unknown frozen action_id {action_id!r}") from exc


def resolve_element_ids(
    action_id: str,
    side: str,
    values: Sequence[str],
    *,
    catalog_id: str | None = None,
    catalog_sha256: str | None = None,
) -> tuple[str, ...]:
    action = get_action(
        action_id,
        catalog_id=catalog_id,
        catalog_sha256=catalog_sha256,
    )
    if side not in {"left", "right"}:
        raise ValueError("side must be 'left' or 'right'")
    action_side = action.left if side == "left" else action.right
    return tuple(action_side.resolve(value) for value in values)


def permutation_for_element(
    action_id: str,
    side: str,
    element_id: str,
    *,
    catalog_id: str | None = None,
    catalog_sha256: str | None = None,
) -> Permutation:
    action = get_action(
        action_id,
        catalog_id=catalog_id,
        catalog_sha256=catalog_sha256,
    )
    if side not in {"left", "right"}:
        raise ValueError("side must be 'left' or 'right'")
    action_side = action.left if side == "left" else action.right
    canonical_id = action_side.resolve(element_id)
    return action_side.id_to_permutation[canonical_id]


@lru_cache(maxsize=2)
def _descriptors(catalog_id: str) -> tuple[dict[str, Any], ...]:
    catalog = get_catalog(catalog_id=catalog_id)
    descriptors: list[dict[str, Any]] = []
    family_bins = {"nonnormal-coset": 0, "normal-regular": 1}
    for action_lane_index, action in enumerate(catalog.actions.values()):
        try:
            action_family_bin = family_bins[action.bin_name]
        except KeyError as exc:
            raise RuntimeError(
                f"action {action.action_id} has an unknown family bin"
            ) from exc
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
                "action_catalog_id": catalog.catalog_id,
                "action_catalog_schema_version": catalog.schema_version,
                "action_catalog_sha256": catalog.sha256,
                "family": action.family,
                "bin": action.bin_name,
                # Stage 1 MAP-Elites consumes a small integer bin.  The
                # catalog order is frozen by the source hash, so enumeration
                # is deterministic and does not depend on Python hashing.
                "action_family_bin": action_family_bin,
                "action_lane_index": action_lane_index,
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
                "source_bindings": [
                    deepcopy(dict(binding)) for binding in action.source_bindings
                ],
                "validation": {
                    "closure_sizes_verified": True,
                    "faithful_permutation_closures_verified": True,
                    "left_right_commutation_verified": True,
                    **(
                        {"source_bindings_verified": True}
                        if catalog.schema_version == CATALOG_V2_SCHEMA_VERSION
                        else {}
                    ),
                    **(
                        {
                            "source_generator_closure_verified": True,
                            "full_group_action_claimed": False,
                        }
                        if catalog.schema_version == CATALOG_V2_SCHEMA_VERSION
                        and not action.subgroup_normal
                        else {}
                    ),
                },
            }
        )
    return tuple(descriptors)


def list_action_descriptors(
    *,
    catalog_id: str = LEGACY_CATALOG_ID,
) -> tuple[dict[str, Any], ...]:
    """Return mutation-safe, JSON-compatible search action descriptors."""

    return deepcopy(_descriptors(catalog_id))


__all__ = [
    "CATALOG_KIND",
    "CATALOG_PATH",
    "CATALOG_SCHEMA_VERSION",
    "CATALOG_V2_PATH",
    "CATALOG_V2_SCHEMA_VERSION",
    "FrozenAction",
    "FrozenActionCatalog",
    "LEGACY_CATALOG_ID",
    "Permutation",
    "V2_CATALOG_ID",
    "V2_CATALOG_SHA256",
    "action_catalog_identity",
    "action_catalog_sha256",
    "compose_permutations",
    "get_action",
    "get_catalog",
    "inverse_permutation",
    "load_action_catalog",
    "list_action_descriptors",
    "permutation_for_element",
    "resolve_element_ids",
]
