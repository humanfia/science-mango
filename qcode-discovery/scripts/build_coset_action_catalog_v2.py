#!/usr/bin/env python3
"""Build the source-bound coset action catalog v2 from the official data.

The importer accepts exactly one clean checkout of the pinned
``aaydinnnn/Coset2BGACodes`` revision.  It does not invoke GAP and it does not
infer permutation actions from code parameters.  Every permutation copied to
the generated catalog is an exact ``building_blocks`` matrix from an upstream
JSON record.  Records are grouped by the upstream GAP tuple ``(l, m, s)`` and
the coset-action degree, so multiple published supports for the same action do
not masquerade as additional action families.

The generated catalog is deterministic.  ``--check`` is suitable for CI and
does not modify the output file.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from collections.abc import Mapping
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from typing import Any


UPSTREAM_REPOSITORY = "https://github.com/aaydinnnn/Coset2BGACodes"
UPSTREAM_COMMIT = "a828dc43c55982e0212febea634775d36bf6e968"
UPSTREAM_SOURCE_ID = "coset2bga-a828dc43"
PAPER = "arXiv:2606.17268"
CATALOG_ID = "coset2bga-official-all-coset-actions-a828dc43-v2"
CATALOG_KIND = "qcode-coset-two-block-action-catalog"
SCHEMA_VERSION = 2
MAX_UPSTREAM_FILE_BYTES = 1_000_000
MAX_ACTION_DEGREE = 180
EXPECTED_RECORD_COUNT = 60
EXPECTED_OFFICIAL_ACTION_COUNT = 45
EXPECTED_ACTION_COUNT = 46
LEGACY_CATALOG_ID = "coset-two-block-actions-v1"
LEGACY_SOURCE_ID = "local-frozen-catalog-v1"
LEGACY_CATALOG_SHA256 = (
    "7599be34679075de6fba8675f8b7c1d8f21b6eae56061418012ef796eafdb323"
)
LEGACY_CONTROL_ACTION_ID = "dihedral-d36-regular-degree72-v1"

_FILENAME = re.compile(
    r"code_n(?P<n>\d+)_k(?P<k>\d+)_d(?P<d>\d+)_"
    r"l(?P<l>\d+)_m(?P<m>\d+)_s(?P<s>\d+)_"
    r"a(?P<a>\d+(?:_\d+)*)_b(?P<b>\d+(?:_\d+)*)\.json"
)

Permutation = tuple[int, ...]


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key in upstream record: {key!r}")
        result[key] = value
    return result


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, where: str) -> None:
    observed = set(value)
    if observed != expected:
        raise ValueError(
            f"{where} fields are not exact; "
            f"missing={sorted(expected - observed)}, "
            f"unknown={sorted(observed - expected)}"
        )


def _git(root: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return completed.stdout.strip()


def _validate_checkout(root: Path) -> None:
    if not root.is_dir() or root.is_symlink():
        raise ValueError("upstream root must be a real directory")
    revision = _git(root, "rev-parse", "HEAD")
    if revision != UPSTREAM_COMMIT:
        raise ValueError(
            f"upstream checkout is {revision}, expected {UPSTREAM_COMMIT}"
        )
    dirty = _git(root, "status", "--porcelain", "--untracked-files=no")
    if dirty:
        raise ValueError("upstream checkout has tracked modifications")


def _compose(left: Permutation, right: Permutation) -> Permutation:
    if len(left) != len(right):
        raise ValueError("permutation degrees differ")
    return tuple(right[index] for index in left)


def _commute(left: Permutation, right: Permutation) -> bool:
    return _compose(left, right) == _compose(right, left)


def _closure(generators: tuple[Permutation, ...], degree: int) -> set[Permutation]:
    identity = tuple(range(degree))
    discovered = {identity}
    pending: deque[Permutation] = deque([identity])
    while pending:
        current = pending.popleft()
        for generator in generators:
            product = _compose(current, generator)
            if product in discovered:
                continue
            discovered.add(product)
            pending.append(product)
    return discovered


def _permutation(block: Any, degree: int, *, where: str) -> Permutation:
    if not isinstance(block, Mapping):
        raise ValueError(f"{where} must be a mapping")
    _exact_keys(block, {"rows", "cols"}, where=where)
    rows = block["rows"]
    columns = block["cols"]
    if not isinstance(rows, list) or not isinstance(columns, list):
        raise ValueError(f"{where} rows and cols must be lists")
    if rows != list(range(degree)):
        raise ValueError(f"{where} rows must be the canonical row ordering")
    if any(isinstance(item, bool) or not isinstance(item, int) for item in columns):
        raise ValueError(f"{where} has a non-integer column")
    result = tuple(int(item) for item in columns)
    if tuple(sorted(result)) != tuple(range(degree)):
        raise ValueError(f"{where} columns are not a permutation")
    return result


def _strict_int_list(value: Any, *, where: str) -> tuple[int, ...]:
    if (
        not isinstance(value, list)
        or not value
        or any(isinstance(item, bool) or not isinstance(item, int) for item in value)
    ):
        raise ValueError(f"{where} must be a nonempty integer list")
    result = tuple(int(item) for item in value)
    if len(set(result)) != len(result):
        raise ValueError(f"{where} contains duplicates")
    return result


def _read_record(path: Path, upstream_root: Path) -> dict[str, Any]:
    relative = path.relative_to(upstream_root).as_posix()
    if PurePosixPath(relative).is_absolute() or ".." in PurePosixPath(relative).parts:
        raise ValueError(f"unsafe upstream path {relative!r}")
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"upstream record must be a regular file: {relative}")
    payload = path.read_bytes()
    if not payload or len(payload) > MAX_UPSTREAM_FILE_BYTES:
        raise ValueError(f"upstream record size is invalid: {relative}")
    try:
        document = json.loads(payload, object_pairs_hook=_reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"invalid upstream JSON {relative}: {exc}") from exc
    if not isinstance(document, Mapping):
        raise ValueError(f"upstream record root is not a mapping: {relative}")
    _exact_keys(document, {"metadata", "building_blocks"}, where=relative)
    metadata = document["metadata"]
    blocks = document["building_blocks"]
    if not isinstance(metadata, Mapping) or not isinstance(blocks, Mapping):
        raise ValueError(f"upstream record sections are invalid: {relative}")
    _exact_keys(
        metadata,
        {"n", "k", "d", "is_exact_distance", "l", "m", "s", "a", "b"},
        where=f"{relative}.metadata",
    )
    integer_fields = ("n", "k", "d", "l", "m", "s")
    if any(
        isinstance(metadata[field], bool)
        or not isinstance(metadata[field], int)
        or metadata[field] <= 0
        for field in integer_fields
    ):
        raise ValueError(f"upstream integer metadata is invalid: {relative}")
    if not isinstance(metadata["is_exact_distance"], bool):
        raise ValueError(f"upstream exact-distance flag is invalid: {relative}")
    left_indices = _strict_int_list(metadata["a"], where=f"{relative}.metadata.a")
    right_indices = _strict_int_list(metadata["b"], where=f"{relative}.metadata.b")
    match = _FILENAME.fullmatch(path.name)
    if match is None:
        raise ValueError(f"upstream filename violates the published format: {relative}")
    filename_values = {
        key: int(match.group(key)) for key in ("n", "k", "d", "l", "m", "s")
    }
    if any(metadata[key] != value for key, value in filename_values.items()):
        raise ValueError(f"filename metadata mismatch: {relative}")
    if tuple(map(int, match.group("a").split("_"))) != left_indices:
        raise ValueError(f"filename left support mismatch: {relative}")
    if tuple(map(int, match.group("b").split("_"))) != right_indices:
        raise ValueError(f"filename right support mismatch: {relative}")

    degree = metadata["n"] // 2
    if metadata["n"] % 2 or degree < 2 or degree > MAX_ACTION_DEGREE:
        raise ValueError(f"upstream action degree is invalid: {relative}")
    expected_blocks = {
        *(f"A{index}" for index in range(1, len(left_indices) + 1)),
        *(f"B{index}" for index in range(1, len(right_indices) + 1)),
    }
    _exact_keys(blocks, expected_blocks, where=f"{relative}.building_blocks")
    left = tuple(
        _permutation(blocks[f"A{index}"], degree, where=f"{relative}.A{index}")
        for index in range(1, len(left_indices) + 1)
    )
    right = tuple(
        _permutation(blocks[f"B{index}"], degree, where=f"{relative}.B{index}")
        for index in range(1, len(right_indices) + 1)
    )
    identity = tuple(range(degree))
    if left_indices[0] != 1 or right_indices[0] != 1:
        raise ValueError(f"upstream support is not identity-normalized: {relative}")
    if left[0] != identity or right[0] != identity:
        raise ValueError(f"upstream A1/B1 are not identities: {relative}")
    if not all(_commute(first, second) for first in left for second in right):
        raise ValueError(f"upstream left/right blocks do not commute: {relative}")
    return {
        "path": relative,
        "sha256": sha256(payload).hexdigest(),
        "metadata": dict(metadata),
        "left_indices": left_indices,
        "right_indices": right_indices,
        "left": left,
        "right": right,
        "degree": degree,
    }


def _selected_records(upstream_root: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in sorted((upstream_root / "code_dict").glob("code_*.json")):
        record = _read_record(path, upstream_root)
        if record["metadata"]["n"] <= 360:
            records.append(record)
    if len(records) != EXPECTED_RECORD_COUNT:
        raise ValueError(
            f"pinned selection yielded {len(records)} records; "
            f"expected {EXPECTED_RECORD_COUNT}"
        )
    return records


def _side(
    records: list[dict[str, Any]],
    *,
    side: str,
    degree: int,
) -> dict[str, Any]:
    letter = "A" if side == "left" else "B"
    support_key = "left_indices" if side == "left" else "right_indices"
    permutations_key = "left" if side == "left" else "right"
    prefix = "L" if side == "left" else "R"
    aliases: dict[str, tuple[Permutation, str]] = {}
    identity = tuple(range(degree))
    identity_source = records[0]["path"]
    for record in records:
        for position, (paper_index, permutation) in enumerate(
            zip(record[support_key], record[permutations_key], strict=True),
            start=1,
        ):
            alias = f"{'a' if side == 'left' else 'b'}:{paper_index}"
            source_alias = f"{record['path']}#{letter}{position}"
            previous = aliases.get(alias)
            if previous is not None and previous[0] != permutation:
                raise ValueError(
                    f"paper alias {alias} maps to multiple permutations for one action"
                )
            aliases.setdefault(alias, (permutation, source_alias))
    identity_alias = "a:1" if side == "left" else "b:1"
    if aliases.get(identity_alias, (None, ""))[0] != identity:
        raise ValueError(f"{side} identity alias is missing")
    nonidentity = [
        (alias, value)
        for alias, value in sorted(
            aliases.items(), key=lambda item: int(item[0].split(":", 1)[1])
        )
        if value[0] != identity
    ]
    permutations = [value[0] for _, value in nonidentity]
    if len(permutations) != len(set(permutations)):
        raise ValueError(
            f"one {side} permutation has multiple paper aliases; "
            "v2 refuses ambiguous source labels"
        )
    generators = tuple(permutations)
    closure = _closure(generators, degree)
    expected_abelian = all(
        _commute(first, second) for first in generators for second in generators
    )
    return {
        "stable_id_prefix": prefix,
        "expected_closure_size": len(closure),
        "expected_abelian": expected_abelian,
        "identity": {
            "alias": identity_alias,
            "paper_index_alias": 1,
            "upstream_block_alias": f"{identity_source}#{letter}1",
            "permutation": list(identity),
        },
        "generators": [
            {
                "alias": alias,
                "paper_index_alias": int(alias.split(":", 1)[1]),
                "upstream_block_alias": source_alias,
                "permutation": list(permutation),
            }
            for alias, (permutation, source_alias) in nonidentity
        ],
    }


def _anchor(records: list[dict[str, Any]]) -> dict[str, Any] | None:
    # A 4+4 record safely expands the action geometry, but is not a production
    # 3+3 candidate anchor.  Prefer the strongest published 3+3 record when one
    # exists.  Exactness remains metadata and never becomes local proof.
    compatible = [
        record
        for record in records
        if len(record["left_indices"]) == 3
        and len(record["right_indices"]) == 3
    ]
    if not compatible:
        return None
    return max(
        compatible,
        key=lambda record: (
            record["metadata"]["k"] * record["metadata"]["d"] ** 2
            / record["metadata"]["n"],
            record["metadata"]["d"],
            record["metadata"]["k"],
            record["path"],
        ),
    )


def _action(records: list[dict[str, Any]]) -> dict[str, Any]:
    records = sorted(records, key=lambda record: record["path"])
    metadata = records[0]["metadata"]
    degree = records[0]["degree"]
    group_key = (metadata["l"], metadata["m"], metadata["s"], degree)
    if any(
        (
            record["metadata"]["l"],
            record["metadata"]["m"],
            record["metadata"]["s"],
            record["degree"],
        )
        != group_key
        for record in records
    ):
        raise ValueError("attempted to merge distinct GAP actions")
    left = _side(records, side="left", degree=degree)
    right = _side(records, side="right", degree=degree)
    left_closure = _closure(
        tuple(tuple(item["permutation"]) for item in left["generators"]), degree
    )
    right_closure = _closure(
        tuple(tuple(item["permutation"]) for item in right["generators"]), degree
    )
    if not all(_commute(first, second) for first in left_closure for second in right_closure):
        raise ValueError(f"merged action {group_key} does not commute")
    anchor = _anchor(records)
    bindings = [
        {
            "source_id": UPSTREAM_SOURCE_ID,
            "path": record["path"],
            "sha256": record["sha256"],
        }
        for record in records
    ]
    published_support = None
    if anchor is not None:
        anchor_metadata = anchor["metadata"]
        published_support = {
            "left_support": [f"a:{value}" for value in anchor["left_indices"]],
            "right_support": [f"b:{value}" for value in anchor["right_indices"]],
            "reported_n": anchor_metadata["n"],
            "reported_k": anchor_metadata["k"],
            "reported_distance": anchor_metadata["d"],
            "reported_distance_exact": anchor_metadata["is_exact_distance"],
            "distance_evidence_status": (
                "published-exact-metadata-not-locally-proven"
                if anchor_metadata["is_exact_distance"]
                else "published-upper-bound-metadata-not-locally-proven"
            ),
        }
    return {
        "action_id": (
            f"coset2bga-l{metadata['l']}-m{metadata['m']}-s{metadata['s']}-"
            f"degree{degree}-v2"
        ),
        "family": "coset-two-block-nonnormal",
        "bin": "nonnormal-coset",
        "block_size": degree,
        "subgroup_normal": False,
        "search_enabled": True,
        "source_bindings": bindings,
        "provenance": {
            "paper": PAPER,
            "upstream_repository": UPSTREAM_REPOSITORY,
            "upstream_commit": UPSTREAM_COMMIT,
            "gap_version": "4.14.0",
            "gap_group_id": [metadata["l"], metadata["m"]],
            "gap_nonnormal_subgroup_index": metadata["s"],
            "generator_policy": "union-of-all-published-building-blocks",
            "action_scope": "published-generator-closure-not-claimed-full-G-action",
            "published_record_count": len(records),
        },
        "published_support": published_support,
        "left": left,
        "right": right,
    }


def _legacy_control(project_root: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    """Carry the existing normal regular control into the v2 superset."""

    catalog_path = project_root / "evaluation" / "coset_two_block_actions.v1.json"
    if catalog_path.is_symlink() or not catalog_path.is_file():
        raise ValueError("legacy v1 catalog must be a regular file")
    payload = catalog_path.read_bytes()
    digest = sha256(payload).hexdigest()
    if digest != LEGACY_CATALOG_SHA256:
        raise ValueError(
            f"legacy v1 catalog hash is {digest}, expected {LEGACY_CATALOG_SHA256}"
        )
    document = json.loads(payload, object_pairs_hook=_reject_duplicate_keys)
    actions = document.get("actions") if isinstance(document, Mapping) else None
    if not isinstance(actions, list):
        raise ValueError("legacy v1 catalog has no action list")
    matches = [
        item
        for item in actions
        if isinstance(item, Mapping)
        and item.get("action_id") == LEGACY_CONTROL_ACTION_ID
    ]
    if len(matches) != 1:
        raise ValueError("legacy v1 normal control is missing or ambiguous")
    action = deepcopy(dict(matches[0]))
    action["action_id"] = "dihedral-d36-regular-degree72-v2"
    legacy_path = "evaluation/coset_two_block_actions.v1.json"
    for side_name in ("left", "right"):
        side = action[side_name]
        side["identity"]["upstream_block_alias"] = (
            f"{legacy_path}#{side['identity']['upstream_block_alias']}"
        )
        for generator in side["generators"]:
            generator["upstream_block_alias"] = (
                f"{legacy_path}#{generator['upstream_block_alias']}"
            )
    action["source_bindings"] = [
        {
            "source_id": LEGACY_SOURCE_ID,
            "path": legacy_path,
            "sha256": digest,
        }
    ]
    provenance = deepcopy(dict(action["provenance"]))
    provenance.update({
        "derived_from_catalog_id": LEGACY_CATALOG_ID,
        "derived_from_catalog_sha256": digest,
        "derived_from_action_id": LEGACY_CONTROL_ACTION_ID,
    })
    action["provenance"] = provenance
    source = {
        "source_id": LEGACY_SOURCE_ID,
        "kind": "frozen-catalog",
        "path": legacy_path,
        "sha256": digest,
    }
    return action, source


def build_catalog(upstream_root: Path) -> dict[str, Any]:
    _validate_checkout(upstream_root)
    records = _selected_records(upstream_root)
    grouped: dict[tuple[int, int, int, int], list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        metadata = record["metadata"]
        grouped[
            (metadata["l"], metadata["m"], metadata["s"], record["degree"])
        ].append(record)
    if len(grouped) != EXPECTED_OFFICIAL_ACTION_COUNT:
        raise ValueError(
            f"pinned records yielded {len(grouped)} distinct actions; "
            f"expected {EXPECTED_OFFICIAL_ACTION_COUNT}"
        )
    actions = [_action(grouped[key]) for key in sorted(grouped)]
    project_root = Path(__file__).resolve().parents[1]
    legacy_control, legacy_source = _legacy_control(project_root)
    actions.append(legacy_control)
    actions.sort(key=lambda action: action["action_id"])
    if len(actions) != EXPECTED_ACTION_COUNT:
        raise ValueError(
            f"v2 catalog has {len(actions)} actions; expected {EXPECTED_ACTION_COUNT}"
        )
    files = [
        {"path": record["path"], "sha256": record["sha256"]}
        for record in sorted(records, key=lambda record: record["path"])
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": CATALOG_KIND,
        "catalog_id": CATALOG_ID,
        "sources": [
            {
                "source_id": UPSTREAM_SOURCE_ID,
                "kind": "git",
                "repository": UPSTREAM_REPOSITORY,
                "revision": UPSTREAM_COMMIT,
                "selection": "all code_*.json with n<=360; grouped by (l,m,s,degree)",
                "files": files,
            },
            legacy_source,
        ],
        "actions": actions,
    }


def _canonical_bytes(document: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(
            document,
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream-root", required=True, type=Path)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1]
        / "evaluation"
        / "coset_two_block_actions.v2.json",
    )
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    payload = _canonical_bytes(build_catalog(arguments.upstream_root.resolve()))
    if arguments.check:
        if not arguments.output.is_file() or arguments.output.read_bytes() != payload:
            raise SystemExit("coset action catalog v2 is not reproducible")
        print(f"verified {arguments.output} ({sha256(payload).hexdigest()})")
        return 0
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_bytes(payload)
    print(f"wrote {arguments.output} ({sha256(payload).hexdigest()})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
