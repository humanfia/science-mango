#!/usr/bin/env python3
"""Solver-free width-six campaign for one authenticated paper400 parent.

The existing root cover has 16 mutually exclusive and exhaustive parents.  For
one selected parent this module freshly constructs both the established
width-four refinement and a width-six refinement with
``paper400_dic5_hierarchical_cubes_v1``.  The refiner's deterministic ranking
must make the first four width-six variables identical to the width-four
variables.  Consequently every old child is replaced by exactly four wider
children, indexed ``4 * old_child + suffix``.

The 64 wider children are scheduled in immutable four-lane batches.  Each
batch takes four consecutive old width-four prefixes and one common two-bit
suffix, so the first four batches are ``[0,4,8,12]``, ``[1,5,9,13]``,
``[2,6,10,14]``, and ``[3,7,11,15]``.  This file never invokes a solver and a
campaign manifest alone is not an UNSAT or distance proof.
"""

from __future__ import annotations

import hashlib
import json
from itertools import product
from pathlib import Path
from typing import Any, Mapping, Sequence

from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy


cube16 = hierarchy.cube16
PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 1
MANIFEST_KIND = "paper400-dic5-widened-parent-campaign-v1"
FORMULATION = "one-parent-exact-width6-refinement-with-width4-prefix-v1"
AUTHORITY_PRODUCTION_CANDIDATE = "PRODUCTION_CANDIDATE"
AUTHORITY_TEST_ONLY = "SYNTHETIC_TEST_ONLY"

PARENT_COUNT = 16
OLD_SPLIT_WIDTH = 4
SPLIT_WIDTH = 6
SUFFIX_WIDTH = SPLIT_WIDTH - OLD_SPLIT_WIDTH
OLD_PREFIX_COUNT = 1 << OLD_SPLIT_WIDTH
SUFFIX_COUNT = 1 << SUFFIX_WIDTH
LEAF_COUNT = 1 << SPLIT_WIDTH
LANES_PER_BATCH = 4
BATCH_COUNT = LEAF_COUNT // LANES_PER_BATCH
PAIR_COUNT = LEAF_COUNT * (LEAF_COUNT - 1) // 2

MANIFEST_FIELDS = frozenset({
    "schema_version",
    "manifest_kind",
    "formulation",
    "authority",
    "test_only",
    "production_eligible",
    "parent_cover",
    "selected_parent",
    "refinement",
    "prefix_compatibility",
    "leaves",
    "coverage",
    "batch_policy",
    "batches",
    "claim_preservation",
    "source_binding",
    "solver_invoked",
    "manifest_sha256",
})


class WidenedParentCampaignError(RuntimeError):
    """The selected parent, exact refinement, or schedule is invalid."""


def canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise WidenedParentCampaignError(
            f"not canonical JSON: {exc}"
        ) from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(
    value: Mapping[str, Any], field: str = "manifest_sha256",
) -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise WidenedParentCampaignError("invalid value passed to seal")
    result = dict(value)
    result[field] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def selfhash_valid(
    value: Any, field: str = "manifest_sha256",
) -> bool:
    if type(value) is not dict or not _is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field)
    try:
        return stored == canonical_sha256(unsigned)
    except WidenedParentCampaignError:
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            json_type_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(a, b)
            for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def _source_binding() -> dict[str, Any]:
    sources = {
        "widened_campaign_source": Path(__file__).resolve(),
        "hierarchical_refiner_source": Path(hierarchy.__file__).resolve(),
        "root_cover_source": Path(cube16.__file__).resolve(),
        "optimized_builder_source": Path(cube16.optimized.__file__).resolve(),
    }
    records: list[dict[str, Any]] = []
    for role, path in sorted(sources.items()):
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise WidenedParentCampaignError(
                f"source escapes project: {role}"
            ) from exc
        records.append({
            "role": role,
            "relative_path": relative,
            "sha256": cube16._file_sha256(path),
        })
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "fresh-current-source-sha256-replay-v1",
        "sources": records,
        "source_role_sequence_sha256": canonical_sha256([
            record["role"] for record in records
        ]),
    }, "source_binding_sha256")


def _parent_cover_binding(
    parent_manifest: Mapping[str, Any],
) -> dict[str, Any]:
    payload = canonical_bytes(parent_manifest)
    cubes = parent_manifest.get("cubes", [])
    return {
        "manifest_kind": parent_manifest.get("manifest_kind"),
        "manifest_sha256": parent_manifest.get("manifest_sha256"),
        "canonical_json_bytes": len(payload),
        "canonical_json_sha256": hashlib.sha256(payload).hexdigest(),
        "base_cnf_sha256": parent_manifest.get("base", {}).get("cnf_sha256"),
        "base_dimacs_sha256": parent_manifest.get("base", {}).get(
            "dimacs_sha256"
        ),
        "parent_count": len(cubes) if type(cubes) is list else None,
        "parent_cube_sha256_sequence_sha256": canonical_sha256([
            cube.get("cube_sha256") if type(cube) is dict else None
            for cube in cubes
        ]) if type(cubes) is list else None,
        "coverage_mutually_exclusive": parent_manifest.get(
            "coverage", {}
        ).get("mutually_exclusive"),
        "coverage_exhaustive": parent_manifest.get("coverage", {}).get(
            "exhaustive"
        ),
        "test_only": parent_manifest.get("test_only"),
    }


def _selected_parent_binding(
    parent_manifest: Mapping[str, Any], *, parent_cube_index: int,
) -> dict[str, Any]:
    parent = parent_manifest["cubes"][parent_cube_index]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "parent_cube_index": parent_cube_index,
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "parent_cube_cnf_sha256": parent.get("cube_cnf_sha256"),
        "parent_cube_dimacs_sha256": parent.get("cube_dimacs_sha256"),
        "parent_assignment_sha256": canonical_sha256(
            parent.get("assignment_by_dimacs_variable")
        ),
        "parent_unit_clauses_sha256": canonical_sha256(
            parent.get("unit_clauses")
        ),
    }, "selected_parent_binding_sha256")


def _bits(value: int, width: int) -> list[int]:
    return [
        (value >> (width - position - 1)) & 1
        for position in range(width)
    ]


def _prefix_compatibility(
    old_refinement: Mapping[str, Any],
    widened_refinement: Mapping[str, Any],
) -> dict[str, Any]:
    old_variables = old_refinement.get("refinement", {}).get(
        "variables_dimacs"
    )
    widened_variables = widened_refinement.get("refinement", {}).get(
        "variables_dimacs"
    )
    old_children = old_refinement.get("children")
    widened_children = widened_refinement.get("children")
    if (
        type(old_variables) is not list
        or type(widened_variables) is not list
        or type(old_children) is not list
        or type(widened_children) is not list
        or len(old_variables) != OLD_SPLIT_WIDTH
        or len(widened_variables) != SPLIT_WIDTH
        or len(old_children) != OLD_PREFIX_COUNT
        or len(widened_children) != LEAF_COUNT
    ):
        raise WidenedParentCampaignError(
            "refinement shapes cannot certify width-four prefix compatibility"
        )
    variable_prefix_equal = (
        widened_variables[:OLD_SPLIT_WIDTH] == old_variables
    )
    mappings: list[dict[str, Any]] = []
    all_exact = variable_prefix_equal
    for old_child_index, old_child in enumerate(old_children):
        descendant_indices = [
            old_child_index * SUFFIX_COUNT + suffix
            for suffix in range(SUFFIX_COUNT)
        ]
        descendants = [
            widened_children[index] for index in descendant_indices
        ]
        old_assignment_bits = old_child.get("assignment_bits")
        suffix_bits = [
            child.get("assignment_bits", [])[OLD_SPLIT_WIDTH:]
            if type(child) is dict else None
            for child in descendants
        ]
        prefix_match = bool(
            old_assignment_bits == _bits(old_child_index, OLD_SPLIT_WIDTH)
            and all(
                type(child) is dict
                and child.get("assignment_bits", [])[:OLD_SPLIT_WIDTH]
                == old_assignment_bits
                and child.get("refinement_unit_clauses", [])[
                    :OLD_SPLIT_WIDTH
                ] == old_child.get("refinement_unit_clauses")
                for child in descendants
            )
        )
        suffix_exact = suffix_bits == [
            list(bits) for bits in product((0, 1), repeat=SUFFIX_WIDTH)
        ]
        all_exact = bool(all_exact and prefix_match and suffix_exact)
        mappings.append({
            "old_child_index": old_child_index,
            "old_assignment_bits": old_assignment_bits,
            "widened_child_indices": descendant_indices,
            "widened_suffix_bits": suffix_bits,
            "prefix_assignment_and_units_match": prefix_match,
            "suffix_cover_exhaustive": suffix_exact,
        })
    if not all_exact:
        raise WidenedParentCampaignError(
            "width-six refinement is not an exact extension of width four"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "old_split_width": OLD_SPLIT_WIDTH,
        "widened_split_width": SPLIT_WIDTH,
        "suffix_width": SUFFIX_WIDTH,
        "old_refinement_manifest_sha256": old_refinement.get(
            "manifest_sha256"
        ),
        "widened_refinement_manifest_sha256": widened_refinement.get(
            "manifest_sha256"
        ),
        "old_variables_dimacs": old_variables,
        "widened_variables_dimacs": widened_variables,
        "selected_variable_prefix_equal": variable_prefix_equal,
        "old_prefix_count": OLD_PREFIX_COUNT,
        "descendants_per_old_prefix": SUFFIX_COUNT,
        "mappings": mappings,
        "mapping_sha256": canonical_sha256(mappings),
        "all_old_leaves_exactly_refined": all_exact,
        "solver_invoked": False,
    }, "prefix_compatibility_sha256")


def _leaf_record(
    parent_manifest: Mapping[str, Any],
    refinement: Mapping[str, Any],
    *,
    parent_cube_index: int,
    leaf_index: int,
) -> dict[str, Any]:
    parent = parent_manifest["cubes"][parent_cube_index]
    child = refinement["children"][leaf_index]
    old_prefix = leaf_index // SUFFIX_COUNT
    suffix = leaf_index % SUFFIX_COUNT
    return seal({
        "schema_version": SCHEMA_VERSION,
        "leaf_index": leaf_index,
        "leaf_id": f"paper400-p{parent_cube_index:02d}-w6-c{leaf_index:02d}",
        "parent_cube_index": parent_cube_index,
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "refinement_manifest_sha256": refinement.get("manifest_sha256"),
        "child_index": child.get("child_index"),
        "child_id": child.get("child_id"),
        "child_sha256": child.get("child_sha256"),
        "child_cnf_sha256": child.get("child_cnf_sha256"),
        "child_dimacs_sha256": child.get("child_dimacs_sha256"),
        "child_dimacs_bytes": child.get("child_dimacs_bytes"),
        "child_num_variables": child.get("child_num_variables"),
        "child_num_clauses": child.get("child_num_clauses"),
        "assignment_bits": child.get("assignment_bits"),
        "old_width4_prefix_index": old_prefix,
        "old_width4_prefix_bits": _bits(old_prefix, OLD_SPLIT_WIDTH),
        "suffix_index": suffix,
        "suffix_bits": _bits(suffix, SUFFIX_WIDTH),
        "combined_unit_clauses_sha256": child.get(
            "combined_unit_clauses_sha256"
        ),
    }, "leaf_sha256")


def _scheduled_leaf_indices() -> list[list[int]]:
    return [
        [
            old_prefix * SUFFIX_COUNT + suffix
            for old_prefix in range(
                prefix_group_start,
                prefix_group_start + LANES_PER_BATCH,
            )
        ]
        for prefix_group_start in range(
            0, OLD_PREFIX_COUNT, LANES_PER_BATCH
        )
        for suffix in range(SUFFIX_COUNT)
    ]


def _batch_records(
    leaves: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    batches: list[dict[str, Any]] = []
    for batch_index, leaf_indices in enumerate(_scheduled_leaf_indices()):
        lanes = [
            {
                "lane_index": lane_index,
                "leaf_index": leaf_index,
                "leaf_sha256": leaves[leaf_index]["leaf_sha256"],
                "old_width4_prefix_index": leaves[leaf_index][
                    "old_width4_prefix_index"
                ],
                "suffix_index": leaves[leaf_index]["suffix_index"],
            }
            for lane_index, leaf_index in enumerate(leaf_indices)
        ]
        batches.append(seal({
            "schema_version": SCHEMA_VERSION,
            "batch_index": batch_index,
            "lane_count": LANES_PER_BATCH,
            "old_prefix_group_start": lanes[0][
                "old_width4_prefix_index"
            ],
            "suffix_index": lanes[0]["suffix_index"],
            "leaf_indices": leaf_indices,
            "lanes": lanes,
        }, "batch_sha256"))
    return batches


def _assemble_manifest(
    parent_manifest: Mapping[str, Any],
    old_refinement: Mapping[str, Any],
    refinement: Mapping[str, Any],
    *,
    parent_cube_index: int,
) -> dict[str, Any]:
    children = refinement.get("children")
    if type(children) is not list or len(children) != LEAF_COUNT:
        raise WidenedParentCampaignError("width-six child count is not 64")
    expected_assignments = [
        list(bits) for bits in product((0, 1), repeat=SPLIT_WIDTH)
    ]
    observed_assignments = [
        child.get("assignment_bits") if type(child) is dict else None
        for child in children
    ]
    child_indices = [
        child.get("child_index") if type(child) is dict else None
        for child in children
    ]
    coverage = refinement.get("coverage", {})
    exact = bool(
        child_indices == list(range(LEAF_COUNT))
        and observed_assignments == expected_assignments
        and coverage.get("expected_child_count") == LEAF_COUNT
        and coverage.get("observed_child_count") == LEAF_COUNT
        and coverage.get("expected_pair_count") == PAIR_COUNT
        and coverage.get("pair_count_checked") == PAIR_COUNT
        and coverage.get("mutually_exclusive") is True
        and coverage.get("exhaustive") is True
    )
    if not exact:
        raise WidenedParentCampaignError(
            "width-six refinement failed exact 64-leaf checks"
        )
    compatibility = _prefix_compatibility(old_refinement, refinement)
    leaves = [
        _leaf_record(
            parent_manifest,
            refinement,
            parent_cube_index=parent_cube_index,
            leaf_index=leaf_index,
        )
        for leaf_index in range(LEAF_COUNT)
    ]
    batches = _batch_records(leaves)
    flat = [
        leaf_index
        for batch in batches
        for leaf_index in batch["leaf_indices"]
    ]
    batch_partition_exact = bool(
        len(flat) == LEAF_COUNT
        and len(set(flat)) == LEAF_COUNT
        and sorted(flat) == list(range(LEAF_COUNT))
    )
    if not batch_partition_exact:
        raise WidenedParentCampaignError(
            "interleaved schedule is not an exact leaf partition"
        )
    test_only = parent_manifest.get("test_only")
    if (
        type(test_only) is not bool
        or old_refinement.get("test_only") is not test_only
        or refinement.get("test_only") is not test_only
    ):
        raise WidenedParentCampaignError(
            "parent/refinement authority mismatch"
        )
    authority = (
        AUTHORITY_TEST_ONLY if test_only
        else AUTHORITY_PRODUCTION_CANDIDATE
    )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "formulation": FORMULATION,
        "authority": authority,
        "test_only": test_only,
        "production_eligible": False,
        "parent_cover": _parent_cover_binding(parent_manifest),
        "selected_parent": _selected_parent_binding(
            parent_manifest, parent_cube_index=parent_cube_index
        ),
        "refinement": dict(refinement),
        "prefix_compatibility": compatibility,
        "leaves": leaves,
        "coverage": {
            "method": "explicit-selected-parent-cartesian-width6-replay-v1",
            "split_width": SPLIT_WIDTH,
            "expected_leaf_count": LEAF_COUNT,
            "observed_leaf_count": len(leaves),
            "expected_pair_count": PAIR_COUNT,
            "pair_count_checked": coverage.get("pair_count_checked"),
            "assignments_sha256": canonical_sha256(observed_assignments),
            "leaf_sha256_sequence_sha256": canonical_sha256([
                leaf["leaf_sha256"] for leaf in leaves
            ]),
            "mutually_exclusive": True,
            "exhaustive": True,
            "parent_formula_equivalence_certified": True,
            "proof": (
                "all 2^6 assignments occur once in lexicographic order; "
                "distinct children disagree on a selected physical variable"
            ),
            "solver_invoked": False,
        },
        "batch_policy": {
            "lane_count": LANES_PER_BATCH,
            "expected_batch_count": BATCH_COUNT,
            "observed_batch_count": len(batches),
            "ordering": (
                "groups of four consecutive old width4 prefixes; within each "
                "group enumerate the common two-bit suffix 0..3"
            ),
            "first_four_batches": _scheduled_leaf_indices()[:4],
            "all_64_leaves_appear_exactly_once": True,
            "flattened_leaf_indices_sha256": canonical_sha256(flat),
            "batch_sha256_sequence_sha256": canonical_sha256([
                batch["batch_sha256"] for batch in batches
            ]),
            "solver_invoked": False,
        },
        "batches": batches,
        "claim_preservation": {
            "quantum_code_changed": False,
            "base_cnf_changed": False,
            "only_physical_operator_unit_clauses_added": True,
            "all_64_authenticated_unsat_leaves_imply_selected_parent_unsat": True,
            "one_verified_sat_leaf_implies_selected_parent_sat": True,
            "this_manifest_alone_proves_selected_parent_unsat": False,
            "this_manifest_alone_proves_distance_lower_bound": False,
            "inherited_distance_lower_bound_target": parent_manifest.get(
                "aggregation_policy", {}
            ).get("all_unsat_distance_lower_bound"),
        },
        "source_binding": _source_binding(),
        "solver_invoked": False,
    })


def _verified_refinement(
    refinement: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    split_width: int,
    strict_base: bool,
) -> None:
    replay = hierarchy.verify_refinement_manifest(
        refinement,
        parent_manifest,
        instance,
        strict_base=strict_base,
        expected_parent_cube_index=parent_cube_index,
        expected_split_width=split_width,
    )
    if (
        replay.get("valid") is not True
        or replay.get("coverage_mutually_exclusive") is not True
        or replay.get("coverage_exhaustive") is not True
    ):
        raise WidenedParentCampaignError(
            f"width-{split_width} refinement failed fresh exact replay: "
            f"{replay.get('binding_failures')}"
        )


def build_campaign_manifest(
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Build a fresh width-six exact campaign for one root-cover parent."""

    if type(strict_base) is not bool:
        raise WidenedParentCampaignError("strict_base must be a strict boolean")
    if (
        type(parent_cube_index) is not int
        or not 0 <= parent_cube_index < PARENT_COUNT
    ):
        raise WidenedParentCampaignError(
            "parent_cube_index must be an integer in 0..15"
        )
    parent_replay = cube16.verify_coverage_manifest(
        parent_manifest, instance, strict_base=strict_base
    )
    if (
        parent_replay.get("valid") is not True
        or parent_replay.get("coverage_mutually_exclusive") is not True
        or parent_replay.get("coverage_exhaustive") is not True
        or type(parent_manifest.get("cubes")) is not list
        or len(parent_manifest["cubes"]) != PARENT_COUNT
    ):
        raise WidenedParentCampaignError(
            "parent 16-cube cover failed fresh exact replay"
        )
    old_refinement = hierarchy.build_refinement_manifest(
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        split_width=OLD_SPLIT_WIDTH,
        strict_base=strict_base,
    )
    refinement = hierarchy.build_refinement_manifest(
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        split_width=SPLIT_WIDTH,
        strict_base=strict_base,
    )
    _verified_refinement(
        old_refinement,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        split_width=OLD_SPLIT_WIDTH,
        strict_base=strict_base,
    )
    _verified_refinement(
        refinement,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        split_width=SPLIT_WIDTH,
        strict_base=strict_base,
    )
    return _assemble_manifest(
        parent_manifest,
        old_refinement,
        refinement,
        parent_cube_index=parent_cube_index,
    )


def verify_campaign_manifest(
    manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Freshly rebuild and type-exact compare one widened campaign."""

    if type(strict_base) is not bool:
        raise WidenedParentCampaignError("strict_base must be a strict boolean")
    raw = dict(manifest) if type(manifest) is dict else {}
    failures: list[str] = []
    if set(raw) != MANIFEST_FIELDS:
        failures.append("manifest field set mismatch")
    if not selfhash_valid(raw):
        failures.append("manifest self-hash mismatch")
    expected_authority = (
        AUTHORITY_PRODUCTION_CANDIDATE if strict_base
        else AUTHORITY_TEST_ONLY
    )
    if raw.get("authority") != expected_authority:
        failures.append("campaign authority mismatch")
    if raw.get("test_only") is not (not strict_base):
        failures.append("campaign test_only mismatch")
    if raw.get("production_eligible") is not False:
        failures.append("cover manifest cannot claim a completed proof")
    selected_parent = raw.get("selected_parent")
    if (
        type(selected_parent) is not dict
        or selected_parent.get("parent_cube_index") != parent_cube_index
    ):
        failures.append("selected parent does not match caller expectation")
    refinement = raw.get("refinement")
    refinement_parameters = (
        refinement.get("refinement")
        if type(refinement) is dict
        and type(refinement.get("refinement")) is dict
        else {}
    )
    if (
        type(refinement) is not dict
        or refinement_parameters.get("variable_count") != SPLIT_WIDTH
    ):
        failures.append("campaign does not contain a width-six refinement")
    leaves = raw.get("leaves")
    if type(leaves) is not list or [
        leaf.get("leaf_index") if type(leaf) is dict else None
        for leaf in leaves
    ] != list(range(LEAF_COUNT)):
        failures.append("leaves are missing, duplicated, or reordered")
    batches = raw.get("batches")
    flat: list[Any] = []
    batch_indices: list[Any] = []
    batch_shape_valid = type(batches) is list
    if type(batches) is list:
        for batch in batches:
            if type(batch) is not dict:
                batch_shape_valid = False
                continue
            batch_indices.append(batch.get("batch_index"))
            indices = batch.get("leaf_indices")
            if type(indices) is not list:
                batch_shape_valid = False
                continue
            flat.extend(indices)
    if (
        (len(batches) if type(batches) is list else -1) != BATCH_COUNT
        or batch_indices != list(range(BATCH_COUNT))
    ):
        failures.append("batch count or ordering mismatch")
    flat_indices_are_strict_integers = all(
        type(index) is int for index in flat
    )
    if (
        not batch_shape_valid
        or not flat_indices_are_strict_integers
        or len(flat) != LEAF_COUNT
        or (
            flat_indices_are_strict_integers
            and len(set(flat)) != LEAF_COUNT
        )
        or sorted(flat) != list(range(LEAF_COUNT))
    ):
        failures.append("batch leaves are missing, duplicated, or substituted")
    if type(batches) is not list or [
        batch.get("leaf_indices") if type(batch) is dict else None
        for batch in batches[:4]
    ] != _scheduled_leaf_indices()[:4]:
        failures.append("first four interleaved batches mismatch")

    expected: dict[str, Any] | None = None
    try:
        expected = build_campaign_manifest(
            parent_manifest,
            instance,
            parent_cube_index=parent_cube_index,
            strict_base=strict_base,
        )
    except (
        WidenedParentCampaignError,
        hierarchy.HierarchicalCubeError,
        cube16.Cube16Error,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
    ) as exc:
        failures.append(f"fresh campaign replay failed: {exc}")
    if expected is not None and not json_type_equal(raw, expected):
        failures.append("manifest is not exact current-source canonical replay")
    coverage_record = (
        raw.get("coverage") if type(raw.get("coverage")) is dict else {}
    )
    compatibility_record = (
        raw.get("prefix_compatibility")
        if type(raw.get("prefix_compatibility")) is dict else {}
    )
    batch_policy_record = (
        raw.get("batch_policy")
        if type(raw.get("batch_policy")) is dict else {}
    )
    valid = not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-widened-parent-campaign-verification-v1",
        "campaign_manifest_sha256": raw.get("manifest_sha256"),
        "expected_manifest_sha256": (
            expected.get("manifest_sha256") if expected is not None else None
        ),
        "parent_cube_index": parent_cube_index,
        "valid": valid,
        "binding_failures": failures,
        "leaf_count": len(leaves) if type(leaves) is list else None,
        "batch_count": len(batches) if type(batches) is list else None,
        "mutually_exclusive": bool(
            valid and coverage_record.get("mutually_exclusive") is True
        ),
        "exhaustive": bool(
            valid and coverage_record.get("exhaustive") is True
        ),
        "width4_prefix_compatible": bool(
            valid
            and compatibility_record.get(
                "all_old_leaves_exactly_refined"
            ) is True
        ),
        "batch_partition_exact": bool(
            valid
            and batch_policy_record.get(
                "all_64_leaves_appear_exactly_once"
            ) is True
        ),
        "solver_invoked": False,
        "launch_authorized_by_this_record": False,
        "publication_certificate": False,
    }, "record_sha256")


def verified_child_dimacs(
    manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    leaf_index: int,
    strict_base: bool = True,
) -> bytes:
    """Materialize one wider child only after complete campaign replay."""

    if type(leaf_index) is not int or not 0 <= leaf_index < LEAF_COUNT:
        raise WidenedParentCampaignError("leaf_index must be in 0..63")
    replay = verify_campaign_manifest(
        manifest,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if replay.get("valid") is not True:
        raise WidenedParentCampaignError(
            f"campaign failed exact replay: {replay.get('binding_failures')}"
        )
    payload = hierarchy.verified_child_dimacs(
        manifest["refinement"],
        parent_manifest,
        instance,
        child_index=leaf_index,
        strict_base=strict_base,
        expected_parent_cube_index=parent_cube_index,
        expected_split_width=SPLIT_WIDTH,
    )
    leaf = manifest["leaves"][leaf_index]
    if (
        leaf.get("child_index") != leaf_index
        or len(payload) != leaf.get("child_dimacs_bytes")
        or hashlib.sha256(payload).hexdigest()
        != leaf.get("child_dimacs_sha256")
    ):
        raise WidenedParentCampaignError(
            "on-demand child DIMACS binding mismatch"
        )
    return payload


def verified_four_lane_batch_plan(
    manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Return all 16 immutable batches after a full fresh replay."""

    replay = verify_campaign_manifest(
        manifest,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if replay.get("valid") is not True:
        raise WidenedParentCampaignError(
            f"campaign failed exact replay: {replay.get('binding_failures')}"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-widened-parent-four-lane-plan-v1",
        "campaign_manifest_sha256": manifest["manifest_sha256"],
        "parent_cube_index": parent_cube_index,
        "lane_count": LANES_PER_BATCH,
        "batch_count": BATCH_COUNT,
        "batches": [dict(batch) for batch in manifest["batches"]],
        "all_64_leaves_scheduled_exactly_once": True,
        "solver_invoked": False,
        "launch_authorized_by_this_record": False,
    }, "record_sha256")


__all__ = [
    "AUTHORITY_PRODUCTION_CANDIDATE",
    "AUTHORITY_TEST_ONLY",
    "BATCH_COUNT",
    "LANES_PER_BATCH",
    "LEAF_COUNT",
    "MANIFEST_FIELDS",
    "MANIFEST_KIND",
    "OLD_PREFIX_COUNT",
    "OLD_SPLIT_WIDTH",
    "PAIR_COUNT",
    "PARENT_COUNT",
    "SPLIT_WIDTH",
    "SUFFIX_COUNT",
    "SUFFIX_WIDTH",
    "WidenedParentCampaignError",
    "build_campaign_manifest",
    "canonical_bytes",
    "canonical_sha256",
    "json_type_equal",
    "seal",
    "selfhash_valid",
    "verified_child_dimacs",
    "verified_four_lane_batch_plan",
    "verify_campaign_manifest",
]
