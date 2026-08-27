#!/usr/bin/env python3
"""Solver-free nested width-ten cover for paper400 parent 000.

This module extends the existing authenticated width-six campaign by four
common physical-operator variables.  Every width-six leaf is replaced by the
sixteen assignments to those variables, yielding 64 * 16 = 1024 leaves.

The global cover is certified hierarchically.  Leaves below different
width-six prefixes are separated by the already authenticated width-six
cover; leaves below one prefix are separated by the local four-bit Cartesian
cover.  This avoids materializing all 523,776 global leaf pairs.  No solver is
imported or invoked, and this manifest alone is not an UNSAT proof.
"""

from __future__ import annotations

import hashlib
import json
from itertools import combinations, product
from pathlib import Path
from typing import Any, Mapping, Sequence

from investigations import paper400_dic5_widened_parent_campaign_v1 as width6


hierarchy = width6.hierarchy
cube16 = width6.cube16
PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 1
MANIFEST_KIND = "paper400-dic5-nested-width10-parent000-campaign-v1"
FORMULATION = "width6-leaf-times-common-width4-cartesian-refinement-v1"
PREVIEW_KIND = "paper400-dic5-parent000-width10-selection-preview-v1"
VERIFICATION_KIND = "paper400-dic5-nested-width10-campaign-verification-v1"
AUTHORITY_PRODUCTION_CANDIDATE = width6.AUTHORITY_PRODUCTION_CANDIDATE
AUTHORITY_TEST_ONLY = width6.AUTHORITY_TEST_ONLY

TARGET_PARENT_CUBE_INDEX = 0
WIDTH6_SPLIT_WIDTH = 6
EXTENSION_WIDTH = 4
SPLIT_WIDTH = WIDTH6_SPLIT_WIDTH + EXTENSION_WIDTH
WIDTH6_LEAF_COUNT = 1 << WIDTH6_SPLIT_WIDTH
LOCAL_CHILD_COUNT = 1 << EXTENSION_WIDTH
LEAF_COUNT = WIDTH6_LEAF_COUNT * LOCAL_CHILD_COUNT
LOCAL_PAIR_COUNT = LOCAL_CHILD_COUNT * (LOCAL_CHILD_COUNT - 1) // 2
WIDTH6_PAIR_COUNT = WIDTH6_LEAF_COUNT * (WIDTH6_LEAF_COUNT - 1) // 2
WITHIN_PREFIX_PAIR_COUNT = WIDTH6_LEAF_COUNT * LOCAL_PAIR_COUNT
CROSS_PREFIX_PAIR_COUNT = (
    WIDTH6_PAIR_COUNT * LOCAL_CHILD_COUNT * LOCAL_CHILD_COUNT
)
GLOBAL_PAIR_COUNT = LEAF_COUNT * (LEAF_COUNT - 1) // 2

EXPECTED_PARENT000_WIDTH6_VARIABLES = (236, 254, 271, 274, 280, 321)
EXPECTED_PARENT000_EXTENSION_VARIABLES = (324, 342, 345, 352)
EXPECTED_PARENT000_WIDTH10_VARIABLES = (
    EXPECTED_PARENT000_WIDTH6_VARIABLES
    + EXPECTED_PARENT000_EXTENSION_VARIABLES
)

MANIFEST_FIELDS = frozenset({
    "schema_version",
    "manifest_kind",
    "formulation",
    "authority",
    "test_only",
    "production_eligible",
    "parent_cover",
    "selected_parent",
    "width6_campaign",
    "selection_preview",
    "refinement",
    "leaves",
    "local_covers",
    "global_coverage",
    "resource_profile",
    "claim_preservation",
    "source_binding",
    "solver_invoked",
    "manifest_sha256",
})

VERIFICATION_FIELDS = frozenset({
    "schema_version",
    "kind",
    "campaign_manifest_sha256",
    "expected_manifest_sha256",
    "parent_cube_index",
    "valid",
    "binding_failures",
    "width6_prefix_count",
    "leaf_count",
    "mutually_exclusive",
    "exhaustive",
    "parent000_formula_equivalence_certified",
    "solver_invoked",
    "launch_authorized_by_this_record",
    "publication_certificate",
    "record_sha256",
})


class NestedWidth10CampaignError(RuntimeError):
    """A width-six binding, nested child, or cover is malformed."""


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
        raise NestedWidth10CampaignError(f"not canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(
    value: Mapping[str, Any], field: str = "manifest_sha256",
) -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise NestedWidth10CampaignError("invalid value passed to seal")
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
    except NestedWidth10CampaignError:
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


def _bits(value: int, width: int) -> list[int]:
    if type(value) is not int or type(width) is not int:
        raise NestedWidth10CampaignError("bit decomposition requires integers")
    if width < 1 or not 0 <= value < (1 << width):
        raise NestedWidth10CampaignError("bit decomposition is out of range")
    return [
        (value >> (width - position - 1)) & 1
        for position in range(width)
    ]


def _source_binding() -> dict[str, Any]:
    sources = {
        "nested_width10_campaign_source": Path(__file__).resolve(),
        "width6_campaign_source": Path(width6.__file__).resolve(),
        "hierarchical_refiner_source": Path(hierarchy.__file__).resolve(),
        "root_cover_source": Path(cube16.__file__).resolve(),
        "optimized_builder_source": Path(cube16.optimized.__file__).resolve(),
    }
    records: list[dict[str, Any]] = []
    for role, path in sorted(sources.items()):
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise NestedWidth10CampaignError(
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


def _require_target_parent(parent_cube_index: int) -> None:
    if type(parent_cube_index) is not int or parent_cube_index != 0:
        raise NestedWidth10CampaignError(
            "this campaign is scoped exactly to parent_cube_index 0"
        )


def _verified_width6_campaign(
    campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int,
    strict_base: bool,
) -> dict[str, Any]:
    _require_target_parent(parent_cube_index)
    if type(strict_base) is not bool:
        raise NestedWidth10CampaignError("strict_base must be a strict boolean")
    replay = width6.verify_campaign_manifest(
        campaign,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if (
        replay.get("valid") is not True
        or replay.get("mutually_exclusive") is not True
        or replay.get("exhaustive") is not True
        or replay.get("width4_prefix_compatible") is not True
        or replay.get("leaf_count") != WIDTH6_LEAF_COUNT
    ):
        raise NestedWidth10CampaignError(
            f"width-six campaign failed exact replay: "
            f"{replay.get('binding_failures')}"
        )
    if (
        campaign.get("manifest_kind") != width6.MANIFEST_KIND
        or campaign.get("selected_parent", {}).get("parent_cube_index")
        != parent_cube_index
        or campaign.get("refinement", {}).get("refinement", {}).get(
            "variable_count"
        ) != WIDTH6_SPLIT_WIDTH
        or len(campaign.get("leaves", [])) != WIDTH6_LEAF_COUNT
    ):
        raise NestedWidth10CampaignError("width-six campaign shape mismatch")
    return replay


def _selection_ranking(
    base_clauses: Sequence[Sequence[int]],
    parent_assignment: Mapping[int, int],
) -> tuple[list[dict[str, int]], dict[str, Any]]:
    residual, profile = hierarchy._restrict_without_propagation(
        base_clauses, parent_assignment
    )
    candidates = [
        variable
        for variable in range(1, cube16.EXPECTED_OPERATOR_VARIABLES + 1)
        if variable not in parent_assignment
    ]
    positive = {variable: 0 for variable in candidates}
    negative = {variable: 0 for variable in candidates}
    incidence = {variable: set() for variable in candidates}
    candidate_set = set(candidates)
    for clause_index, clause in enumerate(residual):
        for raw_literal in clause:
            literal = int(raw_literal)
            variable = abs(literal)
            if variable not in candidate_set:
                continue
            if literal > 0:
                positive[variable] += 1
            else:
                negative[variable] += 1
            incidence[variable].add(clause_index)
    ranking = [
        {
            "dimacs_variable": variable,
            "positive_occurrences": positive[variable],
            "negative_occurrences": negative[variable],
            "min_sign_occurrences": min(
                positive[variable], negative[variable]
            ),
            "sign_imbalance": abs(
                positive[variable] - negative[variable]
            ),
            "total_occurrences": positive[variable] + negative[variable],
            "incident_clause_count": len(incidence[variable]),
        }
        for variable in candidates
    ]
    ranking.sort(key=lambda record: (
        -record["min_sign_occurrences"],
        record["sign_imbalance"],
        -record["total_occurrences"],
        record["dimacs_variable"],
    ))
    return ranking, profile


def _selection_preview_from_verified(
    campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    strict_base: bool,
) -> dict[str, Any]:
    parent = parent_manifest["cubes"][TARGET_PARENT_CUBE_INDEX]
    parent_assignment = hierarchy._assignment_from_records(
        parent["assignment_by_dimacs_variable"]
    )
    ranking, restriction_profile = _selection_ranking(
        instance.cnf["clauses"], parent_assignment
    )
    if len(ranking) < SPLIT_WIDTH:
        raise NestedWidth10CampaignError("fewer than ten physical candidates")
    width6_refinement = campaign["refinement"]
    width6_variables = width6_refinement["refinement"]["variables_dimacs"]
    selection = width6_refinement["refinement"]["selection_certificate"]
    ranking_sha256 = hierarchy.canonical_sha256(ranking)
    selected_width10 = [
        int(record["dimacs_variable"])
        for record in ranking[:SPLIT_WIDTH]
    ]
    proposed_extension = selected_width10[WIDTH6_SPLIT_WIDTH:]
    if (
        width6_variables != selected_width10[:WIDTH6_SPLIT_WIDTH]
        or selection.get("candidate_ranking_sha256") != ranking_sha256
        or not json_type_equal(
            selection.get("selected_records"),
            ranking[:WIDTH6_SPLIT_WIDTH],
        )
    ):
        raise NestedWidth10CampaignError(
            "independent ranking does not exactly replay width-six prefix"
        )
    if (
        len(set(selected_width10)) != SPLIT_WIDTH
        or set(selected_width10) & set(parent_assignment)
        or any(
            type(variable) is not int
            or not 1 <= variable <= cube16.EXPECTED_OPERATOR_VARIABLES
            for variable in selected_width10
        )
    ):
        raise NestedWidth10CampaignError(
            "width-ten selection is not ten new physical variables"
        )
    production_ranking_required = bool(strict_base)
    production_ranking_matches = (
        tuple(selected_width10) == EXPECTED_PARENT000_WIDTH10_VARIABLES
    )
    if production_ranking_required and not production_ranking_matches:
        raise NestedWidth10CampaignError(
            "production parent000 width-ten ranking changed"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": PREVIEW_KIND,
        "parent_cube_index": TARGET_PARENT_CUBE_INDEX,
        "parent_manifest_sha256": parent_manifest.get("manifest_sha256"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "width6_campaign_sha256": campaign.get("manifest_sha256"),
        "width6_refinement_manifest_sha256": width6_refinement.get(
            "manifest_sha256"
        ),
        "selection_method": selection.get("method"),
        "candidate_count": len(ranking),
        "candidate_ranking_sha256": ranking_sha256,
        "parent_restriction_profile": restriction_profile,
        "width6_variables_dimacs": list(width6_variables),
        "proposed_extension_variables_dimacs": proposed_extension,
        "proposed_width10_variables_dimacs": selected_width10,
        "width6_prefix_exact": True,
        "production_expected_width10_variables_dimacs": list(
            EXPECTED_PARENT000_WIDTH10_VARIABLES
        ),
        "production_ranking_required": production_ranking_required,
        "production_ranking_matches": production_ranking_matches,
        "selection_depends_on_solver_state": False,
        "solver_invoked": False,
    }, "record_sha256")


def preview_extension_variables(
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int = TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Replay ranking and return the four proposed variables without leaves."""

    _verified_width6_campaign(
        width6_campaign,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    return _selection_preview_from_verified(
        width6_campaign,
        parent_manifest,
        instance,
        strict_base=strict_base,
    )


def _confirmed_extension(
    value: Sequence[int], preview: Mapping[str, Any],
) -> list[int]:
    if type(value) not in {list, tuple}:
        raise NestedWidth10CampaignError(
            "confirmed extension variables must be a list or tuple"
        )
    confirmed = list(value)
    if (
        len(confirmed) != EXTENSION_WIDTH
        or any(type(variable) is not int for variable in confirmed)
        or confirmed != preview.get("proposed_extension_variables_dimacs")
    ):
        raise NestedWidth10CampaignError(
            "confirmed extension variables do not match the exact preview"
        )
    return confirmed


def _width6_campaign_binding(campaign: Mapping[str, Any]) -> dict[str, Any]:
    leaves = campaign["leaves"]
    payload = canonical_bytes(campaign)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": campaign.get("manifest_kind"),
        "manifest_sha256": campaign.get("manifest_sha256"),
        "canonical_json_bytes": len(payload),
        "canonical_json_sha256": hashlib.sha256(payload).hexdigest(),
        "selected_parent_binding_sha256": campaign.get(
            "selected_parent", {}
        ).get("selected_parent_binding_sha256"),
        "refinement_manifest_sha256": campaign.get("refinement", {}).get(
            "manifest_sha256"
        ),
        "source_binding_sha256": campaign.get("source_binding", {}).get(
            "source_binding_sha256"
        ),
        "width6_leaf_count": len(leaves),
        "width6_leaf_sha256_sequence_sha256": canonical_sha256([
            leaf.get("leaf_sha256") for leaf in leaves
        ]),
        "width6_child_sha256_sequence_sha256": canonical_sha256([
            leaf.get("child_sha256") for leaf in leaves
        ]),
        "coverage_mutually_exclusive": campaign.get("coverage", {}).get(
            "mutually_exclusive"
        ),
        "coverage_exhaustive": campaign.get("coverage", {}).get(
            "exhaustive"
        ),
        "test_only": campaign.get("test_only"),
    }, "width6_campaign_binding_sha256")


def _selected_parent_binding(
    parent_manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
) -> dict[str, Any]:
    parent = parent_manifest["cubes"][TARGET_PARENT_CUBE_INDEX]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "parent_cube_index": TARGET_PARENT_CUBE_INDEX,
        "parent_manifest_sha256": parent_manifest.get("manifest_sha256"),
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
        "width6_selected_parent_binding_sha256": width6_campaign.get(
            "selected_parent", {}
        ).get("selected_parent_binding_sha256"),
    }, "selected_parent_binding_sha256")


def _validated_width6_leaf(
    campaign: Mapping[str, Any], leaf_index: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    leaf = campaign["leaves"][leaf_index]
    child = campaign["refinement"]["children"][leaf_index]
    expected_bits = _bits(leaf_index, WIDTH6_SPLIT_WIDTH)
    if (
        leaf.get("leaf_index") != leaf_index
        or leaf.get("child_index") != leaf_index
        or child.get("child_index") != leaf_index
        or leaf.get("assignment_bits") != expected_bits
        or child.get("assignment_bits") != expected_bits
        or leaf.get("child_sha256") != child.get("child_sha256")
        or leaf.get("child_cnf_sha256") != child.get("child_cnf_sha256")
        or leaf.get("child_dimacs_sha256")
        != child.get("child_dimacs_sha256")
        or leaf.get("combined_unit_clauses_sha256")
        != child.get("combined_unit_clauses_sha256")
    ):
        raise NestedWidth10CampaignError(
            f"width-six leaf/child binding mismatch at {leaf_index}"
        )
    return dict(leaf), dict(child)


def _nested_leaf_record(
    *,
    instance: Any,
    base_clauses: Sequence[Sequence[int]],
    width6_campaign: Mapping[str, Any],
    width6_leaf_index: int,
    local_child_index: int,
    extension_variables: Sequence[int],
    extension_bits: Sequence[int],
) -> tuple[dict[str, Any], bytes]:
    width6_leaf, width6_child = _validated_width6_leaf(
        width6_campaign, width6_leaf_index
    )
    expected_local_bits = _bits(local_child_index, EXTENSION_WIDTH)
    bit_list = list(extension_bits)
    variables = list(extension_variables)
    if bit_list != expected_local_bits or len(variables) != EXTENSION_WIDTH:
        raise NestedWidth10CampaignError("local child assignment mismatch")
    width6_assignment = hierarchy._assignment_from_records(
        width6_child["combined_assignment_by_dimacs_variable"]
    )
    if set(variables) & set(width6_assignment):
        raise NestedWidth10CampaignError(
            "extension variable reassigns the width-six child"
        )
    extension_assignment = dict(zip(variables, bit_list, strict=True))
    extension_units = [
        [variable if extension_assignment[variable] else -variable]
        for variable in variables
    ]
    width6_units = [
        [int(literal) for literal in clause]
        for clause in width6_child["combined_unit_clauses"]
    ]
    combined_units = width6_units + extension_units
    clauses = list(base_clauses) + combined_units
    num_variables = int(instance.cnf["num_variables"])
    dimacs = cube16._render_dimacs(
        num_variables=num_variables, clauses=clauses
    )
    child_cnf_sha256 = cube16._cnf_sha256(
        num_variables=num_variables,
        clauses=clauses,
        native_atmost=None,
    )
    global_leaf_index = (
        width6_leaf_index * LOCAL_CHILD_COUNT + local_child_index
    )
    width6_bits = list(width6_child["assignment_bits"])
    full_bits = width6_bits + bit_list
    if full_bits != _bits(global_leaf_index, SPLIT_WIDTH):
        raise NestedWidth10CampaignError(
            "global leaf index/ten-bit assignment mismatch"
        )
    combined_assignment = dict(width6_assignment)
    combined_assignment.update(extension_assignment)
    parent_cube_index = width6_leaf.get("parent_cube_index")
    record = seal({
        "schema_version": SCHEMA_VERSION,
        "global_leaf_index": global_leaf_index,
        "global_leaf_id": (
            f"paper400-p{parent_cube_index:02d}-w10-c{global_leaf_index:04d}"
        ),
        "parent_cube_index": parent_cube_index,
        "width6_campaign_sha256": width6_campaign.get("manifest_sha256"),
        "width6_refinement_manifest_sha256": width6_campaign.get(
            "refinement", {}
        ).get("manifest_sha256"),
        "width6_leaf_index": width6_leaf_index,
        "width6_leaf_id": width6_leaf.get("leaf_id"),
        "width6_leaf_sha256": width6_leaf.get("leaf_sha256"),
        "width6_child_index": width6_child.get("child_index"),
        "width6_child_id": width6_child.get("child_id"),
        "width6_child_sha256": width6_child.get("child_sha256"),
        "width6_child_cnf_sha256": width6_child.get("child_cnf_sha256"),
        "width6_child_dimacs_sha256": width6_child.get(
            "child_dimacs_sha256"
        ),
        "local_child_index": local_child_index,
        "width6_assignment_bits": width6_bits,
        "extension_assignment_bits": bit_list,
        "assignment_bits": full_bits,
        "extension_assignment_by_dimacs_variable": [
            {"dimacs_variable": variable, "value": extension_assignment[variable]}
            for variable in variables
        ],
        "combined_assignment_by_dimacs_variable": [
            {"dimacs_variable": variable, "value": combined_assignment[variable]}
            for variable in sorted(combined_assignment)
        ],
        "width6_combined_unit_clauses": width6_units,
        "width6_combined_unit_clauses_sha256": canonical_sha256(width6_units),
        "extension_unit_clauses": extension_units,
        "combined_unit_clauses": combined_units,
        "combined_unit_clauses_sha256": canonical_sha256(combined_units),
        "child_cnf_sha256": child_cnf_sha256,
        "child_dimacs_sha256": hashlib.sha256(dimacs).hexdigest(),
        "child_num_variables": num_variables,
        "child_num_clauses": len(clauses),
        "child_dimacs_bytes": len(dimacs),
        "dimacs_relative_path": (
            f"children/leaf-{global_leaf_index:04d}.cnf"
        ),
    }, "leaf_sha256")
    return record, dimacs


def _local_cover_record(
    width6_leaf: Mapping[str, Any], descendants: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    width6_leaf_index = width6_leaf["leaf_index"]
    expected_indices = list(range(
        width6_leaf_index * LOCAL_CHILD_COUNT,
        (width6_leaf_index + 1) * LOCAL_CHILD_COUNT,
    ))
    observed_indices = [leaf.get("global_leaf_index") for leaf in descendants]
    expected_assignments = [
        list(bits) for bits in product((0, 1), repeat=EXTENSION_WIDTH)
    ]
    observed_assignments = [
        leaf.get("extension_assignment_bits") for leaf in descendants
    ]
    separations: list[dict[str, Any]] = []
    for left, right in combinations(descendants, 2):
        differing_positions = [
            position
            for position, (left_bit, right_bit) in enumerate(zip(
                left["extension_assignment_bits"],
                right["extension_assignment_bits"],
                strict=True,
            ))
            if left_bit != right_bit
        ]
        separations.append({
            "left_local_child_index": left["local_child_index"],
            "right_local_child_index": right["local_child_index"],
            "differing_positions": differing_positions,
        })
    exact = bool(
        observed_indices == expected_indices
        and observed_assignments == expected_assignments
        and len(separations) == LOCAL_PAIR_COUNT
        and all(record["differing_positions"] for record in separations)
    )
    if not exact:
        raise NestedWidth10CampaignError(
            f"local four-bit cover failed at width-six leaf {width6_leaf_index}"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "width6_leaf_index": width6_leaf_index,
        "width6_leaf_sha256": width6_leaf.get("leaf_sha256"),
        "width6_child_sha256": width6_leaf.get("child_sha256"),
        "extension_width": EXTENSION_WIDTH,
        "expected_child_count": LOCAL_CHILD_COUNT,
        "observed_child_count": len(descendants),
        "global_leaf_indices": expected_indices,
        "extension_assignments_sha256": canonical_sha256(
            observed_assignments
        ),
        "descendant_leaf_sha256_sequence_sha256": canonical_sha256([
            leaf["leaf_sha256"] for leaf in descendants
        ]),
        "descendant_cnf_sha256_sequence_sha256": canonical_sha256([
            leaf["child_cnf_sha256"] for leaf in descendants
        ]),
        "expected_pair_count": LOCAL_PAIR_COUNT,
        "pair_count_checked": len(separations),
        "pairwise_separation_sha256": canonical_sha256(separations),
        "mutually_exclusive": True,
        "exhaustive": True,
        "equivalence_statement": (
            "W6 iff OR_b(W6 AND common_extension_assignment_b)"
        ),
        "solver_invoked": False,
    }, "local_cover_sha256")


def build_campaign_manifest(
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    confirmed_extension_variables: Sequence[int],
    parent_cube_index: int = TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Build all 1024 nested leaves after explicit variable confirmation."""

    _verified_width6_campaign(
        width6_campaign,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    preview = _selection_preview_from_verified(
        width6_campaign,
        parent_manifest,
        instance,
        strict_base=strict_base,
    )
    extension_variables = _confirmed_extension(
        confirmed_extension_variables, preview
    )
    width6_variables = preview["width6_variables_dimacs"]
    width10_variables = width6_variables + extension_variables
    base_clauses = [
        [int(literal) for literal in clause]
        for clause in instance.cnf["clauses"]
    ]
    leaves: list[dict[str, Any]] = []
    local_covers: list[dict[str, Any]] = []
    for width6_leaf_index in range(WIDTH6_LEAF_COUNT):
        descendants: list[dict[str, Any]] = []
        for local_child_index, bits in enumerate(
            product((0, 1), repeat=EXTENSION_WIDTH)
        ):
            leaf, _ = _nested_leaf_record(
                instance=instance,
                base_clauses=base_clauses,
                width6_campaign=width6_campaign,
                width6_leaf_index=width6_leaf_index,
                local_child_index=local_child_index,
                extension_variables=extension_variables,
                extension_bits=bits,
            )
            leaves.append(leaf)
            descendants.append(leaf)
        local_covers.append(_local_cover_record(
            width6_campaign["leaves"][width6_leaf_index], descendants
        ))

    expected_assignments = [
        list(bits) for bits in product((0, 1), repeat=SPLIT_WIDTH)
    ]
    observed_assignments = [leaf["assignment_bits"] for leaf in leaves]
    global_indices = [leaf["global_leaf_index"] for leaf in leaves]
    flattened_local_indices = [
        index
        for local_cover in local_covers
        for index in local_cover["global_leaf_indices"]
    ]
    global_exact = bool(
        len(leaves) == LEAF_COUNT
        and global_indices == list(range(LEAF_COUNT))
        and flattened_local_indices == list(range(LEAF_COUNT))
        and observed_assignments == expected_assignments
        and len(local_covers) == WIDTH6_LEAF_COUNT
        and all(
            cover["mutually_exclusive"] is True
            and cover["exhaustive"] is True
            for cover in local_covers
        )
        and width6_campaign.get("coverage", {}).get("mutually_exclusive")
        is True
        and width6_campaign.get("coverage", {}).get("exhaustive") is True
        and WITHIN_PREFIX_PAIR_COUNT + CROSS_PREFIX_PAIR_COUNT
        == GLOBAL_PAIR_COUNT
    )
    if not global_exact:
        raise NestedWidth10CampaignError(
            "hierarchical 1024-leaf cover composition failed"
        )
    test_only = width6_campaign.get("test_only")
    if type(test_only) is not bool or test_only is strict_base:
        raise NestedWidth10CampaignError("authority/strict_base mismatch")
    authority = (
        AUTHORITY_TEST_ONLY if test_only
        else AUTHORITY_PRODUCTION_CANDIDATE
    )
    total_dimacs_bytes = sum(leaf["child_dimacs_bytes"] for leaf in leaves)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "formulation": FORMULATION,
        "authority": authority,
        "test_only": test_only,
        "production_eligible": False,
        "parent_cover": width6._parent_cover_binding(parent_manifest),
        "selected_parent": _selected_parent_binding(
            parent_manifest, width6_campaign
        ),
        "width6_campaign": _width6_campaign_binding(width6_campaign),
        "selection_preview": preview,
        "refinement": {
            "width6_variable_count": WIDTH6_SPLIT_WIDTH,
            "width6_variables_dimacs": width6_variables,
            "extension_variable_count": EXTENSION_WIDTH,
            "extension_variables_dimacs": extension_variables,
            "width10_variable_count": SPLIT_WIDTH,
            "width10_variables_dimacs": width10_variables,
            "physical_qubit_indices_zero_based": [
                variable - 1 for variable in width10_variables
            ],
            "selection_preview_sha256": preview["record_sha256"],
            "assignment_order": (
                "lexicographic ten bits; width6 prefix then four-bit suffix"
            ),
            "descendants_per_width6_leaf": LOCAL_CHILD_COUNT,
        },
        "leaves": leaves,
        "local_covers": local_covers,
        "global_coverage": {
            "method": "hierarchical-width6-times-local-width4-cover-v1",
            "parent_cube_index": TARGET_PARENT_CUBE_INDEX,
            "expected_width6_prefix_count": WIDTH6_LEAF_COUNT,
            "observed_width6_prefix_count": len(local_covers),
            "expected_leaf_count": LEAF_COUNT,
            "observed_leaf_count": len(leaves),
            "global_leaf_indices": global_indices,
            "assignments_sha256": canonical_sha256(observed_assignments),
            "leaf_sha256_sequence_sha256": canonical_sha256([
                leaf["leaf_sha256"] for leaf in leaves
            ]),
            "child_cnf_sha256_sequence_sha256": canonical_sha256([
                leaf["child_cnf_sha256"] for leaf in leaves
            ]),
            "local_cover_sha256_sequence_sha256": canonical_sha256([
                cover["local_cover_sha256"] for cover in local_covers
            ]),
            "expected_global_pair_count": GLOBAL_PAIR_COUNT,
            "within_width6_prefix_pair_count": WITHIN_PREFIX_PAIR_COUNT,
            "cross_width6_prefix_pair_count": CROSS_PREFIX_PAIR_COUNT,
            "hierarchically_accounted_pair_count": (
                WITHIN_PREFIX_PAIR_COUNT + CROSS_PREFIX_PAIR_COUNT
            ),
            "global_pair_records_materialized": False,
            "all_local_pair_records_hashed": True,
            "mutually_exclusive": True,
            "exhaustive": True,
            "parent_formula_equivalence_certified": True,
            "proof": (
                "different width6 prefixes are separated by the authenticated "
                "width6 cover; equal prefixes have all 16 common four-bit "
                "suffix assignments exactly once"
            ),
            "solver_invoked": False,
        },
        "resource_profile": {
            "leaf_count": LEAF_COUNT,
            "local_cover_count": WIDTH6_LEAF_COUNT,
            "child_dimacs_payloads_retained_in_manifest": False,
            "child_dimacs_generated_sequentially": True,
            "total_child_dimacs_bytes": total_dimacs_bytes,
            "maximum_child_dimacs_bytes": max(
                leaf["child_dimacs_bytes"] for leaf in leaves
            ),
            "global_pair_record_count_avoided": GLOBAL_PAIR_COUNT,
            "local_pair_records_hashed_then_discarded": (
                WITHIN_PREFIX_PAIR_COUNT
            ),
            "solver_invoked": False,
        },
        "claim_preservation": {
            "quantum_code_changed": False,
            "base_cnf_changed": False,
            "only_physical_operator_unit_clauses_added": True,
            "all_1024_authenticated_unsat_leaves_imply_parent000_unsat": True,
            "one_verified_sat_leaf_implies_parent000_sat": True,
            "this_manifest_alone_proves_parent000_unsat": False,
            "this_manifest_alone_proves_distance_lower_bound": False,
            "inherited_distance_lower_bound_target": parent_manifest.get(
                "aggregation_policy", {}
            ).get("all_unsat_distance_lower_bound"),
        },
        "source_binding": _source_binding(),
        "solver_invoked": False,
    })


def verify_campaign_manifest(
    manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    parent_cube_index: int = TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Freshly rebuild and type-exact compare one nested campaign."""

    raw = dict(manifest) if type(manifest) is dict else {}
    failures: list[str] = []
    if set(raw) != MANIFEST_FIELDS:
        failures.append("manifest field set mismatch")
    if not selfhash_valid(raw):
        failures.append("manifest self-hash mismatch")
    if type(strict_base) is not bool:
        failures.append("strict_base is not a strict boolean")
    if type(parent_cube_index) is not int or parent_cube_index != 0:
        failures.append("caller parent is not exactly parent000")
    if raw.get("manifest_kind") != MANIFEST_KIND:
        failures.append("manifest kind mismatch")
    if raw.get("formulation") != FORMULATION:
        failures.append("formulation mismatch")
    if raw.get("test_only") is not (not strict_base):
        failures.append("test_only/strict_base mismatch")
    if raw.get("production_eligible") is not False:
        failures.append("cover manifest cannot claim a completed proof")
    width6_binding = (
        raw.get("width6_campaign")
        if type(raw.get("width6_campaign")) is dict else {}
    )
    if width6_binding.get("manifest_sha256") != width6_campaign.get(
        "manifest_sha256"
    ):
        failures.append("width-six campaign binding mismatch")
    refinement = (
        raw.get("refinement") if type(raw.get("refinement")) is dict else {}
    )
    extension = refinement.get("extension_variables_dimacs")
    if (
        type(extension) is not list
        or len(extension) != EXTENSION_WIDTH
        or any(type(variable) is not int for variable in extension)
    ):
        failures.append("extension variable field mismatch")
    leaves = raw.get("leaves")
    leaf_indices = [
        leaf.get("global_leaf_index") if type(leaf) is dict else None
        for leaf in leaves
    ] if type(leaves) is list else []
    if leaf_indices != list(range(LEAF_COUNT)):
        failures.append("global leaves are missing, duplicated, or reordered")
    local_covers = raw.get("local_covers")
    local_indices = [
        cover.get("width6_leaf_index") if type(cover) is dict else None
        for cover in local_covers
    ] if type(local_covers) is list else []
    if local_indices != list(range(WIDTH6_LEAF_COUNT)):
        failures.append("local covers are missing, duplicated, or reordered")
    flattened: list[Any] = []
    if type(local_covers) is list:
        for cover in local_covers:
            indices = cover.get("global_leaf_indices") if type(cover) is dict else None
            if type(indices) is list:
                flattened.extend(indices)
            else:
                flattened.append(None)
    if flattened != list(range(LEAF_COUNT)):
        failures.append("local covers do not partition all global leaves")
    global_coverage = (
        raw.get("global_coverage")
        if type(raw.get("global_coverage")) is dict else {}
    )
    if (
        global_coverage.get("mutually_exclusive") is not True
        or global_coverage.get("exhaustive") is not True
        or global_coverage.get("expected_global_pair_count")
        != GLOBAL_PAIR_COUNT
        or global_coverage.get("hierarchically_accounted_pair_count")
        != GLOBAL_PAIR_COUNT
    ):
        failures.append("global hierarchical coverage claim mismatch")

    expected: dict[str, Any] | None = None
    if type(extension) is list:
        try:
            expected = build_campaign_manifest(
                width6_campaign,
                parent_manifest,
                instance,
                confirmed_extension_variables=extension,
                parent_cube_index=parent_cube_index,
                strict_base=strict_base,
            )
        except (
            NestedWidth10CampaignError,
            width6.WidenedParentCampaignError,
            hierarchy.HierarchicalCubeError,
            cube16.Cube16Error,
            IndexError,
            KeyError,
            TypeError,
            ValueError,
        ) as exc:
            failures.append(f"fresh nested campaign replay failed: {exc}")
    if expected is not None and not json_type_equal(raw, expected):
        failures.append("manifest is not exact current-source canonical replay")
    coverage = (
        raw.get("global_coverage")
        if type(raw.get("global_coverage")) is dict else {}
    )
    valid = not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": VERIFICATION_KIND,
        "campaign_manifest_sha256": raw.get("manifest_sha256"),
        "expected_manifest_sha256": (
            expected.get("manifest_sha256") if expected is not None else None
        ),
        "parent_cube_index": parent_cube_index,
        "valid": valid,
        "binding_failures": failures,
        "width6_prefix_count": (
            len(local_covers) if type(local_covers) is list else None
        ),
        "leaf_count": len(leaves) if type(leaves) is list else None,
        "mutually_exclusive": bool(
            valid and coverage.get("mutually_exclusive") is True
        ),
        "exhaustive": bool(valid and coverage.get("exhaustive") is True),
        "parent000_formula_equivalence_certified": bool(
            valid
            and coverage.get("parent_formula_equivalence_certified") is True
        ),
        "solver_invoked": False,
        "launch_authorized_by_this_record": False,
        "publication_certificate": False,
    }, "record_sha256")



def _canonical_valid_verification_record(
    manifest_sha256: str,
) -> dict[str, Any]:
    if not _is_sha256(manifest_sha256):
        raise NestedWidth10CampaignError(
            "campaign manifest SHA-256 is not canonical"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": VERIFICATION_KIND,
        "campaign_manifest_sha256": manifest_sha256,
        "expected_manifest_sha256": manifest_sha256,
        "parent_cube_index": TARGET_PARENT_CUBE_INDEX,
        "valid": True,
        "binding_failures": [],
        "width6_prefix_count": WIDTH6_LEAF_COUNT,
        "leaf_count": LEAF_COUNT,
        "mutually_exclusive": True,
        "exhaustive": True,
        "parent000_formula_equivalence_certified": True,
        "solver_invoked": False,
        "launch_authorized_by_this_record": False,
        "publication_certificate": False,
    }, "record_sha256")


def _validate_fast_boundary(
    manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    *,
    verification_record: Mapping[str, Any],
    parent_cube_index: int,
    strict_base: bool,
) -> None:
    _require_target_parent(parent_cube_index)
    if type(strict_base) is not bool:
        raise NestedWidth10CampaignError("strict_base must be a strict boolean")
    if (
        type(manifest) is not dict
        or set(manifest) != MANIFEST_FIELDS
        or not selfhash_valid(manifest)
    ):
        raise NestedWidth10CampaignError(
            "fast boundary requires an intact canonical campaign manifest"
        )
    manifest_sha256 = manifest.get("manifest_sha256")
    expected_record = _canonical_valid_verification_record(
        manifest_sha256
    )
    if (
        type(verification_record) is not dict
        or set(verification_record) != VERIFICATION_FIELDS
        or not selfhash_valid(verification_record, "record_sha256")
        or not json_type_equal(verification_record, expected_record)
    ):
        raise NestedWidth10CampaignError(
            "fast boundary requires the exact successful verification record"
        )
    if (
        type(width6_campaign) is not dict
        or not selfhash_valid(width6_campaign)
        or type(parent_manifest) is not dict
        or not selfhash_valid(parent_manifest)
    ):
        raise NestedWidth10CampaignError(
            "fast boundary source manifests are not intact"
        )
    test_only = manifest.get("test_only")
    expected_authority = (
        AUTHORITY_TEST_ONLY if not strict_base
        else AUTHORITY_PRODUCTION_CANDIDATE
    )
    if (
        manifest.get("schema_version") != SCHEMA_VERSION
        or type(manifest.get("schema_version")) is not int
        or manifest.get("manifest_kind") != MANIFEST_KIND
        or manifest.get("formulation") != FORMULATION
        or manifest.get("authority") != expected_authority
        or test_only is not (not strict_base)
        or manifest.get("production_eligible") is not False
        or manifest.get("solver_invoked") is not False
    ):
        raise NestedWidth10CampaignError(
            "fast boundary campaign authority or schema mismatch"
        )
    try:
        if not json_type_equal(
            manifest.get("source_binding"), _source_binding()
        ):
            raise NestedWidth10CampaignError(
                "fast boundary current-source binding mismatch"
            )
        if not json_type_equal(
            manifest.get("parent_cover"),
            width6._parent_cover_binding(parent_manifest),
        ):
            raise NestedWidth10CampaignError(
                "fast boundary parent-cover binding mismatch"
            )
        if not json_type_equal(
            manifest.get("selected_parent"),
            _selected_parent_binding(parent_manifest, width6_campaign),
        ):
            raise NestedWidth10CampaignError(
                "fast boundary selected-parent binding mismatch"
            )
        if not json_type_equal(
            manifest.get("width6_campaign"),
            _width6_campaign_binding(width6_campaign),
        ):
            raise NestedWidth10CampaignError(
                "fast boundary width-six campaign binding mismatch"
            )
    except NestedWidth10CampaignError:
        raise
    except (
        width6.WidenedParentCampaignError,
        hierarchy.HierarchicalCubeError,
        cube16.Cube16Error,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
    ) as exc:
        raise NestedWidth10CampaignError(
            f"fast boundary binding reconstruction failed: {exc}"
        ) from exc

    preview = manifest.get("selection_preview")
    refinement = manifest.get("refinement")
    leaves = manifest.get("leaves")
    local_covers = manifest.get("local_covers")
    coverage = manifest.get("global_coverage")
    if (
        type(preview) is not dict
        or not selfhash_valid(preview, "record_sha256")
        or type(refinement) is not dict
        or type(leaves) is not list
        or len(leaves) != LEAF_COUNT
        or type(local_covers) is not list
        or len(local_covers) != WIDTH6_LEAF_COUNT
        or type(coverage) is not dict
    ):
        raise NestedWidth10CampaignError(
            "fast boundary campaign payload shape mismatch"
        )
    width6_variables = preview.get("width6_variables_dimacs")
    extension_variables = preview.get(
        "proposed_extension_variables_dimacs"
    )
    width10_variables = preview.get(
        "proposed_width10_variables_dimacs"
    )
    if (
        type(width6_variables) is not list
        or type(extension_variables) is not list
        or type(width10_variables) is not list
        or len(width6_variables) != WIDTH6_SPLIT_WIDTH
        or len(extension_variables) != EXTENSION_WIDTH
        or len(width10_variables) != SPLIT_WIDTH
        or width10_variables != width6_variables + extension_variables
        or len(set(width10_variables)) != SPLIT_WIDTH
        or refinement.get("width6_variables_dimacs") != width6_variables
        or refinement.get("extension_variables_dimacs")
        != extension_variables
        or refinement.get("width10_variables_dimacs") != width10_variables
        or refinement.get("selection_preview_sha256")
        != preview.get("record_sha256")
        or preview.get("width6_prefix_exact") is not True
    ):
        raise NestedWidth10CampaignError(
            "fast boundary width-ten selection binding mismatch"
        )
    if (
        strict_base
        and (
            width10_variables
            != list(EXPECTED_PARENT000_WIDTH10_VARIABLES)
            or preview.get("production_ranking_required") is not True
            or preview.get("production_ranking_matches") is not True
        )
    ):
        raise NestedWidth10CampaignError(
            "fast boundary production ranking mismatch"
        )
    if (
        [leaf.get("global_leaf_index") if type(leaf) is dict else None
         for leaf in leaves] != list(range(LEAF_COUNT))
        or [
            cover.get("width6_leaf_index")
            if type(cover) is dict else None
            for cover in local_covers
        ] != list(range(WIDTH6_LEAF_COUNT))
        or coverage.get("global_leaf_indices") != list(range(LEAF_COUNT))
        or coverage.get("expected_width6_prefix_count")
        != WIDTH6_LEAF_COUNT
        or coverage.get("observed_width6_prefix_count")
        != WIDTH6_LEAF_COUNT
        or coverage.get("expected_leaf_count") != LEAF_COUNT
        or coverage.get("observed_leaf_count") != LEAF_COUNT
        or coverage.get("expected_global_pair_count") != GLOBAL_PAIR_COUNT
        or coverage.get("within_width6_prefix_pair_count")
        != WITHIN_PREFIX_PAIR_COUNT
        or coverage.get("cross_width6_prefix_pair_count")
        != CROSS_PREFIX_PAIR_COUNT
        or coverage.get("hierarchically_accounted_pair_count")
        != GLOBAL_PAIR_COUNT
        or coverage.get("mutually_exclusive") is not True
        or coverage.get("exhaustive") is not True
        or coverage.get("parent_formula_equivalence_certified") is not True
        or coverage.get("solver_invoked") is not False
    ):
        raise NestedWidth10CampaignError(
            "fast boundary hierarchical coverage binding mismatch"
        )


def verified_child_dimacs_from_verification(
    manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    verification_record: Mapping[str, Any],
    global_leaf_index: int,
    parent_cube_index: int = TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> bytes:
    """Rebuild one child using a same-process full-verification result.

    verification_record MUST be the immediate return value of a same-process
    verify_campaign_manifest call for these exact objects.  Its self-hash is
    an integrity binding, not a signature or launch authorization.  A
    deserialized, copied, resealed, or synthesized record is outside this
    contract.  This API does not replace the required full replay and its
    result is not production authorization.
    """

    if (
        type(global_leaf_index) is not int
        or not 0 <= global_leaf_index < LEAF_COUNT
    ):
        raise NestedWidth10CampaignError(
            "global_leaf_index must be in 0..1023"
        )
    _validate_fast_boundary(
        manifest,
        width6_campaign,
        parent_manifest,
        verification_record=verification_record,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    try:
        leaves = manifest["leaves"]
        width6_leaf_index, local_child_index = divmod(
            global_leaf_index, LOCAL_CHILD_COUNT
        )
        expected_leaf, payload = _nested_leaf_record(
            instance=instance,
            base_clauses=[
                [int(literal) for literal in clause]
                for clause in instance.cnf["clauses"]
            ],
            width6_campaign=width6_campaign,
            width6_leaf_index=width6_leaf_index,
            local_child_index=local_child_index,
            extension_variables=manifest["refinement"][
                "extension_variables_dimacs"
            ],
            extension_bits=_bits(local_child_index, EXTENSION_WIDTH),
        )
        observed_leaf = leaves[global_leaf_index]
        if not json_type_equal(observed_leaf, expected_leaf):
            raise NestedWidth10CampaignError(
                "target leaf is not its exact canonical reconstruction"
            )
        descendant_start = width6_leaf_index * LOCAL_CHILD_COUNT
        descendants = leaves[
            descendant_start:descendant_start + LOCAL_CHILD_COUNT
        ]
        expected_local_cover = _local_cover_record(
            width6_campaign["leaves"][width6_leaf_index], descendants
        )
        if not json_type_equal(
            manifest["local_covers"][width6_leaf_index],
            expected_local_cover,
        ):
            raise NestedWidth10CampaignError(
                "target leaf local cover binding mismatch"
            )
        return payload
    except NestedWidth10CampaignError:
        raise
    except (
        width6.WidenedParentCampaignError,
        hierarchy.HierarchicalCubeError,
        cube16.Cube16Error,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
    ) as exc:
        raise NestedWidth10CampaignError(
            f"target leaf reconstruction failed: {exc}"
        ) from exc


def verified_child_dimacs(
    manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    global_leaf_index: int,
    parent_cube_index: int = TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> bytes:
    """Return one exact child DIMACS only after full fresh campaign replay."""

    if type(global_leaf_index) is not int or not 0 <= global_leaf_index < LEAF_COUNT:
        raise NestedWidth10CampaignError("global_leaf_index must be in 0..1023")
    replay = verify_campaign_manifest(
        manifest,
        width6_campaign,
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if replay.get("valid") is not True:
        raise NestedWidth10CampaignError(
            f"nested campaign failed exact replay: {replay.get('binding_failures')}"
        )
    return verified_child_dimacs_from_verification(
        manifest,
        width6_campaign,
        parent_manifest,
        instance,
        verification_record=replay,
        global_leaf_index=global_leaf_index,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )


__all__ = [
    "AUTHORITY_PRODUCTION_CANDIDATE",
    "AUTHORITY_TEST_ONLY",
    "CROSS_PREFIX_PAIR_COUNT",
    "EXPECTED_PARENT000_EXTENSION_VARIABLES",
    "EXPECTED_PARENT000_WIDTH10_VARIABLES",
    "EXPECTED_PARENT000_WIDTH6_VARIABLES",
    "EXTENSION_WIDTH",
    "FORMULATION",
    "GLOBAL_PAIR_COUNT",
    "LEAF_COUNT",
    "LOCAL_CHILD_COUNT",
    "LOCAL_PAIR_COUNT",
    "MANIFEST_FIELDS",
    "VERIFICATION_FIELDS",
    "MANIFEST_KIND",
    "NestedWidth10CampaignError",
    "SCHEMA_VERSION",
    "SPLIT_WIDTH",
    "TARGET_PARENT_CUBE_INDEX",
    "WIDTH6_LEAF_COUNT",
    "WIDTH6_SPLIT_WIDTH",
    "WITHIN_PREFIX_PAIR_COUNT",
    "build_campaign_manifest",
    "canonical_bytes",
    "canonical_sha256",
    "json_type_equal",
    "preview_extension_variables",
    "seal",
    "selfhash_valid",
    "verified_child_dimacs",
    "verified_child_dimacs_from_verification",
    "verify_campaign_manifest",
]
