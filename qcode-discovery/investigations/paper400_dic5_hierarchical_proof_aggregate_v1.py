#!/usr/bin/env python3
"""Strict proof-carrying aggregation for one refined paper400 parent cube.

The authenticated refinement manifest proves only that its children are an
exact, mutually exclusive cover of one parent cube.  This module accepts only
proof-carrying UNSAT validation envelopes for those children and derives only
``PARENT_CUBE_UNSAT``.  It deliberately cannot make a global distance claim:
the derived parent terminal still has to be composed with every other leaf of
the original root cover.

This module does not invoke a solver or a proof checker.  A leaf runner must
produce the validation envelopes after fresh DRAT and LRAT replay.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Any, Mapping, Sequence

from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_cube16_proof_aggregate_v1 as root_aggregate
from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy


SCHEMA_VERSION = 1
RUNNER_GATE = "paper400-dic5-hierarchical-child-proof-carrying-v1"
CHILD_CERTIFICATE_KIND = "paper400-dic5-proof-carrying-refined-child-unsat-v1"
CHILD_VALIDATION_KIND = "paper400-dic5-refined-child-proof-validation-v1"
AGGREGATE_KIND = "paper400-dic5-refined-parent-proof-aggregate-v1"

STATE_PROOF_UNSAT = "PROOF_CARRYING_CHILD_UNSAT"
STATE_PARENT_UNSAT = "PARENT_CUBE_UNSAT"
STATE_UNRESOLVED = "UNRESOLVED"

AUTHORITY_PRODUCTION = root_aggregate.AUTHORITY_PRODUCTION
AUTHORITY_TEST_ONLY = root_aggregate.AUTHORITY_TEST_ONLY


IDENTITY_FIELDS = (
    "refinement_manifest_sha256",
    "parent_manifest_sha256",
    "parent_cube_index",
    "parent_cube_id",
    "parent_cube_sha256",
    "parent_cube_cnf_sha256",
    "parent_cube_dimacs_sha256",
    "child_index",
    "child_id",
    "child_sha256",
    "child_cnf_sha256",
    "child_dimacs_sha256",
    "combined_unit_clauses",
    "combined_unit_clauses_sha256",
)

CERTIFICATE_FIELDS = frozenset({
    "schema_version",
    "kind",
    "gate",
    "state",
    "authority",
    "test_only",
    "production_eligible",
    *IDENTITY_FIELDS,
    "child_num_variables",
    "child_num_clauses",
    "child_dimacs_bytes",
    "solver",
    "decision",
    "proof_chain",
    "source_binding_sha256",
    "toolchain_binding_sha256",
    "predecessor_chain_sha256",
    "parent_cube_unsat_claim",
    "global_distance_claim",
    "publication_certificate",
    "upload_authorized",
    "certificate_sha256",
})

VALIDATION_FIELDS = frozenset({
    "schema_version",
    "kind",
    "gate",
    "root",
    *IDENTITY_FIELDS,
    "state",
    "authority",
    "test_only",
    "valid",
    "strict_proof_unsat",
    "fresh_proof_replay",
    "source_toolchain_fresh",
    "certificate",
    "failures",
    "validation_sha256",
})


def canonical_sha256(value: Any) -> str:
    return hierarchy.canonical_sha256(value)


def seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    return hierarchy.seal(value, field)


def _same(left: Any, right: Any) -> bool:
    return cube16.optimized.json_type_equal(left, right)


def _selfhash_valid(value: Any, field: str) -> bool:
    return root_aggregate.selfhash_valid(value, field)


def _expected_authority(manifest: Mapping[str, Any]) -> str | None:
    test_only = manifest.get("test_only") if type(manifest) is dict else None
    if type(test_only) is not bool:
        return None
    return AUTHORITY_TEST_ONLY if test_only else AUTHORITY_PRODUCTION


def _child_for_index(
    manifest: Mapping[str, Any], child_index: Any,
) -> Mapping[str, Any] | None:
    children = manifest.get("children") if type(manifest) is dict else None
    if (
        type(child_index) is int
        and type(children) is list
        and 0 <= child_index < len(children)
        and type(children[child_index]) is dict
        and children[child_index].get("child_index") == child_index
    ):
        return children[child_index]
    return None


def _expected_identity(
    manifest: Mapping[str, Any], child: Mapping[str, Any],
) -> dict[str, Any]:
    parent = manifest.get("parent", {})
    return {
        "refinement_manifest_sha256": manifest.get("manifest_sha256"),
        "parent_manifest_sha256": parent.get("manifest_sha256"),
        "parent_cube_index": parent.get("cube_index"),
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "parent_cube_cnf_sha256": parent.get("cube_cnf_sha256"),
        "parent_cube_dimacs_sha256": parent.get("cube_dimacs_sha256"),
        "child_index": child.get("child_index"),
        "child_id": child.get("child_id"),
        "child_sha256": child.get("child_sha256"),
        "child_cnf_sha256": child.get("child_cnf_sha256"),
        "child_dimacs_sha256": child.get("child_dimacs_sha256"),
        "combined_unit_clauses": child.get("combined_unit_clauses"),
        "combined_unit_clauses_sha256": child.get(
            "combined_unit_clauses_sha256"
        ),
    }


def _identity_failures(
    value: Mapping[str, Any], manifest: Mapping[str, Any],
) -> list[str]:
    child = _child_for_index(manifest, value.get("child_index"))
    if child is None:
        return ["child index is not bound to the refinement manifest"]
    failures: list[str] = []
    for key, wanted in _expected_identity(manifest, child).items():
        if not _same(value.get(key), wanted):
            failures.append(f"{key} binding mismatch")
    return failures


def _proof_chain_failures(value: Any) -> list[str]:
    fields = {
        "format",
        "binary_drat",
        "converted_lrat",
        "drat_checker_sha256",
        "lrat_checker_sha256",
        "trusted_policy_sha256",
        "drat_independently_verified",
        "lrat_independently_verified",
        "fresh_drat_replay",
        "fresh_lrat_replay",
        "drat_record_sha256",
        "lrat_record_sha256",
        "fresh_replay_record_sha256",
        "chain_sha256",
    }
    if type(value) is not dict or set(value) != fields:
        return ["proof chain field set mismatch"]
    failures: list[str] = []
    if not _selfhash_valid(value, "chain_sha256"):
        failures.append("proof chain self-hash mismatch")
    if value.get("format") != "binary-drat+converted-lrat-v1":
        failures.append("proof chain format mismatch")
    failures.extend(root_aggregate._artifact_reference_failures(
        value.get("binary_drat"), role="raw-binary-drat"
    ))
    failures.extend(root_aggregate._artifact_reference_failures(
        value.get("converted_lrat"), role="converted-lrat"
    ))
    for key, wanted in {
        "drat_checker_sha256": root_aggregate.EXPECTED_DRAT_CHECKER_SHA256,
        "lrat_checker_sha256": root_aggregate.EXPECTED_LRAT_CHECKER_SHA256,
        "trusted_policy_sha256": root_aggregate.EXPECTED_POLICY_SHA256,
    }.items():
        if value.get(key) != wanted:
            failures.append(f"{key} mismatch")
    for key in (
        "drat_independently_verified",
        "lrat_independently_verified",
        "fresh_drat_replay",
        "fresh_lrat_replay",
    ):
        if value.get(key) is not True:
            failures.append(f"{key} is not true")
    for key in (
        "drat_record_sha256",
        "lrat_record_sha256",
        "fresh_replay_record_sha256",
    ):
        if not root_aggregate.is_sha256(value.get(key)):
            failures.append(f"{key} invalid")
    return failures


def validate_child_certificate(
    certificate: Any,
    refinement_manifest: Mapping[str, Any],
) -> list[str]:
    """Validate one durable refined-child UNSAT certificate."""

    raw = dict(certificate) if type(certificate) is dict else {}
    failures: list[str] = []
    if set(raw) != CERTIFICATE_FIELDS:
        failures.append("certificate field set mismatch")
    if not _selfhash_valid(raw, "certificate_sha256"):
        failures.append("certificate self-hash mismatch")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
    ):
        failures.append("certificate schema version mismatch")
    if (
        raw.get("kind") != CHILD_CERTIFICATE_KIND
        or raw.get("gate") != RUNNER_GATE
    ):
        failures.append("certificate kind/gate mismatch")
    if raw.get("state") != STATE_PROOF_UNSAT:
        failures.append("certificate state is not proof-carrying child UNSAT")
    failures.extend(_identity_failures(raw, refinement_manifest))

    child = _child_for_index(refinement_manifest, raw.get("child_index"))
    if child is not None:
        for key, wanted in {
            "child_num_variables": child.get("child_num_variables"),
            "child_num_clauses": child.get("child_num_clauses"),
            "child_dimacs_bytes": child.get("child_dimacs_bytes"),
        }.items():
            if not _same(raw.get(key), wanted):
                failures.append(f"{key} binding mismatch")

    expected_authority = _expected_authority(refinement_manifest)
    if expected_authority is None or raw.get("authority") != expected_authority:
        failures.append("certificate authority does not match refinement")
    expected_test_only = expected_authority != AUTHORITY_PRODUCTION
    if type(raw.get("test_only")) is not bool or raw.get("test_only") is not expected_test_only:
        failures.append("certificate authority/test_only mismatch")
    if raw.get("production_eligible") is not (
        expected_authority == AUTHORITY_PRODUCTION
    ):
        failures.append("certificate production eligibility mismatch")

    solver = raw.get("solver")
    if type(solver) is not dict or set(solver) != {
        "name", "version", "executable_sha256",
    }:
        failures.append("solver binding field set mismatch")
    elif solver != {
        "name": root_aggregate.EXPECTED_SOLVER_NAME,
        "version": root_aggregate.EXPECTED_SOLVER_VERSION,
        "executable_sha256": root_aggregate.EXPECTED_SOLVER_SHA256,
    }:
        failures.append("solver binding mismatch")

    if not _same(raw.get("decision"), {
        "outcome": "unsat",
        "status_name": "UNSATISFIABLE",
        "decision_complete": True,
        "clean_exit": True,
        "timed_out": False,
    }):
        failures.append("UNSAT decision semantics mismatch")
    failures.extend(_proof_chain_failures(raw.get("proof_chain")))

    for key in (
        "source_binding_sha256",
        "toolchain_binding_sha256",
        "predecessor_chain_sha256",
    ):
        if not root_aggregate.is_sha256(raw.get(key)):
            failures.append(f"{key} invalid")
    if raw.get("parent_cube_unsat_claim") is not False:
        failures.append("a single child cannot claim parent cube UNSAT")
    if raw.get("global_distance_claim") is not None:
        failures.append("a child certificate cannot make a global distance claim")
    if raw.get("publication_certificate") is not False:
        failures.append("a child certificate is not a publication certificate")
    if raw.get("upload_authorized") is not False:
        failures.append("a child certificate cannot authorize upload")
    return list(dict.fromkeys(failures))


def validate_child_run_record(
    record: Any,
    refinement_manifest: Mapping[str, Any],
) -> list[str]:
    """Accept only a freshly replayed proof-carrying child envelope."""

    raw = dict(record) if type(record) is dict else {}
    failures: list[str] = []
    if set(raw) != VALIDATION_FIELDS:
        failures.append("validation field set mismatch")
    if not _selfhash_valid(raw, "validation_sha256"):
        failures.append("validation self-hash mismatch")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
    ):
        failures.append("validation schema version mismatch")
    if raw.get("kind") != CHILD_VALIDATION_KIND or raw.get("gate") != RUNNER_GATE:
        failures.append("validation kind/gate mismatch")
    if type(raw.get("root")) is not str or not os.path.isabs(raw.get("root", "")):
        failures.append("validation root is not absolute")
    failures.extend(_identity_failures(raw, refinement_manifest))

    expected_authority = _expected_authority(refinement_manifest)
    if expected_authority is None or raw.get("authority") != expected_authority:
        failures.append("validation authority does not match refinement")
    if (
        type(raw.get("test_only")) is not bool
        or raw.get("test_only") is not (expected_authority != AUTHORITY_PRODUCTION)
    ):
        failures.append("validation authority/test_only mismatch")
    if type(raw.get("failures")) is not list or any(
        type(item) is not str for item in raw.get("failures", [])
    ):
        failures.append("validation failures list invalid")

    if not (
        raw.get("state") == STATE_PROOF_UNSAT
        and raw.get("valid") is True
        and raw.get("strict_proof_unsat") is True
        and raw.get("fresh_proof_replay") is True
        and raw.get("source_toolchain_fresh") is True
        and raw.get("failures") == []
    ):
        failures.append("proof-UNSAT validation truth table mismatch")
    certificate = raw.get("certificate")
    failures.extend(validate_child_certificate(certificate, refinement_manifest))
    if type(certificate) is dict:
        for key in (*IDENTITY_FIELDS, "authority", "test_only"):
            if not _same(certificate.get(key), raw.get(key)):
                failures.append(f"certificate/validation {key} binding mismatch")
    return list(dict.fromkeys(failures))


def aggregate_child_validations(
    refinement_manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    validations: Sequence[Mapping[str, Any]],
    instance: cube16.optimized.OptimizedInstance,
    *,
    expected_parent_cube_index: int,
    expected_split_width: int,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Derive only parent-cube UNSAT from a complete authenticated child set."""

    manifest_replay = hierarchy.verify_refinement_manifest(
        refinement_manifest,
        parent_manifest,
        instance,
        strict_base=strict_base,
        expected_parent_cube_index=expected_parent_cube_index,
        expected_split_width=expected_split_width,
    )
    manifest_authenticated = bool(
        manifest_replay.get("valid") is True
        and manifest_replay.get("coverage_mutually_exclusive") is True
        and manifest_replay.get("coverage_exhaustive") is True
        and manifest_replay.get("quantum_code_changed") is False
        and refinement_manifest.get("claim_preservation", {}).get(
            "all_children_unsat_implies_parent_unsat"
        ) is True
        and refinement_manifest.get("claim_preservation", {}).get(
            "this_manifest_alone_proves_global_distance_lower_bound"
        ) is False
    )
    children = (
        refinement_manifest.get("children")
        if type(refinement_manifest) is dict
        else None
    )
    expected_child_count = len(children) if type(children) is list else 0

    records: list[dict[str, Any]] = []
    for position, candidate in enumerate(validations):
        failures = validate_child_run_record(candidate, refinement_manifest)
        records.append({
            "input_position": position,
            "child_index": candidate.get("child_index")
            if type(candidate) is dict else None,
            "state": candidate.get("state")
            if type(candidate) is dict else None,
            "valid": not failures,
            "binding_failures": failures,
            "validation_sha256": candidate.get("validation_sha256")
            if type(candidate) is dict else None,
        })

    indices = [record["child_index"] for record in records]
    exact_indices = bool(
        expected_child_count > 0
        and len(indices) == expected_child_count
        and all(type(index) is int for index in indices)
        and sorted(indices) == list(range(expected_child_count))
    )
    all_proof_unsat = bool(
        manifest_authenticated
        and exact_indices
        and all(record["valid"] for record in records)
        and all(
            candidate.get("state") == STATE_PROOF_UNSAT
            and candidate.get("strict_proof_unsat") is True
            and candidate.get("fresh_proof_replay") is True
            and candidate.get("source_toolchain_fresh") is True
            for candidate in validations
        )
    )

    ordered_bindings: list[dict[str, Any]] = []
    if all_proof_unsat:
        ordered = sorted(validations, key=lambda item: item["child_index"])
        ordered_bindings = [{
            "child_index": item["child_index"],
            "child_id": item["child_id"],
            "child_sha256": item["child_sha256"],
            "child_cnf_sha256": item["child_cnf_sha256"],
            "child_dimacs_sha256": item["child_dimacs_sha256"],
            "combined_unit_clauses_sha256": item[
                "combined_unit_clauses_sha256"
            ],
            "validation_sha256": item["validation_sha256"],
            "certificate_sha256": item["certificate"]["certificate_sha256"],
        } for item in ordered]

    parent = refinement_manifest.get("parent", {})
    authority = _expected_authority(refinement_manifest)
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "aggregate_kind": AGGREGATE_KIND,
        "status": STATE_PARENT_UNSAT if all_proof_unsat else STATE_UNRESOLVED,
        "refinement_manifest_sha256": refinement_manifest.get(
            "manifest_sha256"
        ),
        "manifest_replay_record_sha256": manifest_replay.get("record_sha256"),
        "manifest_authenticated": manifest_authenticated,
        "manifest_binding_failures": manifest_replay.get(
            "binding_failures", []
        ),
        "parent_manifest_sha256": parent.get("manifest_sha256"),
        "parent_cube_index": parent.get("cube_index"),
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "expected_child_count": expected_child_count,
        "all_child_indices_exactly_once": exact_indices,
        "all_children_proof_carrying_unsat": all_proof_unsat,
        "authority": authority,
        "test_only": authority != AUTHORITY_PRODUCTION,
        "production_eligible_parent_terminal": bool(
            all_proof_unsat and authority == AUTHORITY_PRODUCTION
        ),
        "child_records": records,
        "ordered_child_certificate_bindings": ordered_bindings,
        "parent_cube_unsat": all_proof_unsat,
        "claim_scope": "one-parent-cube-only",
        "global_distance_claim": None,
        "distance_lower_bound": None,
        "publication_certificate": False,
        "upload_authorized": False,
        "required_global_composition": (
            "compose this parent terminal with authenticated terminals for "
            "every other leaf of the original root cover"
        ),
        "blocker": None if all_proof_unsat else (
            "need an authenticated exact refinement and exactly one freshly "
            "replayed proof-carrying UNSAT envelope for every child"
        ),
    }, "aggregate_sha256")
    return result


__all__ = [
    "AGGREGATE_KIND",
    "AUTHORITY_PRODUCTION",
    "AUTHORITY_TEST_ONLY",
    "CERTIFICATE_FIELDS",
    "CHILD_CERTIFICATE_KIND",
    "CHILD_VALIDATION_KIND",
    "RUNNER_GATE",
    "SCHEMA_VERSION",
    "STATE_PARENT_UNSAT",
    "STATE_PROOF_UNSAT",
    "STATE_UNRESOLVED",
    "VALIDATION_FIELDS",
    "aggregate_child_validations",
    "canonical_sha256",
    "seal",
    "validate_child_certificate",
    "validate_child_run_record",
]
