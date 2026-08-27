#!/usr/bin/env python3
"""Strict proof-envelope validation for one nested parent000 width-ten leaf.

This module reuses the frozen v4 DRAT/LRAT and stopped-transport validators,
but gives width-ten output its own schema, gate, provenance tuple, and exact
campaign/leaf identity.  It aggregates nothing and grants no global claim.
"""

from __future__ import annotations

import os
from typing import Any, Mapping

from investigations import paper400_dic5_hierarchical_proof_aggregate_v4 as v4
from investigations import paper400_dic5_nested_width10_campaign_v1 as nested


SCHEMA_VERSION = 1
RUNNER_GATE = "paper400-dic5-nested-width10-child-resume-proof-v1"
CHILD_CERTIFICATE_KIND = "paper400-dic5-nested-width10-child-unsat-v1"
CHILD_VALIDATION_KIND = "paper400-dic5-nested-width10-child-validation-v1"
STATE_PROOF_UNSAT = v4.STATE_PROOF_UNSAT
AUTHORITY_PRODUCTION = v4.AUTHORITY_PRODUCTION
AUTHORITY_TEST_ONLY = v4.AUTHORITY_TEST_ONLY
TRANSPORT_STATE_CHECKPOINTED = v4.TRANSPORT_STATE_CHECKPOINTED
TRANSPORT_STATE_INACTIVE = v4.TRANSPORT_STATE_INACTIVE
TRANSPORT_STATES = v4.TRANSPORT_STATES

TRANSPORT_PROFILE_NATIVE = "NATIVE_NESTED_WIDTH10_V1"
TRANSPORT_PROVENANCE_FIELDS = v4.TRANSPORT_PROVENANCE_FIELDS

IDENTITY_FIELDS = (
    "width10_campaign_sha256",
    "width6_campaign_sha256",
    "parent_manifest_sha256",
    "parent_cube_index",
    "parent_cube_id",
    "parent_cube_sha256",
    "parent_cube_cnf_sha256",
    "parent_cube_dimacs_sha256",
    "global_leaf_index",
    "global_leaf_id",
    "leaf_sha256",
    "width6_leaf_index",
    "width6_leaf_sha256",
    "local_child_index",
    "child_index",
    "child_id",
    "child_sha256",
    "child_cnf_sha256",
    "child_dimacs_sha256",
    "combined_unit_clauses",
    "combined_unit_clauses_sha256",
)

CERTIFICATE_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", *IDENTITY_FIELDS, "child_num_variables",
    "child_num_clauses", "child_dimacs_bytes", "solver", "decision",
    "proof_chain", "resume_static_sha256", "transport_chain_sha256",
    "transport_quiescence", "transport_provenance",
    "source_binding_sha256", "toolchain_binding_sha256",
    "predecessor_chain_sha256", "parent_cube_unsat_claim",
    "global_distance_claim", "publication_certificate", "upload_authorized",
    "certificate_sha256",
})

VALIDATION_FIELDS = frozenset({
    "schema_version", "kind", "gate", "root", *IDENTITY_FIELDS, "state",
    "authority", "test_only", "valid", "strict_proof_unsat",
    "fresh_proof_replay", "source_toolchain_fresh", "certificate",
    "transport_provenance", "failures", "global_distance_claim",
    "publication_certificate", "upload_authorized", "validation_sha256",
})

DECISION_FIELDS = v4.DECISION_FIELDS
_EXPECTED_UNSAT_DECISION_COMMON = {
    "outcome": "unsat",
    "decision_basis": (
        "complete-drat+lrat+fresh-replay-from-exact-width10-child-cnf-v1"
    ),
    "proof_replay_decision_complete": True,
    "strict_proof_unsat": True,
    "solver_terminal_status_observed": False,
    "solver_exit_code_observed": None,
    "solver_clean_exit_observed": False,
    "proof_source_quiescent": True,
}

canonical_sha256 = v4.canonical_sha256
seal = v4.seal


def expected_unsat_decision(transport_state: str) -> dict[str, Any]:
    if transport_state not in TRANSPORT_STATES:
        raise ValueError("unsupported proof source state")
    return {
        **_EXPECTED_UNSAT_DECISION_COMMON,
        "proof_source_state": transport_state,
    }


def native_transport_provenance() -> dict[str, Any]:
    return {
        "profile": TRANSPORT_PROFILE_NATIVE,
        "source_schema_version": SCHEMA_VERSION,
        "source_runner_gate": RUNNER_GATE,
        "source_runner_sha256": None,
        "source_certificate_sha256": None,
        "adoption_record_sha256": None,
    }


def _same(left: Any, right: Any) -> bool:
    return v4.v1._same(left, right)


def _expected_authority(campaign: Mapping[str, Any]) -> str | None:
    test_only = campaign.get("test_only") if type(campaign) is dict else None
    if type(test_only) is not bool:
        return None
    return AUTHORITY_TEST_ONLY if test_only else AUTHORITY_PRODUCTION


def expected_identity(
    campaign: Mapping[str, Any], global_leaf_index: Any,
) -> dict[str, Any]:
    leaves = campaign.get("leaves") if type(campaign) is dict else None
    if (
        type(global_leaf_index) is not int
        or type(leaves) is not list
        or len(leaves) != nested.LEAF_COUNT
        or not 0 <= global_leaf_index < nested.LEAF_COUNT
        or type(leaves[global_leaf_index]) is not dict
    ):
        raise ValueError("global leaf index is not bound to the campaign")
    leaf = leaves[global_leaf_index]
    parent = campaign.get("selected_parent")
    width6 = campaign.get("width6_campaign")
    if (
        leaf.get("global_leaf_index") != global_leaf_index
        or type(parent) is not dict
        or type(width6) is not dict
    ):
        raise ValueError("campaign leaf/parent binding is malformed")
    return {
        "width10_campaign_sha256": campaign.get("manifest_sha256"),
        "width6_campaign_sha256": width6.get("manifest_sha256"),
        "parent_manifest_sha256": parent.get("parent_manifest_sha256"),
        "parent_cube_index": parent.get("parent_cube_index"),
        "parent_cube_id": parent.get("parent_cube_id"),
        "parent_cube_sha256": parent.get("parent_cube_sha256"),
        "parent_cube_cnf_sha256": parent.get("parent_cube_cnf_sha256"),
        "parent_cube_dimacs_sha256": parent.get("parent_cube_dimacs_sha256"),
        "global_leaf_index": leaf.get("global_leaf_index"),
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "width6_leaf_index": leaf.get("width6_leaf_index"),
        "width6_leaf_sha256": leaf.get("width6_leaf_sha256"),
        "local_child_index": leaf.get("local_child_index"),
        "child_index": leaf.get("global_leaf_index"),
        "child_id": leaf.get("global_leaf_id"),
        "child_sha256": leaf.get("leaf_sha256"),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "combined_unit_clauses": leaf.get("combined_unit_clauses"),
        "combined_unit_clauses_sha256": leaf.get(
            "combined_unit_clauses_sha256"
        ),
    }


def _identity_failures(
    value: Mapping[str, Any], campaign: Mapping[str, Any],
) -> list[str]:
    try:
        expected = expected_identity(campaign, value.get("global_leaf_index"))
    except (IndexError, KeyError, TypeError, ValueError) as exc:
        return [f"campaign identity unavailable: {exc}"]
    return [
        f"{key} binding mismatch"
        for key, wanted in expected.items()
        if not _same(value.get(key), wanted)
    ]


def _decision_failures(value: Any) -> list[str]:
    if type(value) is not dict or set(value) != DECISION_FIELDS:
        return ["UNSAT decision field set mismatch"]
    state = value.get("proof_source_state")
    if state not in TRANSPORT_STATES or not _same(
        value, expected_unsat_decision(state),
    ):
        return ["UNSAT proof-replay decision semantics mismatch"]
    return []


def _transport_provenance_failures(value: Any) -> list[str]:
    raw = dict(value) if type(value) is dict else {}
    if set(raw) != TRANSPORT_PROVENANCE_FIELDS:
        return ["transport provenance field set mismatch"]
    if not _same(raw, native_transport_provenance()):
        return ["native width-ten transport provenance mismatch"]
    return []


def validate_child_certificate(
    certificate: Any, campaign: Mapping[str, Any],
) -> list[str]:
    raw = dict(certificate) if type(certificate) is dict else {}
    failures: list[str] = []
    if set(raw) != CERTIFICATE_FIELDS:
        failures.append("certificate field set mismatch")
    if not v4.v1._selfhash_valid(raw, "certificate_sha256"):
        failures.append("certificate self-hash mismatch")
    if raw.get("schema_version") != SCHEMA_VERSION:
        failures.append("certificate schema version mismatch")
    if raw.get("kind") != CHILD_CERTIFICATE_KIND or raw.get("gate") != RUNNER_GATE:
        failures.append("certificate kind/gate mismatch")
    if raw.get("state") != STATE_PROOF_UNSAT:
        failures.append("certificate is not proof-carrying child UNSAT")
    failures.extend(_identity_failures(raw, campaign))

    leaves = campaign.get("leaves") if type(campaign) is dict else None
    index = raw.get("global_leaf_index")
    leaf = (
        leaves[index]
        if type(leaves) is list and type(index) is int and 0 <= index < len(leaves)
        and type(leaves[index]) is dict else None
    )
    if leaf is not None:
        for key in ("child_num_variables", "child_num_clauses", "child_dimacs_bytes"):
            if not _same(raw.get(key), leaf.get(key)):
                failures.append(f"{key} binding mismatch")

    authority = _expected_authority(campaign)
    if authority is None or raw.get("authority") != authority:
        failures.append("certificate authority mismatch")
    expected_test_only = authority != AUTHORITY_PRODUCTION
    if type(raw.get("test_only")) is not bool or raw.get("test_only") is not expected_test_only:
        failures.append("certificate authority/test_only mismatch")
    provenance_failures = _transport_provenance_failures(
        raw.get("transport_provenance")
    )
    failures.extend(provenance_failures)
    if raw.get("production_eligible") is not bool(
        authority == AUTHORITY_PRODUCTION and not provenance_failures
    ):
        failures.append("certificate production eligibility mismatch")

    expected_solver = {
        "name": v4.v1.root_aggregate.EXPECTED_SOLVER_NAME,
        "version": v4.v1.root_aggregate.EXPECTED_SOLVER_VERSION,
        "executable_sha256": v4.v1.root_aggregate.EXPECTED_SOLVER_SHA256,
    }
    if type(raw.get("solver")) is not dict or not _same(raw.get("solver"), expected_solver):
        failures.append("solver binding mismatch")
    failures.extend(_decision_failures(raw.get("decision")))
    failures.extend(v4.v1._proof_chain_failures(raw.get("proof_chain")))
    failures.extend(v4._quiescence_failures(
        raw.get("transport_quiescence"), raw.get("proof_chain")
    ))
    decision = raw.get("decision")
    quiescence = raw.get("transport_quiescence")
    if (
        type(decision) is dict and type(quiescence) is dict
        and decision.get("proof_source_state") != quiescence.get("transport_state")
    ):
        failures.append("decision/quiescence state mismatch")
    for key in (
        "resume_static_sha256", "transport_chain_sha256",
        "source_binding_sha256", "toolchain_binding_sha256",
        "predecessor_chain_sha256",
    ):
        if not v4.v1.root_aggregate.is_sha256(raw.get(key)):
            failures.append(f"{key} invalid")
    if raw.get("parent_cube_unsat_claim") is not False:
        failures.append("one child cannot claim parent000 UNSAT")
    if raw.get("global_distance_claim") is not None:
        failures.append("one child cannot make a global claim")
    if raw.get("publication_certificate") is not False:
        failures.append("child certificate cannot publish")
    if raw.get("upload_authorized") is not False:
        failures.append("child certificate cannot authorize upload")
    return list(dict.fromkeys(failures))


def validate_child_run_record(
    record: Any, campaign: Mapping[str, Any],
) -> list[str]:
    raw = dict(record) if type(record) is dict else {}
    failures: list[str] = []
    if set(raw) != VALIDATION_FIELDS:
        failures.append("validation field set mismatch")
    if not v4.v1._selfhash_valid(raw, "validation_sha256"):
        failures.append("validation self-hash mismatch")
    if raw.get("schema_version") != SCHEMA_VERSION:
        failures.append("validation schema version mismatch")
    if raw.get("kind") != CHILD_VALIDATION_KIND or raw.get("gate") != RUNNER_GATE:
        failures.append("validation kind/gate mismatch")
    if type(raw.get("root")) is not str or not os.path.isabs(raw.get("root", "")):
        failures.append("validation root is not absolute")
    failures.extend(_identity_failures(raw, campaign))

    authority = _expected_authority(campaign)
    if authority is None or raw.get("authority") != authority:
        failures.append("validation authority mismatch")
    if type(raw.get("test_only")) is not bool or raw.get("test_only") is not (
        authority != AUTHORITY_PRODUCTION
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
        and raw.get("global_distance_claim") is None
        and raw.get("publication_certificate") is False
        and raw.get("upload_authorized") is False
    ):
        failures.append("proof-UNSAT validation truth table mismatch")
    certificate = raw.get("certificate")
    failures.extend(validate_child_certificate(certificate, campaign))
    failures.extend(_transport_provenance_failures(raw.get("transport_provenance")))
    if type(certificate) is dict:
        for key in (*IDENTITY_FIELDS, "authority", "test_only", "transport_provenance"):
            if not _same(certificate.get(key), raw.get(key)):
                failures.append(f"certificate/validation {key} mismatch")
    return list(dict.fromkeys(failures))


__all__ = [
    "AUTHORITY_PRODUCTION", "AUTHORITY_TEST_ONLY", "CERTIFICATE_FIELDS",
    "CHILD_CERTIFICATE_KIND", "CHILD_VALIDATION_KIND", "IDENTITY_FIELDS",
    "RUNNER_GATE", "SCHEMA_VERSION", "STATE_PROOF_UNSAT",
    "TRANSPORT_STATE_CHECKPOINTED", "TRANSPORT_STATE_INACTIVE",
    "TRANSPORT_STATES", "VALIDATION_FIELDS", "canonical_sha256",
    "expected_identity", "expected_unsat_decision", "native_transport_provenance",
    "seal", "validate_child_certificate", "validate_child_run_record",
]
