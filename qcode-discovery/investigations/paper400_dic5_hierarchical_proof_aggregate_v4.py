#!/usr/bin/env python3
"""Honest proof-replay aggregation for one refined paper400 parent cube.

Version 4 separates a complete independently replayed UNSAT proof from solver
process telemetry and names the stopped proof source honestly. It accepts
exactly two quiescent proof-source states: a DMTCP checkpoint-stop, or a DMTCP
generation whose exact process identity is dead and whose proof has no
writable holder. Neither profile invents a solver exit code. The mathematical
decision still comes only from complete DRAT checking, LRAT conversion, and
fresh DRAT/LRAT replay from the exact child CNF. Native v4 output and an
explicit adoption of the frozen v3 runner are separated by an exact provenance
truth table; the latter binds its source certificate and target evidence in an
adoption-record digest.

The v1 identity and proof-chain checks are reused, but v1 envelopes are not
accepted. This schema derives only ``PARENT_CUBE_UNSAT``; global root-cover
composition remains a separate obligation.
"""

from __future__ import annotations

import os
from typing import Any, Mapping, Sequence

from investigations import paper400_dic5_hierarchical_proof_aggregate_v1 as v1


SCHEMA_VERSION = 4
RUNNER_GATE = "paper400-dic5-hierarchical-child-resume-proof-v4"
CHILD_CERTIFICATE_KIND = "paper400-dic5-proof-carrying-refined-child-unsat-v4"
CHILD_VALIDATION_KIND = (
    "paper400-dic5-refined-child-resume-proof-validation-v4"
)
AGGREGATE_KIND = "paper400-dic5-refined-parent-proof-aggregate-v4"

STATE_PROOF_UNSAT = v1.STATE_PROOF_UNSAT
STATE_PARENT_UNSAT = v1.STATE_PARENT_UNSAT
STATE_UNRESOLVED = v1.STATE_UNRESOLVED
AUTHORITY_PRODUCTION = v1.AUTHORITY_PRODUCTION
AUTHORITY_TEST_ONLY = v1.AUTHORITY_TEST_ONLY
IDENTITY_FIELDS = v1.IDENTITY_FIELDS
CERTIFICATE_FIELDS = v1.CERTIFICATE_FIELDS | frozenset({
    "resume_static_sha256",
    "transport_chain_sha256",
    "transport_quiescence",
    "transport_provenance",
})
VALIDATION_FIELDS = v1.VALIDATION_FIELDS | frozenset({
    "transport_provenance",
    "global_distance_claim",
    "publication_certificate",
    "upload_authorized",
})

TRANSPORT_PROFILE_NATIVE_V4 = "NATIVE_V4"
TRANSPORT_PROFILE_ADOPTED_FROZEN_V3 = "ADOPTED_FROZEN_V3_70881268"
TRANSPORT_PROFILES = frozenset({
    TRANSPORT_PROFILE_NATIVE_V4,
    TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
})
FROZEN_V3_SCHEMA_VERSION = 3
FROZEN_V3_RUNNER_GATE = (
    "paper400-dic5-hierarchical-child-resume-proof-v3"
)
FROZEN_V3_RUNNER_SHA256 = (
    "7088126800ff618629fb059ec002df09c9a127f57609326ff2857cf793eaf54a"
)
TRANSPORT_PROVENANCE_FIELDS = frozenset({
    "profile",
    "source_schema_version",
    "source_runner_gate",
    "source_runner_sha256",
    "source_certificate_sha256",
    "adoption_record_sha256",
})
ADOPTION_RECORD_SCHEMA_VERSION = 1
ADOPTION_RECORD_KIND = "paper400-dic5-frozen-v3-transport-adoption-v1"

DECISION_FIELDS = frozenset({
    "outcome",
    "decision_basis",
    "proof_replay_decision_complete",
    "strict_proof_unsat",
    "solver_terminal_status_observed",
    "solver_exit_code_observed",
    "solver_clean_exit_observed",
    "proof_source_state",
    "proof_source_quiescent",
})
TRANSPORT_STATE_CHECKPOINTED = "CHECKPOINTED"
TRANSPORT_STATE_INACTIVE = "INACTIVE_UNCHECKPOINTED"
TRANSPORT_STATES = frozenset({
    TRANSPORT_STATE_CHECKPOINTED,
    TRANSPORT_STATE_INACTIVE,
})
QUIESCENCE_FIELDS = frozenset({
    "method",
    "transport_state",
    "latest_generation",
    "latest_pid",
    "latest_proc_start_ticks",
    "latest_pid_identity_alive",
    "coordinator_observations",
    "writable_holders_before",
    "writable_holders_after",
    "proof_before",
    "proof_after",
})
COORDINATOR_OBSERVATION_FIELDS = frozenset({
    "attempted", "reachable", "peer_count", "running",
})
STOPPED_PROOF_FIELDS = frozenset({
    "role", "relative_path", "file_sha256", "bytes", "mode",
    "device", "inode", "uid", "links",
})
_EXPECTED_UNSAT_DECISION_COMMON = {
    "outcome": "unsat",
    "decision_basis": (
        "complete-drat+lrat+fresh-replay-from-exact-child-cnf-v4"
    ),
    "proof_replay_decision_complete": True,
    "strict_proof_unsat": True,
    "solver_terminal_status_observed": False,
    "solver_exit_code_observed": None,
    "solver_clean_exit_observed": False,
    "proof_source_quiescent": True,
}


def expected_unsat_decision(transport_state: str) -> dict[str, Any]:
    if transport_state not in TRANSPORT_STATES:
        raise ValueError("unsupported proof source state")
    return {
        **_EXPECTED_UNSAT_DECISION_COMMON,
        "proof_source_state": transport_state,
    }


EXPECTED_UNSAT_DECISIONS = {
    state: expected_unsat_decision(state) for state in sorted(TRANSPORT_STATES)
}

canonical_sha256 = v1.canonical_sha256
seal = v1.seal


def native_transport_provenance() -> dict[str, Any]:
    """Return the only provenance tuple accepted for native v4 output."""

    return {
        "profile": TRANSPORT_PROFILE_NATIVE_V4,
        "source_schema_version": SCHEMA_VERSION,
        "source_runner_gate": RUNNER_GATE,
        "source_runner_sha256": None,
        "source_certificate_sha256": None,
        "adoption_record_sha256": None,
    }


def _adoption_binding_payload(
    certificate: Mapping[str, Any], *, source_certificate_sha256: str,
) -> dict[str, Any]:
    proof_chain = certificate.get("proof_chain")
    target_payload = dict(certificate)
    target_payload.pop("certificate_sha256", None)
    target_payload.pop("transport_provenance", None)
    return {
        "schema_version": ADOPTION_RECORD_SCHEMA_VERSION,
        "kind": ADOPTION_RECORD_KIND,
        "profile": TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
        "source_schema_version": FROZEN_V3_SCHEMA_VERSION,
        "source_runner_gate": FROZEN_V3_RUNNER_GATE,
        "source_runner_sha256": FROZEN_V3_RUNNER_SHA256,
        "source_certificate_sha256": source_certificate_sha256,
        "target_schema_version": SCHEMA_VERSION,
        "target_runner_gate": RUNNER_GATE,
        "target_certificate_kind": CHILD_CERTIFICATE_KIND,
        "target_certificate_payload_sha256": canonical_sha256(target_payload),
        "target_child_identity": {
            key: certificate.get(key) for key in IDENTITY_FIELDS
        },
        "resume_static_sha256": certificate.get("resume_static_sha256"),
        "transport_chain_sha256": certificate.get(
            "transport_chain_sha256"
        ),
        "source_binding_sha256": certificate.get("source_binding_sha256"),
        "toolchain_binding_sha256": certificate.get(
            "toolchain_binding_sha256"
        ),
        "predecessor_chain_sha256": certificate.get(
            "predecessor_chain_sha256"
        ),
        "proof_chain_sha256": (
            proof_chain.get("chain_sha256")
            if type(proof_chain) is dict else None
        ),
        "decision": certificate.get("decision"),
        "transport_quiescence": certificate.get("transport_quiescence"),
    }


def expected_adoption_record_sha256(
    certificate: Mapping[str, Any], *, source_certificate_sha256: str,
) -> str:
    """Hash the frozen-v3 source and every v4 target evidence binding."""

    if not v1.root_aggregate.is_sha256(source_certificate_sha256):
        raise ValueError("source certificate SHA-256 invalid")
    return canonical_sha256(_adoption_binding_payload(
        certificate, source_certificate_sha256=source_certificate_sha256,
    ))


def adopted_transport_provenance(
    certificate: Mapping[str, Any], *, source_certificate_sha256: str,
) -> dict[str, Any]:
    """Build the exact provenance tuple for one frozen-v3 adoption."""

    return {
        "profile": TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
        "source_schema_version": FROZEN_V3_SCHEMA_VERSION,
        "source_runner_gate": FROZEN_V3_RUNNER_GATE,
        "source_runner_sha256": FROZEN_V3_RUNNER_SHA256,
        "source_certificate_sha256": source_certificate_sha256,
        "adoption_record_sha256": expected_adoption_record_sha256(
            certificate,
            source_certificate_sha256=source_certificate_sha256,
        ),
    }


def _transport_provenance_failures(
    value: Any, certificate: Mapping[str, Any],
) -> list[str]:
    raw = dict(value) if type(value) is dict else {}
    if set(raw) != TRANSPORT_PROVENANCE_FIELDS:
        return ["transport provenance field set mismatch"]
    profile = raw.get("profile")
    if profile == TRANSPORT_PROFILE_NATIVE_V4:
        if not v1._same(raw, native_transport_provenance()):
            return ["native v4 transport provenance truth table mismatch"]
        return []
    if profile != TRANSPORT_PROFILE_ADOPTED_FROZEN_V3:
        return ["unsupported transport provenance profile"]

    failures: list[str] = []
    for key, wanted in {
        "source_schema_version": FROZEN_V3_SCHEMA_VERSION,
        "source_runner_gate": FROZEN_V3_RUNNER_GATE,
        "source_runner_sha256": FROZEN_V3_RUNNER_SHA256,
    }.items():
        if not v1._same(raw.get(key), wanted):
            failures.append(f"adopted transport provenance {key} mismatch")
    source_certificate_sha256 = raw.get("source_certificate_sha256")
    if not v1.root_aggregate.is_sha256(source_certificate_sha256):
        failures.append("adopted source certificate SHA-256 invalid")
    adoption_record_sha256 = raw.get("adoption_record_sha256")
    if not v1.root_aggregate.is_sha256(adoption_record_sha256):
        failures.append("adoption record SHA-256 invalid")
    if v1.root_aggregate.is_sha256(source_certificate_sha256):
        try:
            expected = expected_adoption_record_sha256(
                certificate,
                source_certificate_sha256=source_certificate_sha256,
            )
        except (TypeError, ValueError):
            failures.append("adoption record target binding is not canonical")
        else:
            if adoption_record_sha256 != expected:
                failures.append("adoption record source binding mismatch")
    return list(dict.fromkeys(failures))


def _decision_failures(value: Any) -> list[str]:
    if type(value) is not dict or set(value) != DECISION_FIELDS:
        return ["UNSAT decision field set mismatch"]
    state = value.get("proof_source_state")
    if state not in TRANSPORT_STATES or not v1._same(
        value, EXPECTED_UNSAT_DECISIONS[state],
    ):
        return ["UNSAT proof-replay decision semantics mismatch"]
    return []


def _coordinator_observation_failures(
    value: Any, *, attempted: bool,
) -> list[str]:
    if type(value) is not dict or set(value) != COORDINATOR_OBSERVATION_FIELDS:
        return ["coordinator observation field set mismatch"]
    if value.get("attempted") is not attempted:
        return ["coordinator observation attempt mismatch"]
    reachable = value.get("reachable")
    if not attempted:
        if (
            reachable is not None
            or value.get("peer_count") is not None
            or value.get("running") is not None
        ):
            return ["unattempted coordinator observation is not empty"]
    elif reachable is True:
        if (
            type(value.get("peer_count")) is not int
            or value.get("peer_count") != 0
            or value.get("running") is not False
        ):
            return ["reachable coordinator still reports an active peer"]
    elif reachable is False:
        if value.get("peer_count") is not None or value.get("running") is not None:
            return ["unreachable coordinator observation is not empty"]
    else:
        return ["coordinator reachability is not a strict boolean"]
    return []


def _stopped_proof_failures(value: Any) -> list[str]:
    raw = dict(value) if type(value) is dict else {}
    failures: list[str] = []
    if set(raw) != STOPPED_PROOF_FIELDS:
        failures.append("stopped proof field set mismatch")
    if raw.get("role") != "raw-binary-drat":
        failures.append("stopped proof role mismatch")
    if raw.get("relative_path") != "runtime/dmtcp/proof.drat":
        failures.append("stopped proof path mismatch")
    if not v1.root_aggregate.is_sha256(raw.get("file_sha256")):
        failures.append("stopped proof SHA-256 invalid")
    if type(raw.get("bytes")) is not int or raw.get("bytes", 0) <= 0:
        failures.append("stopped proof byte count invalid")
    if raw.get("mode") != 0o600 or raw.get("links") != 1:
        failures.append("stopped proof mode/link policy mismatch")
    if type(raw.get("uid")) is not int or raw.get("uid", -1) < 0:
        failures.append("stopped proof uid invalid")
    for key in ("device", "inode"):
        if type(raw.get(key)) is not int or raw.get(key, 0) <= 0:
            failures.append(f"stopped proof {key} invalid")
    return failures


def _quiescence_failures(value: Any, proof_chain: Any) -> list[str]:
    raw = dict(value) if type(value) is dict else {}
    failures: list[str] = []
    if set(raw) != QUIESCENCE_FIELDS:
        failures.append("transport quiescence field set mismatch")
    state = raw.get("transport_state")
    expected_method = {
        TRANSPORT_STATE_CHECKPOINTED: "dmtcp-checkpoint-stop-v1",
        TRANSPORT_STATE_INACTIVE: "dmtcp-inactive-exit-harvest-v1",
    }.get(state)
    if expected_method is None or raw.get("method") != expected_method:
        failures.append("transport quiescence state/method mismatch")
    if (
        type(raw.get("latest_generation")) is not int
        or raw.get("latest_generation", -1) < 0
    ):
        failures.append("transport quiescence latest_generation invalid")
    for key in ("latest_pid", "latest_proc_start_ticks"):
        if type(raw.get(key)) is not int or raw.get(key, 0) <= 0:
            failures.append(f"transport quiescence {key} invalid")
    if raw.get("latest_pid_identity_alive") is not False:
        failures.append("transport proof source process is not dead")
    for key in ("writable_holders_before", "writable_holders_after"):
        if raw.get(key) != []:
            failures.append(f"{key} is not empty")
    observations = raw.get("coordinator_observations")
    attempted = state == TRANSPORT_STATE_INACTIVE
    if type(observations) is not list or len(observations) != 2:
        failures.append("coordinator observations are not an exact pair")
    else:
        for observation in observations:
            failures.extend(_coordinator_observation_failures(
                observation, attempted=attempted,
            ))
    before, after = raw.get("proof_before"), raw.get("proof_after")
    failures.extend(_stopped_proof_failures(before))
    failures.extend(_stopped_proof_failures(after))
    if not v1._same(before, after):
        failures.append("stopped proof changed across quiescence checks")
    binary_drat = (
        proof_chain.get("binary_drat") if type(proof_chain) is dict else None
    )
    if type(before) is dict and type(binary_drat) is dict and (
        before.get("file_sha256") != binary_drat.get("file_sha256")
        or before.get("bytes") != binary_drat.get("bytes")
    ):
        failures.append("quiescent source/copy DRAT binding mismatch")
    return list(dict.fromkeys(failures))


def validate_child_certificate(
    certificate: Any,
    refinement_manifest: Mapping[str, Any],
) -> list[str]:
    """Validate one v4 child certificate without requiring solver exit."""

    raw = dict(certificate) if type(certificate) is dict else {}
    failures: list[str] = []
    if set(raw) != CERTIFICATE_FIELDS:
        failures.append("certificate field set mismatch")
    if not v1._selfhash_valid(raw, "certificate_sha256"):
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
    failures.extend(v1._identity_failures(raw, refinement_manifest))

    child = v1._child_for_index(refinement_manifest, raw.get("child_index"))
    if child is not None:
        for key in (
            "child_num_variables",
            "child_num_clauses",
            "child_dimacs_bytes",
        ):
            if not v1._same(raw.get(key), child.get(key)):
                failures.append(f"{key} binding mismatch")

    expected_authority = v1._expected_authority(refinement_manifest)
    if expected_authority is None or raw.get("authority") != expected_authority:
        failures.append("certificate authority does not match refinement")
    expected_test_only = expected_authority != AUTHORITY_PRODUCTION
    if (
        type(raw.get("test_only")) is not bool
        or raw.get("test_only") is not expected_test_only
    ):
        failures.append("certificate authority/test_only mismatch")
    provenance_failures = _transport_provenance_failures(
        raw.get("transport_provenance"), raw,
    )
    failures.extend(provenance_failures)
    expected_production_eligible = bool(
        expected_authority == AUTHORITY_PRODUCTION
        and not provenance_failures
    )
    if raw.get("production_eligible") is not expected_production_eligible:
        failures.append("certificate production eligibility mismatch")

    root_aggregate = v1.root_aggregate
    expected_solver = {
        "name": root_aggregate.EXPECTED_SOLVER_NAME,
        "version": root_aggregate.EXPECTED_SOLVER_VERSION,
        "executable_sha256": root_aggregate.EXPECTED_SOLVER_SHA256,
    }
    solver = raw.get("solver")
    if type(solver) is not dict or set(solver) != set(expected_solver):
        failures.append("solver binding field set mismatch")
    elif not v1._same(solver, expected_solver):
        failures.append("solver binding mismatch")

    decision = raw.get("decision")
    proof_chain = raw.get("proof_chain")
    quiescence = raw.get("transport_quiescence")
    failures.extend(_decision_failures(decision))
    failures.extend(v1._proof_chain_failures(proof_chain))
    failures.extend(_quiescence_failures(quiescence, proof_chain))
    if (
        type(decision) is dict
        and type(quiescence) is dict
        and decision.get("proof_source_state")
        != quiescence.get("transport_state")
    ):
        failures.append("decision/quiescence transport state mismatch")
    for key in (
        "resume_static_sha256",
        "transport_chain_sha256",
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
    """Accept exactly one honest v4 proof-replay validation envelope."""

    raw = dict(record) if type(record) is dict else {}
    failures: list[str] = []
    if set(raw) != VALIDATION_FIELDS:
        failures.append("validation field set mismatch")
    if not v1._selfhash_valid(raw, "validation_sha256"):
        failures.append("validation self-hash mismatch")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
    ):
        failures.append("validation schema version mismatch")
    if (
        raw.get("kind") != CHILD_VALIDATION_KIND
        or raw.get("gate") != RUNNER_GATE
    ):
        failures.append("validation kind/gate mismatch")
    if type(raw.get("root")) is not str or not os.path.isabs(raw.get("root", "")):
        failures.append("validation root is not absolute")
    failures.extend(v1._identity_failures(raw, refinement_manifest))

    expected_authority = v1._expected_authority(refinement_manifest)
    if expected_authority is None or raw.get("authority") != expected_authority:
        failures.append("validation authority does not match refinement")
    if (
        type(raw.get("test_only")) is not bool
        or raw.get("test_only") is not (
            expected_authority != AUTHORITY_PRODUCTION
        )
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
    failures.extend(validate_child_certificate(certificate, refinement_manifest))
    failures.extend(_transport_provenance_failures(
        raw.get("transport_provenance"),
        certificate if type(certificate) is dict else {},
    ))
    if type(certificate) is dict:
        for key in (
            *IDENTITY_FIELDS, "authority", "test_only",
            "transport_provenance",
        ):
            if not v1._same(certificate.get(key), raw.get(key)):
                failures.append(f"certificate/validation {key} binding mismatch")
    return list(dict.fromkeys(failures))


def aggregate_child_validations(
    refinement_manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    validations: Sequence[Mapping[str, Any]],
    instance: v1.cube16.optimized.OptimizedInstance,
    *,
    expected_parent_cube_index: int,
    expected_split_width: int,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Derive parent UNSAT only from the v4 replay for every exact child."""

    manifest_replay = v1.hierarchy.verify_refinement_manifest(
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
        candidate_raw = candidate if type(candidate) is dict else {}
        certificate = candidate_raw.get("certificate")
        provenance = candidate_raw.get("transport_provenance")
        profile_failures = _transport_provenance_failures(
            provenance, certificate if type(certificate) is dict else {},
        )
        profile_consistent = bool(
            type(certificate) is dict
            and v1._same(
                provenance, certificate.get("transport_provenance"),
            )
        )
        failures = validate_child_run_record(candidate, refinement_manifest)
        records.append({
            "input_position": position,
            "child_index": candidate_raw.get("child_index"),
            "state": candidate_raw.get("state"),
            "transport_profile": (
                provenance.get("profile") if type(provenance) is dict else None
            ),
            "transport_provenance_complete": bool(
                not profile_failures and profile_consistent
            ),
            "valid": not failures,
            "binding_failures": failures,
            "validation_sha256": candidate_raw.get("validation_sha256"),
        })
    indices = [record["child_index"] for record in records]
    exact_indices = bool(
        expected_child_count > 0
        and len(indices) == expected_child_count
        and all(type(index) is int for index in indices)
        and sorted(indices) == list(range(expected_child_count))
    )
    all_transport_provenance_profiles_complete = bool(
        exact_indices
        and all(
            record["transport_provenance_complete"] is True
            for record in records
        )
    )
    all_proof_unsat = bool(
        manifest_authenticated
        and exact_indices
        and all_transport_provenance_profiles_complete
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
            "transport_profile": item["transport_provenance"]["profile"],
            "source_certificate_sha256": item["transport_provenance"][
                "source_certificate_sha256"
            ],
            "adoption_record_sha256": item["transport_provenance"][
                "adoption_record_sha256"
            ],
        } for item in sorted(validations, key=lambda item: item["child_index"])]

    parent = refinement_manifest.get("parent", {})
    authority = v1._expected_authority(refinement_manifest)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "aggregate_kind": AGGREGATE_KIND,
        "status": STATE_PARENT_UNSAT if all_proof_unsat else STATE_UNRESOLVED,
        "refinement_manifest_sha256": refinement_manifest.get(
            "manifest_sha256"
        ),
        "manifest_replay_record_sha256": manifest_replay.get("record_sha256"),
        "manifest_authenticated": manifest_authenticated,
        "manifest_binding_failures": manifest_replay.get("binding_failures", []),
        "parent_manifest_sha256": parent.get("manifest_sha256"),
        "parent_cube_index": parent.get("cube_index"),
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "expected_child_count": expected_child_count,
        "all_child_indices_exactly_once": exact_indices,
        "all_transport_provenance_profiles_complete": (
            all_transport_provenance_profiles_complete
        ),
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
            "need an authenticated exact refinement and exactly one honest v4 "
            "proof-replayed UNSAT envelope for every child"
        ),
    }, "aggregate_sha256")


__all__ = [
    "ADOPTION_RECORD_KIND",
    "ADOPTION_RECORD_SCHEMA_VERSION",
    "AGGREGATE_KIND",
    "AUTHORITY_PRODUCTION",
    "AUTHORITY_TEST_ONLY",
    "CERTIFICATE_FIELDS",
    "CHILD_CERTIFICATE_KIND",
    "CHILD_VALIDATION_KIND",
    "DECISION_FIELDS",
    "EXPECTED_UNSAT_DECISIONS",
    "FROZEN_V3_RUNNER_GATE",
    "FROZEN_V3_RUNNER_SHA256",
    "FROZEN_V3_SCHEMA_VERSION",
    "QUIESCENCE_FIELDS",
    "RUNNER_GATE",
    "SCHEMA_VERSION",
    "STATE_PARENT_UNSAT",
    "STATE_PROOF_UNSAT",
    "STATE_UNRESOLVED",
    "TRANSPORT_PROFILE_ADOPTED_FROZEN_V3",
    "TRANSPORT_PROFILE_NATIVE_V4",
    "TRANSPORT_PROFILES",
    "TRANSPORT_PROVENANCE_FIELDS",
    "TRANSPORT_STATE_CHECKPOINTED",
    "TRANSPORT_STATE_INACTIVE",
    "TRANSPORT_STATES",
    "VALIDATION_FIELDS",
    "adopted_transport_provenance",
    "aggregate_child_validations",
    "canonical_sha256",
    "expected_adoption_record_sha256",
    "expected_unsat_decision",
    "native_transport_provenance",
    "seal",
    "validate_child_certificate",
    "validate_child_run_record",
]
