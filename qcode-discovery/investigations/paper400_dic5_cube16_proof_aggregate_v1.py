#!/usr/bin/env python3
"""Strict proof-carrying aggregation for the paper400 Dic5 16-cube cover.

This module does not run a SAT solver or a proof checker.  It defines the
per-cube certificate and validation envelopes consumed by the add-only cube
runner, checks their exact bindings to ``paper400_dic5_cube16``, and combines
freshly validated roots.  A single cube certificate never carries a global
distance claim.  The global ``d >= 20`` claim is available only after all 16
mutually exclusive and exhaustive cubes have one independently replayed DRAT
and LRAT proof.

The in-memory aggregation entry point is deliberately useful for tests and
offline inspection.  Production callers should use ``aggregate_cube_roots``:
it invokes the runner's read-only root validator with fresh proof replay before
allowing a publication certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_cube16 as cube16  # noqa: E402


SCHEMA_VERSION = 1
RUNNER_GATE = "paper400-dic5-cube16-proof-carrying-v1"
CUBE_CERTIFICATE_KIND = "paper400-dic5-proof-carrying-cube-unsat-v1"
CUBE_VALIDATION_KIND = "paper400-dic5-cube-proof-root-validation-v1"
AGGREGATE_KIND = "paper400-dic5-cube16-proof-aggregate-v1"

STATE_PROOF_UNSAT = "PROOF_CARRYING_CUBE_UNSAT"
STATE_VERIFIED_SAT = "VERIFIED_SAT_LOW_OPERATOR"
STATE_UNRESOLVED = "UNRESOLVED"

AUTHORITY_PRODUCTION = "PRODUCTION"
AUTHORITY_TEST_ONLY = "TEST_ONLY"

EXPECTED_SOLVER_NAME = "cadical195"
EXPECTED_SOLVER_VERSION = "1.9.5"
EXPECTED_SOLVER_SHA256 = (
    "f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171"
)
EXPECTED_POLICY_SHA256 = (
    "4e284ca7f01079210d458d677a8b5e81dd619da408a5e88fcd61bc703775ef4f"
)
EXPECTED_DRAT_CHECKER_SHA256 = (
    "a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe"
)
EXPECTED_LRAT_CHECKER_SHA256 = (
    "5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517"
)
EXPECTED_CUBE16_SOURCE_SHA256 = (
    "fb2495e1c7acbcd32e2fffc3d4126c48b9042ec1375913bb5e753beb22b4e3c5"
)

CERTIFICATE_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", "manifest_sha256", "base_cnf_sha256",
    "base_dimacs_sha256", "cube_index", "cube_id", "cube_sha256",
    "cube_cnf_sha256", "cube_dimacs_sha256", "cube_num_variables",
    "cube_num_clauses", "cube_dimacs_bytes", "unit_clauses", "solver",
    "decision", "proof_chain", "cube16_source_sha256",
    "aggregate_source_sha256", "source_binding_sha256",
    "toolchain_binding_sha256", "predecessor_chain_sha256",
    "global_distance_claim", "publication_certificate", "upload_authorized",
    "certificate_sha256",
})

VALIDATION_FIELDS = frozenset({
    "schema_version", "kind", "gate", "root", "manifest_sha256",
    "cube_index", "cube_id", "cube_sha256", "cube_cnf_sha256",
    "cube_dimacs_sha256", "state", "authority", "test_only", "valid",
    "strict_proof_unsat", "strict_verified_sat", "fresh_proof_replay",
    "source_toolchain_fresh", "certificate", "sat_terminal", "failures",
    "validation_sha256",
})


class CubeProofAggregateError(RuntimeError):
    """A proof certificate, validation, root, or aggregate is malformed."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def is_sha256(value: Any, *, allow_zero: bool = False) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        valid = bytes.fromhex(value).hex() == value
    except ValueError:
        return False
    return bool(valid and (allow_zero or value != "0" * 64))


def selfhash_valid(value: Any, field: str) -> bool:
    if type(value) is not dict:
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field, None)
    try:
        return bool(is_sha256(stored, allow_zero=False) and stored == canonical_sha256(unsigned))
    except (TypeError, ValueError):
        return False


def _safe_relative_path(value: Any) -> bool:
    if type(value) is not str or not value or "\x00" in value:
        return False
    path = Path(value)
    return bool(not path.is_absolute() and ".." not in path.parts and path.parts)


def _artifact_reference_failures(value: Any, *, role: str) -> list[str]:
    failures: list[str] = []
    if type(value) is not dict or set(value) != {
        "role", "relative_path", "file_sha256", "bytes",
    }:
        return [f"{role} artifact field set mismatch"]
    if value.get("role") != role:
        failures.append(f"{role} artifact role mismatch")
    if not _safe_relative_path(value.get("relative_path")):
        failures.append(f"{role} artifact path unsafe")
    if not is_sha256(value.get("file_sha256")):
        failures.append(f"{role} artifact hash invalid")
    size = value.get("bytes")
    if type(size) is not int or size <= 0:
        failures.append(f"{role} artifact size invalid")
    return failures


def _cube_for_index(
    manifest: Mapping[str, Any], cube_index: Any,
) -> Mapping[str, Any] | None:
    cubes = manifest.get("cubes") if type(manifest) is dict else None
    if (
        type(cube_index) is int
        and 0 <= cube_index < 16
        and type(cubes) is list
        and len(cubes) == 16
        and type(cubes[cube_index]) is dict
    ):
        return cubes[cube_index]
    return None


def _binding_failures(
    value: Mapping[str, Any], manifest: Mapping[str, Any],
) -> list[str]:
    failures: list[str] = []
    cube = _cube_for_index(manifest, value.get("cube_index"))
    if cube is None:
        return ["cube index is not bound to the 16-cube manifest"]
    expected = {
        "manifest_sha256": manifest.get("manifest_sha256"),
        "cube_index": cube.get("cube_index"),
        "cube_id": cube.get("cube_id"),
        "cube_sha256": cube.get("cube_sha256"),
        "cube_cnf_sha256": cube.get("cube_cnf_sha256"),
        "cube_dimacs_sha256": cube.get("cube_dimacs_sha256"),
    }
    for key, wanted in expected.items():
        if not cube16.optimized.json_type_equal(value.get(key), wanted):
            failures.append(f"{key} binding mismatch")
    return list(dict.fromkeys(failures))


def validate_cube_certificate(
    certificate: Any,
    manifest: Mapping[str, Any],
    *,
    require_production: bool,
) -> list[str]:
    """Validate one durable cube-UNSAT certificate against the cover."""

    raw = dict(certificate) if type(certificate) is dict else {}
    failures: list[str] = []
    if set(raw) != CERTIFICATE_FIELDS:
        failures.append("certificate field set mismatch")
    if not selfhash_valid(raw, "certificate_sha256"):
        failures.append("certificate self-hash mismatch")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
    ):
        failures.append("certificate schema version mismatch")
    if raw.get("kind") != CUBE_CERTIFICATE_KIND or raw.get("gate") != RUNNER_GATE:
        failures.append("certificate kind/gate mismatch")
    if raw.get("state") != STATE_PROOF_UNSAT:
        failures.append("certificate state is not proof-carrying cube UNSAT")
    failures.extend(_binding_failures(raw, manifest))
    cube = _cube_for_index(manifest, raw.get("cube_index"))
    if cube is not None:
        expected = {
            "base_cnf_sha256": manifest.get("base", {}).get("cnf_sha256"),
            "base_dimacs_sha256": manifest.get("base", {}).get("dimacs_sha256"),
            "cube_num_variables": cube.get("cube_num_variables"),
            "cube_num_clauses": cube.get("cube_num_clauses"),
            "cube_dimacs_bytes": cube.get("cube_dimacs_bytes"),
            "unit_clauses": cube.get("unit_clauses"),
        }
        for key, wanted in expected.items():
            if not cube16.optimized.json_type_equal(raw.get(key), wanted):
                failures.append(f"{key} binding mismatch")

    authority = raw.get("authority")
    test_only = raw.get("test_only")
    if authority not in {AUTHORITY_PRODUCTION, AUTHORITY_TEST_ONLY}:
        failures.append("certificate authority invalid")
    if type(test_only) is not bool:
        failures.append("certificate test_only type invalid")
    expected_test_only = authority != AUTHORITY_PRODUCTION
    if type(test_only) is bool and test_only is not expected_test_only:
        failures.append("certificate authority/test_only mismatch")
    if raw.get("production_eligible") is not (authority == AUTHORITY_PRODUCTION):
        failures.append("certificate production eligibility mismatch")
    if require_production and (
        authority != AUTHORITY_PRODUCTION
        or test_only is not False
        or raw.get("production_eligible") is not True
    ):
        failures.append("production certificate required")

    solver = raw.get("solver")
    if type(solver) is not dict or set(solver) != {
        "name", "version", "executable_sha256",
    }:
        failures.append("solver binding field set mismatch")
    elif (
        solver.get("name") != EXPECTED_SOLVER_NAME
        or solver.get("version") != EXPECTED_SOLVER_VERSION
        or solver.get("executable_sha256") != EXPECTED_SOLVER_SHA256
    ):
        failures.append("solver binding mismatch")

    decision = raw.get("decision")
    expected_decision = {
        "outcome": "unsat",
        "status_name": "UNSATISFIABLE",
        "decision_complete": True,
        "clean_exit": True,
        "timed_out": False,
        "solver_invocations": 1,
    }
    if not cube16.optimized.json_type_equal(decision, expected_decision):
        failures.append("UNSAT decision semantics mismatch")

    chain = raw.get("proof_chain")
    chain_fields = {
        "format", "binary_drat", "converted_lrat", "drat_checker_sha256",
        "lrat_checker_sha256", "trusted_policy_sha256",
        "drat_independently_verified", "lrat_independently_verified",
        "fresh_drat_replay", "fresh_lrat_replay", "drat_record_sha256",
        "lrat_record_sha256", "fresh_replay_record_sha256", "chain_sha256",
    }
    if type(chain) is not dict or set(chain) != chain_fields:
        failures.append("proof chain field set mismatch")
    else:
        unsigned_chain = dict(chain)
        stored_chain_hash = unsigned_chain.pop("chain_sha256", None)
        try:
            if not is_sha256(stored_chain_hash) or stored_chain_hash != canonical_sha256(unsigned_chain):
                failures.append("proof chain self-hash mismatch")
        except (TypeError, ValueError):
            failures.append("proof chain is not canonical JSON")
        if chain.get("format") != "binary-drat+converted-lrat-v1":
            failures.append("proof chain format mismatch")
        failures.extend(_artifact_reference_failures(
            chain.get("binary_drat"), role="raw-binary-drat",
        ))
        failures.extend(_artifact_reference_failures(
            chain.get("converted_lrat"), role="converted-lrat",
        ))
        expected_hashes = {
            "drat_checker_sha256": EXPECTED_DRAT_CHECKER_SHA256,
            "lrat_checker_sha256": EXPECTED_LRAT_CHECKER_SHA256,
            "trusted_policy_sha256": EXPECTED_POLICY_SHA256,
        }
        for key, wanted in expected_hashes.items():
            if chain.get(key) != wanted:
                failures.append(f"{key} mismatch")
        for key in (
            "drat_independently_verified", "lrat_independently_verified",
            "fresh_drat_replay", "fresh_lrat_replay",
        ):
            if chain.get(key) is not True:
                failures.append(f"{key} is not true")
        for key in (
            "drat_record_sha256", "lrat_record_sha256",
            "fresh_replay_record_sha256",
        ):
            if not is_sha256(chain.get(key)):
                failures.append(f"{key} invalid")

    for key in (
        "source_binding_sha256", "toolchain_binding_sha256",
        "predecessor_chain_sha256",
    ):
        if not is_sha256(raw.get(key)):
            failures.append(f"{key} invalid")
    if raw.get("cube16_source_sha256") != EXPECTED_CUBE16_SOURCE_SHA256:
        failures.append("cube16 source hash mismatch")
    aggregate_source_sha256 = cube16._file_sha256(Path(__file__))
    if raw.get("aggregate_source_sha256") != aggregate_source_sha256:
        failures.append("aggregate source hash mismatch")
    if raw.get("global_distance_claim") is not None:
        failures.append("a single cube certificate cannot make a global distance claim")
    if raw.get("publication_certificate") is not False:
        failures.append("a single cube certificate is not a publication certificate")
    if raw.get("upload_authorized") is not False:
        failures.append("cube certificate cannot authorize upload")
    return failures


def validate_cube_run_record(
    record: Any,
    manifest: Mapping[str, Any],
    *,
    require_production: bool,
) -> list[str]:
    """Validate the read-only result returned by one runner root replay."""

    raw = dict(record) if type(record) is dict else {}
    failures: list[str] = []
    if set(raw) != VALIDATION_FIELDS:
        failures.append("validation field set mismatch")
    if not selfhash_valid(raw, "validation_sha256"):
        failures.append("validation self-hash mismatch")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
    ):
        failures.append("validation schema version mismatch")
    if raw.get("kind") != CUBE_VALIDATION_KIND or raw.get("gate") != RUNNER_GATE:
        failures.append("validation kind/gate mismatch")
    if type(raw.get("root")) is not str or not os.path.isabs(raw.get("root", "")):
        failures.append("validation root is not absolute")
    failures.extend(_binding_failures(raw, manifest))
    authority = raw.get("authority")
    test_only = raw.get("test_only")
    if authority not in {AUTHORITY_PRODUCTION, AUTHORITY_TEST_ONLY}:
        failures.append("validation authority invalid")
    if type(test_only) is not bool or test_only is not (authority != AUTHORITY_PRODUCTION):
        failures.append("validation authority/test_only mismatch")
    if require_production and (authority != AUTHORITY_PRODUCTION or test_only is not False):
        failures.append("production validation required")
    if type(raw.get("failures")) is not list or any(
        type(value) is not str for value in raw.get("failures", [])
    ):
        failures.append("validation failures list invalid")

    state = raw.get("state")
    proof_unsat = raw.get("strict_proof_unsat")
    verified_sat = raw.get("strict_verified_sat")
    fresh = raw.get("fresh_proof_replay")
    source_fresh = raw.get("source_toolchain_fresh")
    if state == STATE_PROOF_UNSAT:
        if not (
            proof_unsat is True and verified_sat is False and fresh is True
            and source_fresh is True and raw.get("valid") is True
            and raw.get("sat_terminal") is None and raw.get("failures") == []
        ):
            failures.append("proof-UNSAT validation truth table mismatch")
        certificate = raw.get("certificate")
        failures.extend(validate_cube_certificate(
            certificate, manifest,
            require_production=require_production,
        ))
        if type(certificate) is dict:
            for key in (
                "manifest_sha256", "cube_index", "cube_id", "cube_sha256",
                "cube_cnf_sha256", "cube_dimacs_sha256", "authority",
                "test_only",
            ):
                if not cube16.optimized.json_type_equal(
                    certificate.get(key), raw.get(key),
                ):
                    failures.append(f"certificate/validation {key} binding mismatch")
    elif state == STATE_VERIFIED_SAT:
        if not (
            proof_unsat is False and verified_sat is True and fresh is False
            and source_fresh is True and raw.get("valid") is True
            and raw.get("certificate") is None and raw.get("failures") == []
        ):
            failures.append("verified-SAT validation truth table mismatch")
        terminal = raw.get("sat_terminal")
        if (
            type(terminal) is not dict
            or terminal.get("classification") != "VERIFIED_SAT_LOW_OPERATOR"
            or terminal.get("strict_verified_sat") is not True
            or not cube16.optimized.json_type_equal(
                terminal.get("cube_index"), raw.get("cube_index")
            )
            or not is_sha256(terminal.get("record_sha256"))
        ):
            failures.append("verified SAT terminal binding invalid")
    elif state == STATE_UNRESOLVED:
        if not (
            proof_unsat is False and verified_sat is False
            and raw.get("valid") is False
            and type(raw.get("failures")) is list
            and len(raw.get("failures", [])) > 0
        ):
            failures.append("UNRESOLVED validation truth table mismatch")
    else:
        failures.append("validation state invalid")
    return failures


def _aggregate(
    manifest: Mapping[str, Any],
    validations: Sequence[Mapping[str, Any]],
    instance: cube16.optimized.OptimizedInstance,
    *,
    strict_base: bool,
    roots_freshly_validated: bool,
) -> dict[str, Any]:
    manifest_record = cube16.verify_coverage_manifest(
        manifest, instance, strict_base=strict_base,
    )
    production_manifest = bool(
        manifest_record.get("valid") is True
        and manifest_record.get("base_audit_pass_bound") is True
        and manifest.get("test_only") is False
    )
    records: list[dict[str, Any]] = []
    for offset, candidate in enumerate(validations):
        require_production = production_manifest
        failures = validate_cube_run_record(
            candidate, manifest, require_production=require_production,
        )
        records.append({
            "input_position": offset,
            "cube_index": candidate.get("cube_index") if type(candidate) is dict else None,
            "state": candidate.get("state") if type(candidate) is dict else None,
            "valid": not failures,
            "binding_failures": failures,
            "validation_sha256": (
                candidate.get("validation_sha256") if type(candidate) is dict else None
            ),
        })

    strict_sat_candidates = [
        record for record, candidate in zip(records, validations, strict=True)
        if record["valid"]
        and candidate.get("strict_verified_sat") is True
        and candidate.get("state") == STATE_VERIFIED_SAT
    ]
    indices = [record["cube_index"] for record in records]
    exact_indices = bool(
        len(indices) == 16
        and all(type(index) is int for index in indices)
        and sorted(indices) == list(range(16))
    )
    all_proof_unsat = bool(
        exact_indices
        and all(record["valid"] for record in records)
        and all(
            candidate.get("state") == STATE_PROOF_UNSAT
            and candidate.get("strict_proof_unsat") is True
            and candidate.get("fresh_proof_replay") is True
            and candidate.get("source_toolchain_fresh") is True
            for candidate in validations
        )
    )
    authoritative = bool(
        roots_freshly_validated and production_manifest and all_proof_unsat
    )
    authoritative_sat = bool(
        roots_freshly_validated
        and production_manifest
        and strict_sat_candidates
        and all(
            candidate.get("authority") == AUTHORITY_PRODUCTION
            and candidate.get("test_only") is False
            and candidate.get("source_toolchain_fresh") is True
            for record, candidate in zip(records, validations, strict=True)
            if record["valid"] and candidate.get("strict_verified_sat") is True
        )
    )
    if manifest_record.get("valid") is not True:
        status, lower = STATE_UNRESOLVED, None
    elif authoritative_sat:
        status, lower = "REJECTED_LOW_OPERATOR", None
    elif strict_sat_candidates and manifest.get("test_only") is True:
        status, lower = "TEST_ONLY_VERIFIED_SAT_NO_SCIENTIFIC_CLAIM", None
    elif strict_sat_candidates:
        status, lower = "CANDIDATE_VERIFIED_SAT_REQUIRES_FRESH_ROOT_REPLAY", None
    elif all_proof_unsat and manifest.get("test_only") is True:
        status, lower = "TEST_ONLY_ALL_CUBES_PROOF_UNSAT_NO_SCIENTIFIC_CLAIM", None
    elif authoritative:
        status, lower = "PROOF_CARRYING_LOWER_20", 20
    elif all_proof_unsat:
        status, lower = "CANDIDATE_PROOF_CARRYING_LOWER_20_REQUIRES_FRESH_ROOT_REPLAY", None
    else:
        status, lower = STATE_UNRESOLVED, None

    ordered_certificates: list[dict[str, Any]] = []
    if all_proof_unsat:
        ordered = sorted(validations, key=lambda item: item["cube_index"])
        ordered_certificates = [{
            "cube_index": item["cube_index"],
            "cube_id": item["cube_id"],
            "validation_sha256": item["validation_sha256"],
            "certificate_sha256": item["certificate"]["certificate_sha256"],
            "cube_cnf_sha256": item["cube_cnf_sha256"],
        } for item in ordered]
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "aggregate_kind": AGGREGATE_KIND,
        "manifest_sha256": manifest.get("manifest_sha256"),
        "status": status,
        "distance_lower_bound": lower,
        "strict_verified_sat_count": len(strict_sat_candidates),
        "all_16_indices_exactly_once": exact_indices,
        "all_16_proof_carrying_unsat": all_proof_unsat,
        "roots_freshly_validated": roots_freshly_validated,
        "production_manifest": production_manifest,
        "cube_records": records,
        "ordered_certificate_bindings": ordered_certificates,
        "publication_certificate": authoritative,
        "upload_authorized": False,
        "claim_semantics": {
            "distance_claim": "d>=20" if authoritative else None,
            "exact_distance_claimed": False,
            "paper_upper_bound_used_as_exact": False,
            "cover_equivalence": "F iff OR_i(F AND cube_i)",
        },
        "blocker": (
            None if authoritative or authoritative_sat
            else "need exactly one freshly replayed proof-carrying UNSAT root for every cube"
        ),
    }, "aggregate_sha256")
    return result


def aggregate_cube_validations(
    manifest: Mapping[str, Any],
    validations: Sequence[Mapping[str, Any]],
    instance: cube16.optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Aggregate envelopes without granting production publication authority."""

    return _aggregate(
        manifest, validations, instance, strict_base=strict_base,
        roots_freshly_validated=False,
    )


def aggregate_cube_roots(
    manifest: Mapping[str, Any],
    roots: Sequence[Path],
    instance: cube16.optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
    validator: Callable[[Path, Mapping[str, Any]], Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Freshly replay each root and aggregate it.

    ``validator`` exists for focused tests.  Production callers omit it, which
    resolves the add-only cube runner and asks it to re-run both proof checkers.
    """

    injected_validator = validator is not None
    if validator is None:
        from scripts import run_paper400_dic5_cube16_standalone_proof_v1 as runner

        def validator(path: Path, bound_manifest: Mapping[str, Any]) -> Mapping[str, Any]:
            return runner.validate_final_root(
                path, bound_manifest=bound_manifest, execute_fresh_replay=True,
            )
    validations = [dict(validator(Path(root), manifest)) for root in roots]
    return _aggregate(
        manifest, validations, instance, strict_base=strict_base,
        roots_freshly_validated=not injected_validator,
    )


def _strict_json(path: Path) -> dict[str, Any]:
    target = Path(path)
    if target.is_symlink() or not target.is_file():
        raise CubeProofAggregateError(f"not a regular JSON file: {target}")
    payload = target.read_bytes()
    try:
        text = payload.decode("utf-8")
        decoder = json.JSONDecoder(
            object_pairs_hook=lambda pairs: _unique_object(pairs),
            parse_constant=lambda token: (_ for _ in ()).throw(
                ValueError(f"invalid numeric constant: {token}")
            ),
        )
        value, end = decoder.raw_decode(text)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise CubeProofAggregateError(f"invalid strict JSON: {target}") from exc
    if text[end:].strip() or type(value) is not dict:
        raise CubeProofAggregateError(f"invalid JSON root/trailing data: {target}")
    return value


def _unique_object(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--root", required=True, action="append", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    manifest = _strict_json(args.manifest)
    instance = cube16.optimized.build_optimized_instance()
    result = aggregate_cube_roots(manifest, args.root, instance, strict_base=True)
    print(canonical_bytes(result).decode("utf-8"))
    return 0 if result["status"] in {
        "PROOF_CARRYING_LOWER_20", "REJECTED_LOW_OPERATOR",
    } else 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "AGGREGATE_KIND", "AUTHORITY_PRODUCTION", "AUTHORITY_TEST_ONLY",
    "CUBE_CERTIFICATE_KIND", "CUBE_VALIDATION_KIND", "CubeProofAggregateError",
    "RUNNER_GATE", "SCHEMA_VERSION", "STATE_PROOF_UNSAT",
    "STATE_UNRESOLVED", "STATE_VERIFIED_SAT", "aggregate_cube_roots",
    "aggregate_cube_validations", "canonical_bytes", "canonical_sha256",
    "is_sha256", "seal", "selfhash_valid", "validate_cube_certificate",
    "validate_cube_run_record",
]
