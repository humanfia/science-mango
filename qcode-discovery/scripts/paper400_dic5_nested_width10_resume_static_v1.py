#!/usr/bin/env python3
"""Execution-free static binding for one resumable parent000 width-ten leaf.

The record binds the original root-cover manifest, the authenticated width-six
campaign, the nested 1024-leaf width-ten campaign, one exact leaf DIMACS, the
pinned tool set, and the final DRAT/LRAT replay obligations.  It grants no
solver, publication, or upload authority by itself.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Any, Mapping

from investigations import paper400_dic5_nested_width10_campaign_v1 as nested
from scripts import paper400_dic5_hierarchical_resume_static_v2 as base


PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 1
KIND = "paper400-dic5-nested-width10-resume-static-v1"
GATE = "paper400-dic5-nested-width10-resume-static-v1"
STATE = "RESUMABLE_STATIC_SEALED"
EXPECTED_PARENT_CUBE_INDEX = nested.TARGET_PARENT_CUBE_INDEX
EXPECTED_SPLIT_WIDTH = 10
EXPECTED_LEAF_COUNT = 1024

AUTHORITY_PRODUCTION_CANDIDATE = base.AUTHORITY_PRODUCTION_CANDIDATE
AUTHORITY_SYNTHETIC_TEST_ONLY = base.AUTHORITY_SYNTHETIC_TEST_ONLY
CAP_INPUT_FIELDS = base.CAP_INPUT_FIELDS
EXECUTABLE_TOOL_ROLES = base.EXECUTABLE_TOOL_ROLES
TOOL_ROLES = base.TOOL_ROLES
ResumeStaticError = base.ResumeStaticError
canonical_bytes = base.canonical_bytes
canonical_sha256 = base.canonical_sha256
json_type_equal = base.json_type_equal
normalize_resource_caps = base.normalize_resource_caps
seal = base.seal
selfhash_valid = base.selfhash_valid

STATIC_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", "root", "root_identity", "parent_manifest",
    "width6_campaign", "width10_campaign", "campaign_verification",
    "child", "cnf_artifact",
    "source_binding", "toolchain_binding", "resource_policy",
    "resume_policy", "fresh_replay_policy", "claim_scope",
    "publication_certificate", "upload_authorized", "record_sha256",
})


def _internal_source_binding() -> dict[str, Any]:
    sources = {
        "nested_width10_resume_static_source": Path(__file__).resolve(),
        "resume_static_v2_primitives_source": Path(base.__file__).resolve(),
        "nested_width10_campaign_source": Path(nested.__file__).resolve(),
        "width6_campaign_source": Path(nested.width6.__file__).resolve(),
        "hierarchical_refiner_source": Path(nested.hierarchy.__file__).resolve(),
        "parent_cover_source": Path(nested.cube16.__file__).resolve(),
        "optimized_builder_source": Path(
            nested.cube16.optimized.__file__
        ).resolve(),
    }
    records: dict[str, Any] = {}
    for role, path in sorted(sources.items()):
        record, _ = base._stable_file_record(path, role=role)
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise ResumeStaticError(
                f"internal source escapes project: {role}"
            ) from exc
        record.pop("path")
        record["relative_path"] = relative
        records[role] = record
    return {
        "method": "fresh-current-source-sha256-replay-width10-v1",
        "sources": records,
        "source_role_sequence_sha256": canonical_sha256(sorted(records)),
    }


def _authority(
    parent_manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    width10_campaign: Mapping[str, Any],
) -> str:
    flags = (
        parent_manifest.get("test_only"),
        width6_campaign.get("test_only"),
        width10_campaign.get("test_only"),
    )
    if any(type(value) is not bool for value in flags):
        raise ResumeStaticError(
            "parent/campaign test-only flags must be strict booleans"
        )
    if len(set(flags)) != 1:
        raise ResumeStaticError("parent/campaign authority mismatch")
    return (
        AUTHORITY_SYNTHETIC_TEST_ONLY
        if flags[0]
        else AUTHORITY_PRODUCTION_CANDIDATE
    )


def _require_width10_request(
    *, parent_cube_index: int, global_leaf_index: int,
) -> None:
    if (
        nested.TARGET_PARENT_CUBE_INDEX != EXPECTED_PARENT_CUBE_INDEX
        or nested.SPLIT_WIDTH != EXPECTED_SPLIT_WIDTH
        or nested.LEAF_COUNT != EXPECTED_LEAF_COUNT
    ):
        raise ResumeStaticError("nested width-ten campaign constants drifted")
    if (
        type(parent_cube_index) is not int
        or parent_cube_index != EXPECTED_PARENT_CUBE_INDEX
    ):
        raise ResumeStaticError("width-ten launch is restricted to parent000")
    if (
        type(global_leaf_index) is not int
        or not 0 <= global_leaf_index < EXPECTED_LEAF_COUNT
    ):
        raise ResumeStaticError("global leaf index must be in 0..1023")


def _campaign_binding(
    manifest: Mapping[str, Any], *, role: str,
) -> dict[str, Any]:
    return base._manifest_binding(
        manifest, role=role, self_hash_field="manifest_sha256",
    )


def _require_campaign_verification_record(
    record: Mapping[str, Any], *, campaign_manifest_sha256: str,
) -> dict[str, Any]:
    raw = dict(record) if type(record) is dict else {}
    expected = {
        "schema_version": nested.SCHEMA_VERSION,
        "kind": nested.VERIFICATION_KIND,
        "campaign_manifest_sha256": campaign_manifest_sha256,
        "expected_manifest_sha256": campaign_manifest_sha256,
        "parent_cube_index": EXPECTED_PARENT_CUBE_INDEX,
        "valid": True,
        "binding_failures": [],
        "width6_prefix_count": nested.WIDTH6_LEAF_COUNT,
        "leaf_count": EXPECTED_LEAF_COUNT,
        "mutually_exclusive": True,
        "exhaustive": True,
        "parent000_formula_equivalence_certified": True,
        "solver_invoked": False,
        "launch_authorized_by_this_record": False,
        "publication_certificate": False,
    }
    if (
        set(raw) != nested.VERIFICATION_FIELDS
        or not nested.selfhash_valid(raw, "record_sha256")
        or raw.get("record_sha256") != nested.canonical_sha256(expected)
        or not nested.json_type_equal(
            {key: raw.get(key) for key in expected}, expected
        )
    ):
        raise ResumeStaticError(
            "campaign verification record is not the exact successful replay result"
        )
    return raw


def _verified_payload_for_leaf(payload: Any, leaf: Mapping[str, Any]) -> bytes:
    if type(payload) is not bytes:
        raise ResumeStaticError("verified child DIMACS must be exact bytes")
    if (
        len(payload) != leaf.get("child_dimacs_bytes")
        or hashlib.sha256(payload).hexdigest()
        != leaf.get("child_dimacs_sha256")
    ):
        raise ResumeStaticError(
            "verified child DIMACS does not match the selected leaf"
        )
    return payload


def build_resume_static_record(
    *,
    root: Path,
    parent_manifest: Mapping[str, Any],
    width6_campaign_manifest: Mapping[str, Any],
    width10_campaign_manifest: Mapping[str, Any],
    instance: Any,
    parent_cube_index: int,
    global_leaf_index: int,
    campaign_verification_record: Mapping[str, Any],
    verified_child_dimacs: bytes,
    child_cnf_path: Path,
    tool_paths: Mapping[str, Path],
    expected_tool_sha256: Mapping[str, str],
    resource_caps: Mapping[str, Any],
    strict_base: bool = True,
) -> dict[str, Any]:
    """Build one static root only after a complete nested-campaign replay."""

    target = base._plain_absolute_directory(Path(root))
    if type(strict_base) is not bool:
        raise ResumeStaticError("strict_base must be a strict boolean")
    _require_width10_request(
        parent_cube_index=parent_cube_index,
        global_leaf_index=global_leaf_index,
    )

    verification = _require_campaign_verification_record(
        campaign_verification_record,
        campaign_manifest_sha256=width10_campaign_manifest.get(
            "manifest_sha256"
        ),
    )
    leaves = width10_campaign_manifest.get("leaves")
    if (
        type(leaves) is not list
        or len(leaves) != EXPECTED_LEAF_COUNT
        or type(leaves[global_leaf_index]) is not dict
    ):
        raise ResumeStaticError("campaign does not contain exactly 1024 leaves")
    leaf = leaves[global_leaf_index]
    if leaf.get("global_leaf_index") != global_leaf_index:
        raise ResumeStaticError("global leaf index/record mismatch")
    expected_cnf = _verified_payload_for_leaf(verified_child_dimacs, leaf)
    cnf_record, observed_cnf = base._stable_file_record(
        Path(child_cnf_path),
        role="exact-nested-width10-child-cnf",
        relative_to=target,
        cap=max(len(expected_cnf), 1),
    )
    if observed_cnf != expected_cnf:
        raise ResumeStaticError("width-ten child CNF differs from verified bytes")

    authority = _authority(
        parent_manifest, width6_campaign_manifest, width10_campaign_manifest,
    )
    if strict_base and authority != AUTHORITY_PRODUCTION_CANDIDATE:
        raise ResumeStaticError("strict replay cannot use test-only manifests")
    if not strict_base and authority != AUTHORITY_SYNTHETIC_TEST_ONLY:
        raise ResumeStaticError("non-strict replay requires synthetic manifests")

    parent_binding = _campaign_binding(
        parent_manifest, role="paper400-root-cover",
    )
    parent = parent_manifest["cubes"][parent_cube_index]
    parent_binding.update({
        "parent_cube_index": parent_cube_index,
        "parent_cube_id": parent.get("cube_id"),
        "parent_cube_sha256": parent.get("cube_sha256"),
        "parent_cube_cnf_sha256": parent.get("cube_cnf_sha256"),
        "parent_cube_dimacs_sha256": parent.get("cube_dimacs_sha256"),
    })
    width6_binding = _campaign_binding(
        width6_campaign_manifest,
        role="paper400-parent000-width6-campaign",
    )
    width6_binding.update({
        "selected_parent_binding_sha256": width6_campaign_manifest.get(
            "selected_parent", {}
        ).get("selected_parent_binding_sha256"),
        "refinement_manifest_sha256": width6_campaign_manifest.get(
            "refinement", {}
        ).get("manifest_sha256"),
        "split_width": nested.WIDTH6_SPLIT_WIDTH,
        "leaf_count": nested.WIDTH6_LEAF_COUNT,
        "coverage_mutually_exclusive": width6_campaign_manifest.get(
            "coverage", {}
        ).get("mutually_exclusive"),
        "coverage_exhaustive": width6_campaign_manifest.get(
            "coverage", {}
        ).get("exhaustive"),
    })
    width10_binding = _campaign_binding(
        width10_campaign_manifest,
        role="paper400-parent000-nested-width10-campaign",
    )
    width10_binding.update({
        "width6_campaign_binding_sha256": width10_campaign_manifest.get(
            "width6_campaign", {}
        ).get("width6_campaign_binding_sha256"),
        "split_width": EXPECTED_SPLIT_WIDTH,
        "leaf_count": EXPECTED_LEAF_COUNT,
        "variables_dimacs": width10_campaign_manifest.get(
            "refinement", {}
        ).get("width10_variables_dimacs"),
        "coverage_mutually_exclusive": width10_campaign_manifest.get(
            "global_coverage", {}
        ).get("mutually_exclusive"),
        "coverage_exhaustive": width10_campaign_manifest.get(
            "global_coverage", {}
        ).get("exhaustive"),
        "parent_formula_equivalence_certified": width10_campaign_manifest.get(
            "global_coverage", {}
        ).get("parent_formula_equivalence_certified"),
    })
    child = {
        "child_index": leaf.get("global_leaf_index"),
        "child_id": leaf.get("global_leaf_id"),
        "child_sha256": leaf.get("leaf_sha256"),
        "global_leaf_index": leaf.get("global_leaf_index"),
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "parent_cube_index": leaf.get("parent_cube_index"),
        "width6_leaf_index": leaf.get("width6_leaf_index"),
        "width6_leaf_sha256": leaf.get("width6_leaf_sha256"),
        "local_child_index": leaf.get("local_child_index"),
        "combined_unit_clauses": leaf.get("combined_unit_clauses"),
        "combined_unit_clauses_sha256": leaf.get(
            "combined_unit_clauses_sha256"
        ),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "child_num_variables": leaf.get("child_num_variables"),
        "child_num_clauses": leaf.get("child_num_clauses"),
        "child_dimacs_bytes": leaf.get("child_dimacs_bytes"),
        "leaf_record_canonical_sha256": canonical_sha256(leaf),
    }

    caps = normalize_resource_caps(resource_caps)
    sources = _internal_source_binding()
    tools = base._toolchain_binding(tool_paths, expected_tool_sha256)
    test_only = authority == AUTHORITY_SYNTHETIC_TEST_ONLY
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "gate": GATE,
        "state": STATE,
        "authority": authority,
        "test_only": test_only,
        "production_eligible": False,
        "root": str(target),
        "root_identity": base._root_identity(target),
        "parent_manifest": parent_binding,
        "width6_campaign": width6_binding,
        "width10_campaign": width10_binding,
        "campaign_verification": {
            "record": verification,
            "record_sha256": verification["record_sha256"],
            "same_process_full_replay_required_at_prepare": True,
            "record_alone_is_launch_authority": False,
        },
        "child": child,
        "cnf_artifact": cnf_record,
        "source_binding": sources,
        "toolchain_binding": tools,
        "resource_policy": caps,
        "resume_policy": {
            "resume": True,
            "mode": "exact-live-process-dmtcp-generation-chain-v1",
            "workers_per_solver": 1,
            "checkpoint_generation_single_use": True,
            "proof_prefix_append_only_binding_required": True,
            "checkpoint_image_hash_binding_required": True,
            "single_writer_stopped_before_checkpoint_adoption": True,
            "dmtcp_transport_authority": "TEST_ONLY",
            "dmtcp_transport_trusted_for_scientific_proof": False,
            "old_width6_root_may_be_reinterpreted": False,
        },
        "fresh_replay_policy": {
            "fresh_static_replay_before_start": True,
            "fresh_static_replay_before_each_resume": True,
            "checkpoint_or_drat_prefix_is_terminal_evidence": False,
            "complete_drat_from_exact_child_cnf_required": True,
            "drat_to_lrat_conversion_required": True,
            "fresh_lrat_replay_from_exact_child_cnf_required": True,
            "all_tool_and_source_hashes_replayed_before_promotion": True,
            "detached_process_exit_code_may_substitute_for_proof_replay": False,
        },
        "claim_scope": {
            "quantum_code_changed": False,
            "base_cnf_changed": False,
            "only_parent_and_width10_physical_units_added": True,
            "child_unsat_alone_proves_parent000_unsat": False,
            "child_unsat_alone_proves_global_distance_lower_bound": False,
            "all_1024_authenticated_leaf_proofs_required": True,
            "full_campaign_replay_required_at_batch_prepare": True,
            "verification_record_alone_is_launch_authority": False,
            "inherited_distance_lower_bound_target": width10_campaign_manifest.get(
                "claim_preservation", {}
            ).get("inherited_distance_lower_bound_target"),
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })


def verify_resume_static_record(
    record: Mapping[str, Any],
    *,
    root: Path,
    parent_manifest: Mapping[str, Any],
    width6_campaign_manifest: Mapping[str, Any],
    width10_campaign_manifest: Mapping[str, Any],
    instance: Any,
    parent_cube_index: int,
    global_leaf_index: int,
    campaign_verification_record: Mapping[str, Any],
    child_cnf_path: Path,
    tool_paths: Mapping[str, Path],
    expected_tool_sha256: Mapping[str, str],
    resource_caps: Mapping[str, Any],
    strict_base: bool = True,
    verified_child_dimacs: bytes | None = None,
) -> dict[str, Any]:
    """Freshly rebuild and exact-compare one width-ten static record."""

    raw = dict(record) if type(record) is dict else {}
    failures: list[str] = []
    if set(raw) != STATIC_FIELDS:
        failures.append("static field set mismatch")
    if not selfhash_valid(raw):
        failures.append("static self-hash mismatch")
    if raw.get("schema_version") != SCHEMA_VERSION:
        failures.append("static schema version mismatch")
    if raw.get("kind") != KIND or raw.get("gate") != GATE:
        failures.append("static kind/gate mismatch")
    if raw.get("state") != STATE:
        failures.append("static state mismatch")
    expected_authority = (
        AUTHORITY_PRODUCTION_CANDIDATE
        if strict_base else AUTHORITY_SYNTHETIC_TEST_ONLY
    )
    if raw.get("authority") != expected_authority:
        failures.append("static authority mismatch")
    for field in ("production_eligible", "publication_certificate", "upload_authorized"):
        if raw.get(field) is not False:
            failures.append(f"static {field} must be false")
    if raw.get("root") != str(Path(root)):
        failures.append("static root does not match caller expectation")
    if raw.get("width10_campaign", {}).get("split_width") != EXPECTED_SPLIT_WIDTH:
        failures.append("static split width is not exactly ten")
    if raw.get("width10_campaign", {}).get("leaf_count") != EXPECTED_LEAF_COUNT:
        failures.append("static leaf count is not exactly 1024")
    resume_policy = raw.get("resume_policy")
    if type(resume_policy) is not dict or resume_policy.get("resume") is not True:
        failures.append("static resume=True policy is missing")
    fresh_policy = raw.get("fresh_replay_policy")
    if (
        type(fresh_policy) is not dict
        or fresh_policy.get("complete_drat_from_exact_child_cnf_required") is not True
        or fresh_policy.get("fresh_lrat_replay_from_exact_child_cnf_required") is not True
        or fresh_policy.get("checkpoint_or_drat_prefix_is_terminal_evidence") is not False
    ):
        failures.append("mandatory final fresh replay policy is missing")
    try:
        expected_caps = normalize_resource_caps(resource_caps)
        if not json_type_equal(raw.get("resource_policy"), expected_caps):
            failures.append("resource caps do not match caller policy")
    except ResumeStaticError as exc:
        failures.append(f"caller resource cap policy invalid: {exc}")

    expected: dict[str, Any] | None = None
    try:
        verification_binding = raw.get("campaign_verification")
        embedded_verification = (
            verification_binding.get("record")
            if type(verification_binding) is dict else None
        )
        verification_record = _require_campaign_verification_record(
            campaign_verification_record,
            campaign_manifest_sha256=width10_campaign_manifest.get(
                "manifest_sha256"
            ),
        )
        if not json_type_equal(verification_record, embedded_verification):
            raise ResumeStaticError(
                "caller campaign replay differs from embedded preparation replay"
            )
        replay_payload = verified_child_dimacs
        if replay_payload is None:
            replay_payload = nested.verified_child_dimacs_from_verification(
                width10_campaign_manifest,
                width6_campaign_manifest,
                parent_manifest,
                instance,
                verification_record=verification_record,
                global_leaf_index=global_leaf_index,
                parent_cube_index=parent_cube_index,
                strict_base=strict_base,
            )
        expected = build_resume_static_record(
            root=root,
            parent_manifest=parent_manifest,
            width6_campaign_manifest=width6_campaign_manifest,
            width10_campaign_manifest=width10_campaign_manifest,
            instance=instance,
            parent_cube_index=parent_cube_index,
            global_leaf_index=global_leaf_index,
            campaign_verification_record=verification_record,
            verified_child_dimacs=replay_payload,
            child_cnf_path=child_cnf_path,
            tool_paths=tool_paths,
            expected_tool_sha256=expected_tool_sha256,
            resource_caps=resource_caps,
            strict_base=strict_base,
        )
    except (
        ResumeStaticError, nested.NestedWidth10CampaignError,
        nested.width6.WidenedParentCampaignError,
        nested.hierarchy.HierarchicalCubeError, nested.cube16.Cube16Error,
        IndexError, KeyError, OSError, TypeError, ValueError,
    ) as exc:
        failures.append(f"fresh canonical replay failed: {exc}")
    if expected is not None and not json_type_equal(raw, expected):
        failures.append("static record is not exact fresh canonical replay")

    valid = not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-nested-width10-resume-static-verification-v1",
        "static_record_sha256": raw.get("record_sha256"),
        "expected_record_sha256": (
            expected.get("record_sha256") if expected is not None else None
        ),
        "root": str(root),
        "parent_cube_index": parent_cube_index,
        "global_leaf_index": global_leaf_index,
        "strict_base": strict_base,
        "valid": valid,
        "binding_failures": failures,
        "resume": bool(valid and raw.get("resume_policy", {}).get("resume") is True),
        "authority": raw.get("authority"),
        "production_eligible": False,
        "solver_invoked": False,
        "checkpoint_invoked": False,
        "proof_checker_invoked": False,
        "publication_certificate": False,
        "upload_authorized": False,
    })


def require_resume_static_record(*args: Any, **kwargs: Any) -> dict[str, Any]:
    report = verify_resume_static_record(*args, **kwargs)
    if report.get("valid") is not True:
        raise ResumeStaticError(
            f"width-ten static record rejected: {report.get('binding_failures')}"
        )
    record = args[0] if args else kwargs.get("record")
    if type(record) is not dict:
        raise ResumeStaticError("validated record is not a plain object")
    return dict(record)


__all__ = [
    "AUTHORITY_PRODUCTION_CANDIDATE", "AUTHORITY_SYNTHETIC_TEST_ONLY",
    "CAP_INPUT_FIELDS", "EXECUTABLE_TOOL_ROLES", "EXPECTED_LEAF_COUNT",
    "EXPECTED_PARENT_CUBE_INDEX", "EXPECTED_SPLIT_WIDTH", "GATE", "KIND",
    "ResumeStaticError", "SCHEMA_VERSION", "STATE", "STATIC_FIELDS",
    "TOOL_ROLES", "build_resume_static_record", "canonical_bytes",
    "canonical_sha256", "json_type_equal", "normalize_resource_caps",
    "require_resume_static_record", "seal", "selfhash_valid",
    "verify_resume_static_record",
]
