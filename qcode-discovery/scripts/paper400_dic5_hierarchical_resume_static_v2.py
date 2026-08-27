#!/usr/bin/env python3
"""Fail-closed static schema for one resumable paper400 child cube.

This module is intentionally execution-free.  It neither starts CaDiCaL nor
invokes DMTCP or a proof checker.  Its only authority is to bind one exact
hierarchical child formula to a root, a pinned tool set, bounded checkpoint
resources, and the proof replay obligations that a later runner must satisfy.

The existing direct cube runner records ``resume=False``.  A record from this
new schema is therefore a separate ``PRODUCTION_CANDIDATE`` static root; it is
not an upgrade, reinterpretation, or continuation of an old v1 root.  DMTCP
remains an untrusted transport.  A checkpoint or an accumulated DRAT prefix is
never scientific evidence.  A terminal may be promoted only after a complete
DRAT check from the exact child CNF, DRAT-to-LRAT conversion, and a fresh LRAT
replay from that same CNF.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from pathlib import Path
from typing import Any, Mapping

from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy


PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 2
KIND = "paper400-dic5-hierarchical-resume-static-v2"
GATE = "paper400-dic5-hierarchical-resume-static-v2"
STATE = "RESUMABLE_STATIC_SEALED"
AUTHORITY_PRODUCTION_CANDIDATE = "PRODUCTION_CANDIDATE"
AUTHORITY_SYNTHETIC_TEST_ONLY = "SYNTHETIC_TEST_ONLY"

MAX_JSON_BYTES = 64 << 20
MAX_BOUND_FILE_BYTES = 1 << 40
MAX_PROOF_BYTES = 1 << 40
MAX_CHECKPOINT_IMAGE_BYTES = 1 << 40
MAX_IMAGES_PER_GENERATION = 64
MAX_GENERATIONS = 1 << 16
MAX_GENERATION_METADATA_BYTES = 64 << 20
MAX_TOTAL_RUNTIME_ARTIFACT_BYTES = 4 << 40

TOOL_ROLES = frozenset({
    "cadical_solver",
    "dmtcp_controller_source",
    "four_lane_coordinator_source",
    "dmtcp_launch",
    "dmtcp_command",
    "dmtcp_restart",
    "drat_checker",
    "drat_to_lrat",
    "lrat_checker",
})

EXECUTABLE_TOOL_ROLES = frozenset({
    "cadical_solver",
    "dmtcp_launch",
    "dmtcp_command",
    "dmtcp_restart",
    "drat_checker",
    "drat_to_lrat",
    "lrat_checker",
})

CAP_INPUT_FIELDS = frozenset({
    "proof_max_bytes",
    "checkpoint_image_max_bytes",
    "checkpoint_images_per_generation_max",
    "checkpoint_generation_max_count",
    "checkpoint_generation_metadata_max_bytes",
})

STATIC_FIELDS = frozenset({
    "schema_version",
    "kind",
    "gate",
    "state",
    "authority",
    "test_only",
    "production_eligible",
    "root",
    "root_identity",
    "parent_manifest",
    "refinement_manifest",
    "child",
    "cnf_artifact",
    "source_binding",
    "toolchain_binding",
    "resource_policy",
    "resume_policy",
    "fresh_replay_policy",
    "claim_scope",
    "publication_certificate",
    "upload_authorized",
    "record_sha256",
})


class ResumeStaticError(RuntimeError):
    """A static child, root, source, tool, or resource binding is invalid."""


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
        raise ResumeStaticError(f"value is not canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any]) -> dict[str, Any]:
    if type(value) is not dict:
        raise ResumeStaticError("sealed value must be a plain object")
    if "record_sha256" in value:
        raise ResumeStaticError("caller supplied reserved record_sha256")
    result = dict(value)
    result["record_sha256"] = canonical_sha256(result)
    return result


def selfhash_valid(value: Any) -> bool:
    if type(value) is not dict or not _is_sha256(value.get("record_sha256")):
        return False
    unsigned = dict(value)
    stored = unsigned.pop("record_sha256")
    try:
        return stored == canonical_sha256(unsigned)
    except ResumeStaticError:
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    """JSON equality which does not confuse bools with integers."""

    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            json_type_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(a, b) for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def _plain_absolute_directory(path: Path) -> Path:
    target = Path(path)
    if not target.is_absolute():
        raise ResumeStaticError("root must be an absolute path")
    try:
        info = target.lstat()
        resolved = target.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise ResumeStaticError(f"root cannot be resolved: {target}") from exc
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise ResumeStaticError("root must be a plain directory")
    if resolved != target:
        raise ResumeStaticError("root or one of its ancestors is an alias")
    return resolved


def _root_identity(root: Path) -> dict[str, Any]:
    target = _plain_absolute_directory(root)
    info = target.stat()
    return {
        "path": str(target),
        "device": int(info.st_dev),
        "inode": int(info.st_ino),
        "uid": int(info.st_uid),
        "mode": stat.S_IMODE(info.st_mode),
    }


def _stable_file_record(
    path: Path,
    *,
    role: str,
    expected_sha256: str | None = None,
    relative_to: Path | None = None,
    require_executable: bool = False,
    cap: int = MAX_BOUND_FILE_BYTES,
) -> tuple[dict[str, Any], bytes | None]:
    if type(role) is not str or not role:
        raise ResumeStaticError("file role must be a nonempty string")
    if type(cap) is not int or not 1 <= cap <= MAX_BOUND_FILE_BYTES:
        raise ResumeStaticError("file cap is invalid")
    if expected_sha256 is not None and not _is_sha256(expected_sha256):
        raise ResumeStaticError(f"invalid expected SHA-256 for {role}")

    candidate = Path(path)
    try:
        raw_info = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise ResumeStaticError(f"cannot resolve bound file for {role}") from exc
    if stat.S_ISLNK(raw_info.st_mode) or not stat.S_ISREG(raw_info.st_mode):
        raise ResumeStaticError(f"bound file is not plain for {role}")
    if require_executable and not (raw_info.st_mode & 0o111):
        raise ResumeStaticError(f"bound tool is not executable for {role}")

    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    descriptor = os.open(resolved, flags)
    retained: bytearray | None = bytearray() if relative_to is not None else None
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size > cap:
            raise ResumeStaticError(f"bound file exceeds cap for {role}")
        digest = hashlib.sha256()
        observed = 0
        while True:
            chunk = os.read(descriptor, 8 << 20)
            if not chunk:
                break
            observed += len(chunk)
            if observed > cap:
                raise ResumeStaticError(f"bound file exceeds cap for {role}")
            digest.update(chunk)
            if retained is not None:
                retained.extend(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_uid,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_uid,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or observed != before.st_size:
        raise ResumeStaticError(f"bound file changed while hashing for {role}")
    actual_sha256 = digest.hexdigest()
    if expected_sha256 is not None and actual_sha256 != expected_sha256:
        raise ResumeStaticError(f"bound file SHA-256 mismatch for {role}")

    record: dict[str, Any] = {
        "role": role,
        "bytes": observed,
        "sha256": actual_sha256,
        "executable": bool(before.st_mode & 0o111),
    }
    if relative_to is None:
        record["path"] = str(resolved)
    else:
        root = _plain_absolute_directory(relative_to)
        try:
            relative = resolved.relative_to(root)
        except ValueError as exc:
            raise ResumeStaticError(f"bound file escapes root for {role}") from exc
        cursor = root
        for component in relative.parts[:-1]:
            cursor = cursor / component
            component_info = cursor.lstat()
            if stat.S_ISLNK(component_info.st_mode) or not stat.S_ISDIR(
                component_info.st_mode
            ):
                raise ResumeStaticError(f"non-plain ancestor for {role}")
        record["relative_path"] = relative.as_posix()
        record["device"] = int(before.st_dev)
        record["inode"] = int(before.st_ino)
        record["uid"] = int(before.st_uid)
        record["mode"] = stat.S_IMODE(before.st_mode)
    return record, None if retained is None else bytes(retained)


def _manifest_binding(
    manifest: Mapping[str, Any], *, role: str, self_hash_field: str
) -> dict[str, Any]:
    if type(manifest) is not dict:
        raise ResumeStaticError(f"{role} manifest must be a plain object")
    self_hash = manifest.get(self_hash_field)
    if not _is_sha256(self_hash):
        raise ResumeStaticError(f"{role} manifest self hash is invalid")
    unsigned = dict(manifest)
    unsigned.pop(self_hash_field, None)
    if canonical_sha256(unsigned) != self_hash:
        raise ResumeStaticError(f"{role} manifest self hash mismatch")
    payload = canonical_bytes(manifest)
    if len(payload) > MAX_JSON_BYTES:
        raise ResumeStaticError(f"{role} manifest exceeds JSON cap")
    return {
        "role": role,
        "manifest_kind": manifest.get("manifest_kind"),
        "manifest_self_hash_field": self_hash_field,
        "manifest_self_sha256": self_hash,
        "canonical_json_bytes": len(payload),
        "canonical_json_sha256": hashlib.sha256(payload).hexdigest(),
        "test_only": manifest.get("test_only"),
    }


def normalize_resource_caps(caps: Mapping[str, Any]) -> dict[str, Any]:
    if type(caps) is not dict or set(caps) != CAP_INPUT_FIELDS:
        raise ResumeStaticError("resource cap field set mismatch")
    proof = caps["proof_max_bytes"]
    image = caps["checkpoint_image_max_bytes"]
    images_per_generation = caps["checkpoint_images_per_generation_max"]
    generations = caps["checkpoint_generation_max_count"]
    metadata = caps["checkpoint_generation_metadata_max_bytes"]
    integer_values = (proof, image, images_per_generation, generations, metadata)
    if any(type(value) is not int for value in integer_values):
        raise ResumeStaticError("resource caps must be strict integers")
    if not 1 <= proof <= MAX_PROOF_BYTES:
        raise ResumeStaticError("proof cap is outside policy")
    if not 1 <= image <= MAX_CHECKPOINT_IMAGE_BYTES:
        raise ResumeStaticError("checkpoint image cap is outside policy")
    if not 1 <= images_per_generation <= MAX_IMAGES_PER_GENERATION:
        raise ResumeStaticError("images-per-generation cap is outside policy")
    if not 1 <= generations <= MAX_GENERATIONS:
        raise ResumeStaticError("generation count cap is outside policy")
    if not 1 <= metadata <= MAX_GENERATION_METADATA_BYTES:
        raise ResumeStaticError("generation metadata cap is outside policy")

    image_budget = image * images_per_generation * generations
    metadata_budget = metadata * generations
    total = proof + image_budget + metadata_budget
    if total > MAX_TOTAL_RUNTIME_ARTIFACT_BYTES:
        raise ResumeStaticError("combined runtime artifact cap is outside policy")
    return {
        **dict(caps),
        "checkpoint_image_budget_max_bytes": image_budget,
        "checkpoint_metadata_budget_max_bytes": metadata_budget,
        "total_runtime_artifact_max_bytes": total,
        "caps_apply_per_child_root": True,
        "checkpoint_generations_may_not_accumulate_unbounded": True,
    }


def _internal_source_binding() -> dict[str, Any]:
    sources = {
        "resume_static_schema_source": Path(__file__).resolve(),
        "hierarchical_refiner_source": Path(hierarchy.__file__).resolve(),
        "parent_cover_source": Path(hierarchy.cube16.__file__).resolve(),
        "optimized_builder_source": Path(
            hierarchy.cube16.optimized.__file__
        ).resolve(),
    }
    records: dict[str, Any] = {}
    for role, path in sorted(sources.items()):
        record, _ = _stable_file_record(path, role=role)
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise ResumeStaticError(f"internal source escapes project: {role}") from exc
        record.pop("path")
        record["relative_path"] = relative
        records[role] = record
    return {
        "method": "fresh-current-source-sha256-replay-v2",
        "sources": records,
        "source_role_sequence_sha256": canonical_sha256(sorted(records)),
    }


def _toolchain_binding(
    tool_paths: Mapping[str, Path],
    expected_tool_sha256: Mapping[str, str],
) -> dict[str, Any]:
    if type(tool_paths) is not dict or set(tool_paths) != TOOL_ROLES:
        raise ResumeStaticError("tool path role set mismatch")
    if (
        type(expected_tool_sha256) is not dict
        or set(expected_tool_sha256) != TOOL_ROLES
    ):
        raise ResumeStaticError("expected tool SHA-256 role set mismatch")
    tools: dict[str, Any] = {}
    for role in sorted(TOOL_ROLES):
        expected = expected_tool_sha256[role]
        record, _ = _stable_file_record(
            Path(tool_paths[role]),
            role=role,
            expected_sha256=expected,
            require_executable=role in EXECUTABLE_TOOL_ROLES,
        )
        tools[role] = record
    return {
        "method": "caller-pinned-path-and-sha256-fresh-replay-v2",
        "tools": tools,
        "tool_role_sequence_sha256": canonical_sha256(sorted(tools)),
    }


def _authority(parent_manifest: Mapping[str, Any], refinement: Mapping[str, Any]) -> str:
    parent_test_only = parent_manifest.get("test_only")
    refinement_test_only = refinement.get("test_only")
    if type(parent_test_only) is not bool or type(refinement_test_only) is not bool:
        raise ResumeStaticError("manifest test-only flags must be strict booleans")
    if parent_test_only is not refinement_test_only:
        raise ResumeStaticError("parent/refinement test-only authority mismatch")
    return (
        AUTHORITY_SYNTHETIC_TEST_ONLY
        if parent_test_only
        else AUTHORITY_PRODUCTION_CANDIDATE
    )


def build_resume_static_record(
    *,
    root: Path,
    parent_manifest: Mapping[str, Any],
    refinement_manifest: Mapping[str, Any],
    instance: Any,
    parent_cube_index: int,
    child_index: int,
    split_width: int,
    child_cnf_path: Path,
    tool_paths: Mapping[str, Path],
    expected_tool_sha256: Mapping[str, str],
    resource_caps: Mapping[str, Any],
    strict_base: bool = True,
) -> dict[str, Any]:
    """Construct a deterministic static record after a complete child replay."""

    target = _plain_absolute_directory(Path(root))
    if type(strict_base) is not bool:
        raise ResumeStaticError("strict_base must be a strict boolean")
    if type(parent_cube_index) is not int or type(child_index) is not int:
        raise ResumeStaticError("parent and child indices must be integers")
    if type(split_width) is not int or split_width <= 0:
        raise ResumeStaticError("split width must be a positive integer")

    replay = hierarchy.verify_refinement_manifest(
        refinement_manifest,
        parent_manifest,
        instance,
        strict_base=strict_base,
        expected_parent_cube_index=parent_cube_index,
        expected_split_width=split_width,
    )
    if replay.get("valid") is not True:
        raise ResumeStaticError(
            f"hierarchical refinement fresh replay failed: "
            f"{replay.get('binding_failures')}"
        )
    if (
        replay.get("coverage_mutually_exclusive") is not True
        or replay.get("coverage_exhaustive") is not True
        or replay.get("quantum_code_changed") is not False
    ):
        raise ResumeStaticError("hierarchical refinement is not an exact cover")

    expected_cnf = hierarchy.verified_child_dimacs(
        refinement_manifest,
        parent_manifest,
        instance,
        child_index=child_index,
        strict_base=strict_base,
        expected_parent_cube_index=parent_cube_index,
        expected_split_width=split_width,
    )
    cnf_record, observed_cnf = _stable_file_record(
        Path(child_cnf_path),
        role="exact-hierarchical-child-cnf",
        relative_to=target,
        cap=max(len(expected_cnf), 1),
    )
    if observed_cnf != expected_cnf:
        raise ResumeStaticError("child CNF is not exact fresh replay bytes")

    children = refinement_manifest.get("children")
    if (
        type(children) is not list
        or not 0 <= child_index < len(children)
        or type(children[child_index]) is not dict
    ):
        raise ResumeStaticError("child index is outside refinement manifest")
    child = children[child_index]
    if child.get("child_index") != child_index:
        raise ResumeStaticError("child record index mismatch")

    authority = _authority(parent_manifest, refinement_manifest)
    if strict_base and authority != AUTHORITY_PRODUCTION_CANDIDATE:
        raise ResumeStaticError("strict production replay cannot use test-only manifests")
    if not strict_base and authority != AUTHORITY_SYNTHETIC_TEST_ONLY:
        raise ResumeStaticError("non-strict replay is allowed only for test fixtures")

    parent_binding = _manifest_binding(
        parent_manifest,
        role="paper400-root-cover",
        self_hash_field="manifest_sha256",
    )
    parent_cube = parent_manifest["cubes"][parent_cube_index]
    parent_binding.update({
        "parent_cube_index": parent_cube_index,
        "parent_cube_id": parent_cube.get("cube_id"),
        "parent_cube_sha256": parent_cube.get("cube_sha256"),
        "parent_cube_dimacs_sha256": parent_cube.get("cube_dimacs_sha256"),
    })
    refinement_binding = _manifest_binding(
        refinement_manifest,
        role="paper400-parent-local-refinement",
        self_hash_field="manifest_sha256",
    )
    refinement_binding.update({
        "parent_binding_sha256": refinement_manifest.get("parent", {}).get(
            "parent_binding_sha256"
        ),
        "split_width": split_width,
        "refinement_variables_dimacs": refinement_manifest.get(
            "refinement", {}
        ).get("variables_dimacs"),
        "coverage_mutually_exclusive": refinement_manifest.get(
            "coverage", {}
        ).get("mutually_exclusive"),
        "coverage_exhaustive": refinement_manifest.get("coverage", {}).get(
            "exhaustive"
        ),
    })
    child_binding = {
        key: child.get(key)
        for key in (
            "child_index",
            "child_id",
            "child_sha256",
            "parent_cube_index",
            "parent_cube_id",
            "parent_cube_sha256",
            "combined_unit_clauses_sha256",
            "child_cnf_sha256",
            "child_dimacs_sha256",
            "child_num_variables",
            "child_num_clauses",
            "child_dimacs_bytes",
        )
    }
    child_binding["child_record_canonical_sha256"] = canonical_sha256(child)

    caps = normalize_resource_caps(resource_caps)
    sources = _internal_source_binding()
    tools = _toolchain_binding(tool_paths, expected_tool_sha256)
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
        "root_identity": _root_identity(target),
        "parent_manifest": parent_binding,
        "refinement_manifest": refinement_binding,
        "child": child_binding,
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
            "old_nonresumable_v1_root_may_be_reinterpreted": False,
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
            "only_parent_and_refinement_units_added": True,
            "child_unsat_alone_proves_global_distance_lower_bound": False,
            "all_exact_cover_leaves_need_authenticated_terminals": True,
            "inherited_distance_lower_bound_target": refinement_manifest.get(
                "claim_preservation", {}
            ).get("inherited_all_root_unsat_distance_lower_bound"),
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })


def verify_resume_static_record(
    record: Mapping[str, Any],
    *,
    root: Path,
    parent_manifest: Mapping[str, Any],
    refinement_manifest: Mapping[str, Any],
    instance: Any,
    parent_cube_index: int,
    child_index: int,
    split_width: int,
    child_cnf_path: Path,
    tool_paths: Mapping[str, Path],
    expected_tool_sha256: Mapping[str, str],
    resource_caps: Mapping[str, Any],
    strict_base: bool = True,
) -> dict[str, Any]:
    """Freshly rebuild and exact-compare a resumable static candidate."""

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
        if strict_base
        else AUTHORITY_SYNTHETIC_TEST_ONLY
    )
    if raw.get("authority") != expected_authority:
        failures.append("static authority mismatch")
    if raw.get("production_eligible") is not False:
        failures.append("static candidate must not claim production eligibility")
    if raw.get("publication_certificate") is not False:
        failures.append("static candidate must not claim publication authority")
    if raw.get("upload_authorized") is not False:
        failures.append("static candidate must not authorize upload")
    if raw.get("root") != str(Path(root)):
        failures.append("static root does not match caller expectation")
    resume_policy = raw.get("resume_policy")
    if type(resume_policy) is not dict or resume_policy.get("resume") is not True:
        failures.append("static resume=True policy is missing")
    fresh_policy = raw.get("fresh_replay_policy")
    if (
        type(fresh_policy) is not dict
        or fresh_policy.get("complete_drat_from_exact_child_cnf_required") is not True
        or fresh_policy.get("fresh_lrat_replay_from_exact_child_cnf_required")
        is not True
        or fresh_policy.get("checkpoint_or_drat_prefix_is_terminal_evidence")
        is not False
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
        expected = build_resume_static_record(
            root=root,
            parent_manifest=parent_manifest,
            refinement_manifest=refinement_manifest,
            instance=instance,
            parent_cube_index=parent_cube_index,
            child_index=child_index,
            split_width=split_width,
            child_cnf_path=child_cnf_path,
            tool_paths=tool_paths,
            expected_tool_sha256=expected_tool_sha256,
            resource_caps=resource_caps,
            strict_base=strict_base,
        )
    except (
        ResumeStaticError, hierarchy.HierarchicalCubeError, IndexError,
        KeyError, OSError, TypeError, ValueError,
    ) as exc:
        failures.append(f"fresh canonical replay failed: {exc}")
    if expected is not None and not json_type_equal(raw, expected):
        failures.append("static record is not exact fresh canonical replay")

    valid = not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-hierarchical-resume-static-verification-v2",
        "static_record_sha256": raw.get("record_sha256"),
        "expected_record_sha256": (
            expected.get("record_sha256") if expected is not None else None
        ),
        "root": str(root),
        "parent_cube_index": parent_cube_index,
        "child_index": child_index,
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
    """Return a validated record or raise without granting solver authority."""

    report = verify_resume_static_record(*args, **kwargs)
    if report.get("valid") is not True:
        raise ResumeStaticError(
            f"resumable static record rejected: {report.get('binding_failures')}"
        )
    record = args[0] if args else kwargs.get("record")
    if type(record) is not dict:
        raise ResumeStaticError("validated record is not a plain object")
    return dict(record)


__all__ = [
    "AUTHORITY_PRODUCTION_CANDIDATE",
    "AUTHORITY_SYNTHETIC_TEST_ONLY",
    "CAP_INPUT_FIELDS",
    "EXECUTABLE_TOOL_ROLES",
    "GATE",
    "KIND",
    "ResumeStaticError",
    "SCHEMA_VERSION",
    "STATE",
    "STATIC_FIELDS",
    "TOOL_ROLES",
    "build_resume_static_record",
    "canonical_bytes",
    "canonical_sha256",
    "json_type_equal",
    "normalize_resource_caps",
    "require_resume_static_record",
    "seal",
    "selfhash_valid",
    "verify_resume_static_record",
]
