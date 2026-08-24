#!/usr/bin/env python3
"""Add-only proof-carrying runner for one paper400 Dic5 cube.

The runner binds one member of the audited 16-cube cover, executes the pinned
CaDiCaL 1.9.5 binary through the hardened v2 process layer, verifies binary
DRAT, converts it to LRAT, verifies LRAT, and performs a final fresh replay.
The final artifact proves only that one bound cube is UNSAT; it deliberately
does not make a global distance claim.  The separate cube16 proof aggregator
is the only component allowed to combine 16 such certificates into ``d>=20``.

Production roots are append-only and use terminal sinks::

    NEW -> STATIC_SEALED -> RAW_UNSAT -> DRAT_VERIFIED
        -> LRAT_VERIFIED -> PROOF_CARRYING_CUBE_UNSAT

    STATIC_SEALED -> VERIFIED_SAT_LOW_OPERATOR
    STATIC_SEALED -> UNRESOLVED

A claim is written with O_EXCL before each stateful stage.  A failed or
interrupted stage poisons that root; retry/resume on the same root is forbidden.
At supervisor import time this file and the reused v2 safety layer are
stdlib-only.  NumPy and the scientific builder are loaded only by isolated
short-lived helpers.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import importlib.util
import json
import math
import os
import signal
import stat
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


PROJECT = Path(__file__).resolve().parent.parent
RUNNER_RELATIVE_PATH = "scripts/run_paper400_dic5_cube16_standalone_proof_v1.py"
V2_RELATIVE_PATH = "scripts/run_paper400_dic5_w6_standalone_proof_v2.py"
CUBE_RELATIVE_PATH = "investigations/paper400_dic5_cube16.py"
AGGREGATE_RELATIVE_PATH = (
    "investigations/paper400_dic5_cube16_proof_aggregate_v1.py"
)
OPTIMIZED_RELATIVE_PATH = (
    "evaluation/paper400_dic5_optimized_cnf_final_v13.py"
)

EXPECTED_V2_SHA256 = (
    "1034c232eae3bd131e988771673e2c4890c869658c8b380d9703a99d154c99cb"
)
EXPECTED_CUBE_SHA256 = (
    "fb2495e1c7acbcd32e2fffc3d4126c48b9042ec1375913bb5e753beb22b4e3c5"
)
EXPECTED_AGGREGATE_SHA256 = (
    "56990cca72921e7b491d493ac28900e98d4aabdadf641c731f46417be6c5961e"
)
EXPECTED_OPTIMIZED_SHA256 = (
    "5f55709382a7f6d2087199440d9e53351114e0a32129eaabc584464409ce6ee2"
)


def _read_source_stable(path: Path, *, cap: int = 16 << 20) -> bytes:
    target = Path(path)
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    descriptor = os.open(target, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size > cap:
            raise RuntimeError("source is not a bounded regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(1 << 20, cap + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > cap:
                raise RuntimeError("source grew beyond the read cap")
        payload = b"".join(chunks)
        after = os.fstat(descriptor)
        identity_before = (
            before.st_dev, before.st_ino, before.st_mode, before.st_uid,
            before.st_size, before.st_mtime_ns, before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev, after.st_ino, after.st_mode, after.st_uid,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        )
        if identity_before != identity_after or total != before.st_size:
            raise RuntimeError("source changed while reading")
        return payload
    finally:
        os.close(descriptor)


def _load_v2() -> Any:
    path = PROJECT / V2_RELATIVE_PATH
    if path.is_symlink() or not path.is_file():
        raise RuntimeError("pinned v2 safety layer is not a regular file")
    payload = _read_source_stable(path)
    if hashlib.sha256(payload).hexdigest() != EXPECTED_V2_SHA256:
        raise RuntimeError("pinned v2 safety layer hash mismatch")
    spec = importlib.util.spec_from_file_location("_paper400_cube_v2_safety", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load pinned v2 safety layer")
    module = importlib.util.module_from_spec(spec)
    exec(compile(payload, str(path), "exec"), module.__dict__)
    if module.PROJECT != PROJECT:
        raise RuntimeError("v2 safety layer project mismatch")
    return module


v2 = _load_v2()

SCHEMA_VERSION = 1
GATE = "paper400-dic5-cube16-proof-carrying-v1"
AUTHORITY_PRODUCTION = "PRODUCTION"

STATE_STATIC = "STATIC_SEALED"
STATE_RAW_UNSAT = "RAW_UNSAT"
STATE_SAT = "VERIFIED_SAT_LOW_OPERATOR"
STATE_UNRESOLVED = "UNRESOLVED"
STATE_DRAT = "DRAT_VERIFIED"
STATE_LRAT = "LRAT_VERIFIED"
STATE_FINAL = "PROOF_CARRYING_CUBE_UNSAT"

CUBE_CERTIFICATE_KIND = "paper400-dic5-proof-carrying-cube-unsat-v1"
CUBE_VALIDATION_KIND = "paper400-dic5-cube-proof-root-validation-v1"

EXPECTED_NUM_VARIABLES = 2_955
EXPECTED_CUBE_NUM_CLAUSES = 12_026
EXPECTED_SOLVER_NAME = "cadical195"
EXPECTED_SOLVER_VERSION = "1.9.5"

# The pinned v2 safety layer permits proofs up to 1 TiB.  That upper bound is
# intentionally not the admission budget for this two-worker cube campaign:
# reserving it twice would require 2 TiB plus the 128 GiB safety margin and
# would reject the audited production filesystem before either worker starts.
# Keep the inherited process/filesystem hardening, but apply a campaign-local
# cap based on the 28 GiB monolithic 24-hour proof observed for this formula.
PROOF_MAX_BYTES = 192 << 30
LRAT_MAX_BYTES = 192 << 30

INITIAL_PARALLELISM = 2
PER_WORKER_PLANNING_RSS_BYTES = 1 << 30
TWO_WORKER_RAW_HEADROOM_BYTES = 2 * v2.RESOURCE_MIN_RAW_HEADROOM
TWO_WORKER_EFFECTIVE_HEADROOM_BYTES = 2 * v2.RESOURCE_MIN_EFFECTIVE_HEADROOM

STATIC_COVER = Path("static/cover-manifest.json")
STATIC_DIMACS = Path("static/cube.cnf")
STATIC_COMMIT = Path("state/00-static.json")
SOLVE_CLAIM = Path("state/10-solve.claim")
RAW_COMMIT = Path("state/11-raw.json")
VERIFY_CLAIM = Path("state/20-verify.claim")
DRAT_COMMIT = Path("state/21-drat.json")
LRAT_COMMIT = Path("state/22-lrat.json")
FINALIZE_CLAIM = Path("state/30-finalize.claim")
CERTIFICATE = Path("certificate.json")
FINAL_COMMIT = Path("COMMIT.json")
DRAT_ARTIFACT = Path("artifacts/cube.drat")
LRAT_ARTIFACT = Path("artifacts/cube.lrat")

STATIC_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", "root", "root_identity", "cube_index",
    "manifest_sha256", "cube", "cover_artifact", "dimacs_artifact",
    "source_binding", "toolchain_binding", "builder_process",
    "resource_policy", "state_machine", "publication_certificate",
    "upload_authorized", "record_sha256",
})

RAW_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", "root", "root_identity", "cube_index",
    "manifest_sha256", "static_predecessor_sha256", "claim",
    "claim_artifact", "resource_gate_before", "resource_snapshot_after",
    "oom_event_delta", "invocation", "process", "logs", "proof",
    "sat_replay_process", "sat_terminal", "sat_classification", "failures",
    "decision_complete", "strict_raw_unsat", "strict_verified_sat",
    "solver_invocations", "publication_certificate", "upload_authorized",
    "record_sha256",
})

DRAT_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "root", "cube_index",
    "manifest_sha256", "raw_predecessor_sha256", "claim", "claim_artifact",
    "resource_gate_before", "resource_snapshot_after", "oom_event_delta",
    "bound_drat", "checker", "logs", "verified",
    "publication_certificate", "upload_authorized", "record_sha256",
})

LRAT_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "root", "cube_index",
    "manifest_sha256", "drat_predecessor_sha256",
    "resource_gate_before_conversion", "resource_snapshot_after_conversion",
    "resource_snapshot_after_lrat", "oom_event_delta", "bound_drat",
    "conversion", "conversion_logs", "lrat_error", "lrat_artifact",
    "bound_lrat", "lrat_checker", "lrat_checker_logs", "verified",
    "publication_certificate", "upload_authorized", "record_sha256",
})

FINAL_FIELDS = frozenset({
    "schema_version", "kind", "gate", "state", "authority", "test_only",
    "production_eligible", "root", "cube_index", "manifest_sha256",
    "lrat_predecessor_sha256", "claim", "resource_gate_before",
    "resource_snapshot_after", "oom_event_delta", "fresh_replay",
    "certificate", "certificate_sha256", "global_distance_claim",
    "publication_certificate", "upload_authorized",
    "no_further_root_writes_after_this_commit", "record_sha256",
})

CHECKER_RESULT_FIELDS = frozenset({
    "schema_version", "kind", "role", "invocation", "process",
    "semantic_marker", "verified", "record_sha256",
})
CHECKER_INVOCATION_FIELDS = frozenset({
    "schema_version", "kind", "role", "actual_argv_sha256", "checker",
    "dynamic_runtime", "cube_dimacs", "proof_input", "output_role",
    "timeout_s", "environment", "record_sha256",
})
FRESH_REPLAY_FIELDS = frozenset({
    "schema_version", "kind", "cube_index", "manifest_sha256",
    "bound_drat", "bound_lrat", "drat_checker", "lrat_checker",
    "drat_stdout", "drat_stderr", "lrat_stdout", "lrat_stderr",
    "all_fresh_replay_passed", "solver_invoked", "record_sha256",
})
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
SAT_TERMINAL_FIELDS = frozenset({
    "schema_version", "evidence_kind", "manifest_sha256",
    "base_cnf_sha256", "cube_index", "cube_id", "cube_sha256",
    "cube_cnf_sha256", "solver", "invocation_sha256", "outcome",
    "status_name", "decision_complete", "clean_exit", "timed_out",
    "solver_invocations", "full_model", "operator", "objective",
    "logical_syndrome", "elapsed_s", "solver_time_s", "solver_stats",
    "durable_proof", "test_only", "result_sha256",
})
SAT_CLASSIFICATION_FIELDS = frozenset({
    "schema_version", "evidence_kind", "cube_index", "classification",
    "strict_verified_sat", "clean_current_source_unsat",
    "official_full_matrix_witness_verifier_invoked",
    "official_full_matrix_witness_failures", "binding_failures",
    "record_sha256",
})

_PRODUCTION_NONCE = object()
_TEST_NONCE = object()


class CubeProofRunnerError(RuntimeError):
    """A production binding, state, process, or proof invariant failed."""


def canonical_bytes(value: Any) -> bytes:
    return v2.canonical_bytes(value)


def canonical_sha256(value: Any) -> str:
    return v2.canonical_sha256(value)


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    return v2.seal(value, field)


def selfhash_valid(value: Any, field: str = "record_sha256") -> bool:
    return v2.selfhash_valid(value, field)


def _artifact_reference(record: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "role": record["role"],
        "relative_path": record["relative_path"],
        "file_sha256": record["file_sha256"],
        "bytes": record["bytes"],
    }


def two_worker_capacity_requirement(output_cap: int) -> dict[str, int]:
    """Return the shared admission budget for two concurrent output writers."""

    if type(output_cap) is not int or output_cap < 0:
        raise CubeProofRunnerError("output cap must be a nonnegative integer")
    return {
        "parallel_workers": INITIAL_PARALLELISM,
        "per_worker_output_cap_bytes": output_cap,
        "shared_output_cap_bytes": INITIAL_PARALLELISM * output_cap,
        "shared_disk_required_bytes": (
            INITIAL_PARALLELISM * output_cap + v2.DISK_RESERVE_MARGIN_BYTES
        ),
        "shared_raw_headroom_bytes": TWO_WORKER_RAW_HEADROOM_BYTES,
        "shared_effective_headroom_bytes": TWO_WORKER_EFFECTIVE_HEADROOM_BYTES,
    }


def _two_worker_resource_gate(root: Path, *, output_cap: int) -> dict[str, Any]:
    base_gate = v2._resource_gate(root, output_cap=output_cap)
    required = two_worker_capacity_requirement(output_cap)
    raw = base_gate.get("raw_headroom_bytes")
    effective = base_gate.get("effective_headroom_bytes")
    memory_unbounded = raw is None and effective is None
    shared_memory_safe = bool(
        memory_unbounded
        or type(raw) is int
        and type(effective) is int
        and raw >= required["shared_raw_headroom_bytes"]
        and effective >= required["shared_effective_headroom_bytes"]
    )
    shared_disk_safe = bool(
        base_gate.get("filesystem_bavail_bytes", -1)
        >= required["shared_disk_required_bytes"]
    )
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-two-worker-resource-gate-v1",
        "base_v2_gate": base_gate,
        "requirements": required,
        "shared_memory_safe": shared_memory_safe,
        "shared_disk_safe": shared_disk_safe,
        "distinct_single_cpu_affinity_required_by_coordinator": True,
        "global_slot_limit_required_by_coordinator": INITIAL_PARALLELISM,
        "passed": bool(shared_memory_safe and shared_disk_safe),
    })
    if result["passed"] is not True:
        raise CubeProofRunnerError(f"two-worker resource gate failed: {result}")
    return result


def _file_record(relative: str, expected_sha256: str | None) -> dict[str, Any]:
    path = PROJECT / relative
    try:
        payload = _read_source_stable(path)
    except (OSError, RuntimeError) as exc:
        raise CubeProofRunnerError(f"source is not stable/regular: {relative}") from exc
    actual = hashlib.sha256(payload).hexdigest()
    if expected_sha256 is not None and actual != expected_sha256:
        raise CubeProofRunnerError(f"source hash mismatch: {relative}")
    return {"relative_path": relative, "sha256": actual, "bytes": len(payload)}


def _source_binding() -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-proof-source-binding-v1",
        "project_realpath": str(PROJECT.resolve(strict=True)),
        "files": [
            _file_record(RUNNER_RELATIVE_PATH, None),
            _file_record(V2_RELATIVE_PATH, EXPECTED_V2_SHA256),
            _file_record(CUBE_RELATIVE_PATH, EXPECTED_CUBE_SHA256),
            _file_record(AGGREGATE_RELATIVE_PATH, EXPECTED_AGGREGATE_SHA256),
            _file_record(OPTIMIZED_RELATIVE_PATH, EXPECTED_OPTIMIZED_SHA256),
        ],
        "science_python": v2._python_binding(),
    })


def _toolchain_binding() -> dict[str, Any]:
    record = v2._toolchain_binding()
    if record.get("solver", {}).get("sha256") != v2.EXPECTED_SOLVER_SHA256:
        raise CubeProofRunnerError("v2 solver binding mismatch")
    if record.get("drat_trim", {}).get("sha256") != v2.EXPECTED_DRAT_TRIM_SHA256:
        raise CubeProofRunnerError("v2 DRAT checker binding mismatch")
    if record.get("lrat_check", {}).get("sha256") != v2.EXPECTED_LRAT_CHECK_SHA256:
        raise CubeProofRunnerError("v2 LRAT checker binding mismatch")
    return record


def _validate_two_worker_gate_record(value: Any, *, output_cap: int) -> bool:
    fields = {
        "schema_version", "kind", "base_v2_gate", "requirements",
        "shared_memory_safe", "shared_disk_safe",
        "distinct_single_cpu_affinity_required_by_coordinator",
        "global_slot_limit_required_by_coordinator", "passed", "record_sha256",
    }
    if (
        type(value) is not dict
        or set(value) != fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-cube16-two-worker-resource-gate-v1"
        or not v2._validate_resource_record(
            value.get("base_v2_gate"), required_cap=output_cap,
        )
    ):
        return False
    base = value["base_v2_gate"]
    required = two_worker_capacity_requirement(output_cap)
    raw = base.get("raw_headroom_bytes")
    effective = base.get("effective_headroom_bytes")
    expected_memory = bool(
        raw is None and effective is None
        or type(raw) is int
        and type(effective) is int
        and raw >= required["shared_raw_headroom_bytes"]
        and effective >= required["shared_effective_headroom_bytes"]
    )
    expected_disk = bool(
        base["filesystem_bavail_bytes"] >= required["shared_disk_required_bytes"]
    )
    return bool(
        v2.json_type_equal(value.get("requirements"), required)
        and value.get("shared_memory_safe") is expected_memory
        and value.get("shared_disk_safe") is expected_disk
        and value.get("distinct_single_cpu_affinity_required_by_coordinator") is True
        and type(value.get("global_slot_limit_required_by_coordinator")) is int
        and value["global_slot_limit_required_by_coordinator"] == INITIAL_PARALLELISM
        and value.get("passed") is (expected_memory and expected_disk)
        and value.get("passed") is True
    )


def _validate_hash_record(value: Any) -> bool:
    return bool(
        type(value) is dict
        and set(value) == {"bytes", "sha256"}
        and type(value.get("bytes")) is int
        and value["bytes"] >= 0
        and v2.is_sha256(value.get("sha256"))
    )


def _validate_solver_invocation_record(
    value: Any,
    *,
    process: Mapping[str, Any],
    target: Path,
    cube: Mapping[str, Any],
    source_tcb: Mapping[str, Any],
) -> bool:
    fields = {
        "schema_version", "kind", "argv_roles", "actual_argv_sha256",
        "solver", "dynamic_runtime", "cube_dimacs", "proof_format",
        "timeout_s", "workers", "resume", "proof_cap_bytes",
        "environment", "record_sha256",
    }
    expected_roles = [
        "sealed-loader", "--inhibit-cache", "--library-path",
        "private-runtime", "--argv0", EXPECTED_SOLVER_NAME,
        "sealed-cadical195", "-q", "-t", str(v2.SOLVER_TIMEOUT_S),
        "sealed-cube-dimacs", "private-binary-drat",
    ]
    if (
        type(value) is not dict
        or set(value) != fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-cube16-solver-invocation-v1"
        or not v2.json_type_equal(value.get("argv_roles"), expected_roles)
        or not v2._validate_memfd_record(
            value.get("solver"), source_path=v2.SOLVER_PATH,
            expected_sha256=v2.EXPECTED_SOLVER_SHA256,
            expected_bytes=v2.EXPECTED_SOLVER_BYTES, executable=True,
        )
        or not v2._validate_memfd_record(
            value.get("cube_dimacs"), source_path=target / STATIC_DIMACS,
            expected_sha256=cube.get("cube_dimacs_sha256"),
            expected_bytes=cube.get("cube_dimacs_bytes"), executable=False,
        )
        or not v2._validate_historical_dynamic_runtime(
            value.get("dynamic_runtime"), source_tcb=source_tcb,
        )
        or value.get("proof_format") != "binary-drat-default"
        or type(value.get("timeout_s")) is not int
        or value["timeout_s"] != v2.SOLVER_TIMEOUT_S
        or type(value.get("workers")) is not int
        or value["workers"] != 1
        or value.get("resume") is not False
        or type(value.get("proof_cap_bytes")) is not int
        or value["proof_cap_bytes"] != PROOF_MAX_BYTES
        or not v2.json_type_equal(value.get("environment"), v2._clean_env())
        or not v2._validate_process_record(process)
    ):
        return False
    argv = process.get("argv")
    if type(argv) is not list or len(argv) != 12:
        return False
    descriptors = [v2._proc_fd_number(argv[index]) for index in (0, 3, 6, 10, 11)]
    return bool(
        all(number is not None for number in descriptors)
        and len(set(descriptors)) == len(descriptors)
        and argv[1:3] == ["--inhibit-cache", "--library-path"]
        and argv[3] == value["dynamic_runtime"]["library_path"]
        and argv[4:10] == [
            "--argv0", EXPECTED_SOLVER_NAME, argv[6], "-q", "-t",
            str(v2.SOLVER_TIMEOUT_S),
        ]
        and value.get("actual_argv_sha256") == canonical_sha256(argv)
        and process.get("cwd") == str(target)
        and v2.json_type_equal(process.get("environment"), v2._clean_env())
        and process.get("timeout_s") == v2.SOLVER_TIMEOUT_S
        and process.get("stdout_cap_bytes") == v2.SOLVER_STDOUT_MAX_BYTES
        and process.get("stderr_cap_bytes") == v2.SOLVER_STDERR_MAX_BYTES
        and process.get("file_size_cap_bytes") == PROOF_MAX_BYTES
    )


def _validate_checker_result_record(
    value: Any,
    *,
    target: Path,
    cube: Mapping[str, Any],
    expected_role: str,
    expected_proof_record: Mapping[str, Any],
    proof_cap: int,
    marker: bytes,
    expected_output_role: str | None,
    source_tcb: Mapping[str, Any],
    stdout: bytes | None,
    stderr: bytes | None,
    stored_stdout: Mapping[str, Any] | None = None,
    stored_stderr: Mapping[str, Any] | None = None,
) -> bool:
    if expected_role in {"drat-verify", "drat-to-lrat", "final-drat-replay"}:
        checker_path = v2.DRAT_TRIM_PATH
        checker_sha256 = v2.EXPECTED_DRAT_TRIM_SHA256
        checker_bytes = v2.EXPECTED_DRAT_TRIM_BYTES
    elif expected_role in {"lrat-check", "final-lrat-replay"}:
        checker_path = v2.LRAT_CHECK_PATH
        checker_sha256 = v2.EXPECTED_LRAT_CHECK_SHA256
        checker_bytes = v2.EXPECTED_LRAT_CHECK_BYTES
    else:
        return False
    if (
        type(value) is not dict
        or set(value) != CHECKER_RESULT_FIELDS
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-cube16-checker-result-v1"
        or value.get("role") != expected_role
    ):
        return False
    invocation = value.get("invocation")
    if (
        type(invocation) is not dict
        or set(invocation) != CHECKER_INVOCATION_FIELDS
        or not selfhash_valid(invocation)
        or type(invocation.get("schema_version")) is not int
        or invocation["schema_version"] != SCHEMA_VERSION
        or invocation.get("kind") != "paper400-cube16-checker-invocation-v1"
        or invocation.get("role") != expected_role
        or not v2._validate_memfd_record(
            invocation.get("checker"), source_path=checker_path,
            expected_sha256=checker_sha256, expected_bytes=checker_bytes,
            executable=True,
        )
        or not v2._validate_memfd_record(
            invocation.get("cube_dimacs"), source_path=target / STATIC_DIMACS,
            expected_sha256=cube.get("cube_dimacs_sha256"),
            expected_bytes=cube.get("cube_dimacs_bytes"), executable=False,
        )
        or not v2.json_type_equal(
            invocation.get("proof_input"), _artifact_reference(expected_proof_record),
        )
        or not v2._validate_historical_dynamic_runtime(
            invocation.get("dynamic_runtime"), source_tcb=source_tcb,
        )
        or invocation.get("output_role") != expected_output_role
        or type(invocation.get("timeout_s")) is not int
        or invocation["timeout_s"] != v2.CHECKER_TIMEOUT_S
        or not v2.json_type_equal(invocation.get("environment"), v2._clean_env())
    ):
        return False
    process = value.get("process")
    if not v2._validate_process_record(process):
        return False
    argv = process["argv"]
    if expected_role in {"drat-verify", "final-drat-replay"}:
        expected_length, expected_tail, fd_positions = (
            11, ["-t", str(v2.CHECKER_TIMEOUT_S)], (0, 3, 6, 7, 8),
        )
    elif expected_role == "drat-to-lrat":
        expected_length, expected_tail, fd_positions = (
            13, ["-L", None, "-t", str(v2.CHECKER_TIMEOUT_S)],
            (0, 3, 6, 7, 8, 10),
        )
    else:
        expected_length, expected_tail, fd_positions = (9, [], (0, 3, 6, 7, 8))
    if type(argv) is not list or len(argv) != expected_length:
        return False
    descriptors = [v2._proc_fd_number(argv[index]) for index in fd_positions]
    if (
        any(number is None for number in descriptors)
        or len(set(descriptors)) != len(descriptors)
        or argv[1:3] != ["--inhibit-cache", "--library-path"]
        or argv[3] != invocation["dynamic_runtime"]["library_path"]
        or argv[4:6] != ["--argv0", expected_role]
    ):
        return False
    if expected_role == "drat-to-lrat":
        if argv[9] != expected_tail[0] or argv[11:] != expected_tail[2:]:
            return False
    elif argv[9:] != expected_tail:
        return False
    expected_cap = LRAT_MAX_BYTES if expected_output_role == "lrat" else proof_cap
    if (
        invocation.get("actual_argv_sha256") != canonical_sha256(argv)
        or process.get("cwd") != str(target)
        or not v2.json_type_equal(process.get("environment"), v2._clean_env())
        or process.get("timeout_s") != v2.CHECKER_TIMEOUT_S
        or process.get("stdout_cap_bytes") != v2.CHECKER_LOG_MAX_BYTES
        or process.get("stderr_cap_bytes") != v2.CHECKER_LOG_MAX_BYTES
        or process.get("file_size_cap_bytes") != expected_cap
        or value.get("semantic_marker") != marker.decode("ascii")
        or value.get("verified") is not True
        or not v2._process_clean(process, rc=0)
    ):
        return False
    if stdout is not None and stderr is not None:
        return bool(
            process.get("stdout") == v2._hash_record(stdout)
            and process.get("stderr") == v2._hash_record(stderr)
            and value.get("verified")
            is v2._checker_success(process, stdout, stderr, marker=marker)
        )
    return bool(
        _validate_hash_record(stored_stdout)
        and _validate_hash_record(stored_stderr)
        and process.get("stdout") == stored_stdout
        and process.get("stderr") == stored_stderr
        and stored_stderr == v2._hash_record(b"")
    )


def _validate_stored_fresh_replay(
    fresh: Any,
    *,
    target: Path,
    manifest: Mapping[str, Any],
    cube: Mapping[str, Any],
    drat_artifact: Mapping[str, Any],
    lrat_artifact: Mapping[str, Any],
    source_tcb: Mapping[str, Any],
) -> bool:
    if (
        type(fresh) is not dict
        or set(fresh) != FRESH_REPLAY_FIELDS
        or not selfhash_valid(fresh)
        or type(fresh.get("schema_version")) is not int
        or fresh["schema_version"] != SCHEMA_VERSION
        or fresh.get("kind") != "paper400-cube16-fresh-proof-replay-v1"
        or not v2.json_type_equal(fresh.get("cube_index"), cube.get("cube_index"))
        or fresh.get("manifest_sha256") != manifest.get("manifest_sha256")
        or not v2.json_type_equal(fresh.get("bound_drat"), drat_artifact)
        or not v2.json_type_equal(fresh.get("bound_lrat"), lrat_artifact)
        or fresh.get("all_fresh_replay_passed") is not True
        or fresh.get("solver_invoked") is not False
    ):
        return False
    return bool(
        _validate_checker_result_record(
            fresh.get("drat_checker"), target=target, cube=cube,
            expected_role="final-drat-replay",
            expected_proof_record=drat_artifact, proof_cap=PROOF_MAX_BYTES,
            marker=b"s VERIFIED", expected_output_role=None, source_tcb=source_tcb,
            stdout=None, stderr=None, stored_stdout=fresh.get("drat_stdout"),
            stored_stderr=fresh.get("drat_stderr"),
        )
        and _validate_checker_result_record(
            fresh.get("lrat_checker"), target=target, cube=cube,
            expected_role="final-lrat-replay",
            expected_proof_record=lrat_artifact, proof_cap=LRAT_MAX_BYTES,
            marker=b"c VERIFIED", expected_output_role=None, source_tcb=source_tcb,
            stdout=None, stderr=None, stored_stdout=fresh.get("lrat_stdout"),
            stored_stderr=fresh.get("lrat_stderr"),
        )
    )


def _validate_stored_sat_replay(
    *,
    terminal: Any,
    classification: Any,
    process: Any,
    solver_stdout: bytes,
    target: Path,
    manifest: Mapping[str, Any],
    cube: Mapping[str, Any],
) -> bool:
    if (
        type(terminal) is not dict
        or set(terminal) != SAT_TERMINAL_FIELDS
        or not selfhash_valid(terminal, "result_sha256")
        or type(terminal.get("schema_version")) is not int
        or terminal["schema_version"] != SCHEMA_VERSION
        or terminal.get("manifest_sha256") != manifest.get("manifest_sha256")
        or terminal.get("base_cnf_sha256") != manifest.get("base", {}).get("cnf_sha256")
        or not v2.json_type_equal(terminal.get("cube_index"), cube.get("cube_index"))
        or terminal.get("cube_id") != cube.get("cube_id")
        or terminal.get("cube_sha256") != cube.get("cube_sha256")
        or terminal.get("cube_cnf_sha256") != cube.get("cube_cnf_sha256")
        or not v2.json_type_equal(terminal.get("solver"), {
            "name": EXPECTED_SOLVER_NAME,
            "version": EXPECTED_SOLVER_VERSION,
            "executable_sha256": v2.EXPECTED_SOLVER_SHA256,
        })
        or terminal.get("invocation_sha256") != hashlib.sha256(solver_stdout).hexdigest()
        or terminal.get("outcome") != "sat"
        or terminal.get("status_name") != "SATISFIABLE"
        or terminal.get("decision_complete") is not True
        or terminal.get("clean_exit") is not True
        or terminal.get("timed_out") is not False
        or type(terminal.get("solver_invocations")) is not int
        or terminal["solver_invocations"] != 1
        or type(terminal.get("objective")) is not int
        or not 0 <= terminal["objective"] <= 18
        or not v2.json_type_equal(terminal.get("durable_proof"), {
            "format": "none", "sha256": None, "independently_verified": False,
        })
        or terminal.get("test_only") is not False
    ):
        return False
    if (
        type(classification) is not dict
        or set(classification) != SAT_CLASSIFICATION_FIELDS
        or not selfhash_valid(classification)
        or type(classification.get("schema_version")) is not int
        or classification["schema_version"] != SCHEMA_VERSION
        or not v2.json_type_equal(
            classification.get("cube_index"), cube.get("cube_index"),
        )
        or classification.get("classification") != "VERIFIED_SAT_LOW_OPERATOR"
        or classification.get("strict_verified_sat") is not True
        or classification.get("clean_current_source_unsat") is not False
        or classification.get("official_full_matrix_witness_verifier_invoked") is not True
        or not v2.json_type_equal(
            classification.get("official_full_matrix_witness_failures"), [],
        )
        or not v2.json_type_equal(classification.get("binding_failures"), [])
    ):
        return False
    replay = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-sat-replay-v1",
        "cube_index": cube["cube_index"],
        "solver_stdout_sha256": hashlib.sha256(solver_stdout).hexdigest(),
        "terminal": dict(terminal),
        "classification": dict(classification),
        "passed": True,
        "solver_invoked": False,
    })
    if not v2._validate_process_record(process):
        return False
    argv = process["argv"]
    return bool(
        type(argv) is list
        and len(argv) == 9
        and argv[:7] == [
            str(v2.SCIENCE_PYTHON), "-I", "-B",
            str((PROJECT / RUNNER_RELATIVE_PATH).resolve(strict=True)),
            "__sat_replay", "--cube-index", str(cube["cube_index"]),
        ]
        and argv[7] == "--model-fd"
        and v2._proc_fd_number(argv[8]) is not None
        and process.get("cwd") == str(PROJECT)
        and process.get("timeout_s") == v2.PREPARE_TIMEOUT_S
        and process.get("stdout_cap_bytes") == v2.CHECKER_LOG_MAX_BYTES
        and process.get("stderr_cap_bytes") == v2.CHECKER_LOG_MAX_BYTES
        and process.get("file_size_cap_bytes") == v2.CHECKER_LOG_MAX_BYTES
        and process.get("stdout") == v2._hash_record(canonical_bytes(replay) + b"\n")
        and process.get("stderr") == v2._hash_record(b"")
        and v2._process_clean(process, rc=0)
    )


def _direct_cli_context(
    action: str,
    root: Path | None,
    cube_index: int | None,
) -> dict[str, Any]:
    runner = (PROJECT / RUNNER_RELATIVE_PATH).resolve(strict=True)
    if action == "preflight":
        expected = [str(runner), action, "--cube-index", str(cube_index)]
    elif action == "prepare":
        expected = [
            str(runner), action, "--root", str(root),
            "--cube-index", str(cube_index),
        ]
    else:
        expected = [str(runner), action, "--root", str(root)]
    main_module = sys.modules.get("__main__")
    origin = getattr(main_module, "__file__", None)
    try:
        origin_real = None if type(origin) is not str else str(Path(origin).resolve(strict=True))
        argv0_real = str(Path(sys.argv[0]).resolve(strict=True)) if sys.argv else None
        python_real = str(Path(sys.executable).resolve(strict=True))
    except (OSError, RuntimeError):
        origin_real = argv0_real = python_real = None
    checks = {
        "module_is_main": __name__ == "__main__",
        "main_is_runner": origin_real == str(runner),
        "argv0_is_runner": argv0_real == str(runner),
        "argv_exact": list(sys.argv) == expected,
        "isolated": sys.flags.isolated == 1,
        "dont_write_bytecode": sys.flags.dont_write_bytecode == 1,
        "optimize_zero": sys.flags.optimize == 0,
        "science_python_path": sys.executable == str(v2.SCIENCE_PYTHON),
        "science_python_realpath": python_real == str(v2.EXPECTED_PYTHON_REALPATH),
        "runner_not_symlink": not (PROJECT / RUNNER_RELATIVE_PATH).is_symlink(),
    }
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-direct-cli-context-v1",
        "action": action,
        "runner_realpath": str(runner),
        "runner_sha256": v2.file_sha256(runner),
        "root": None if root is None else str(root),
        "cube_index": cube_index,
        "expected_argv": expected,
        "checks": checks,
        "passed": all(value is True for value in checks.values()),
    })


def _require_cli(
    action: str,
    root: Path | None,
    cube_index: int | None,
    nonce: object | None,
) -> dict[str, Any]:
    if nonce is not _PRODUCTION_NONCE:
        raise CubeProofRunnerError("production stage requires direct-CLI authority")
    context = _direct_cli_context(action, root, cube_index)
    if context["passed"] is not True:
        raise CubeProofRunnerError(f"direct CLI context failed: {context}")
    return context


def _cube_builder_helper(cube_index: int) -> int:
    if sys.flags.isolated != 1 or sys.flags.dont_write_bytecode != 1:
        raise CubeProofRunnerError("cube builder helper requires -I -B")
    if type(cube_index) is not int or not 0 <= cube_index < 16:
        raise CubeProofRunnerError("cube index out of range")
    sys.path.insert(0, str(PROJECT))
    from investigations import paper400_dic5_cube16 as cube16

    if v2.file_sha256(Path(cube16.__file__).resolve()) != EXPECTED_CUBE_SHA256:
        raise CubeProofRunnerError("cube16 helper source hash mismatch")
    instance = cube16.optimized.build_optimized_instance()
    manifest = cube16.build_coverage_manifest(instance, strict_base=True)
    cube = manifest["cubes"][cube_index]
    clauses = cube16._cube_clauses(instance, cube)
    dimacs = cube16._render_dimacs(
        num_variables=int(instance.cnf["num_variables"]), clauses=clauses,
    )
    if (
        len(clauses) != EXPECTED_CUBE_NUM_CLAUSES
        or len(dimacs) != cube["cube_dimacs_bytes"]
        or hashlib.sha256(dimacs).hexdigest() != cube["cube_dimacs_sha256"]
    ):
        raise CubeProofRunnerError("cube helper DIMACS replay mismatch")
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-fresh-builder-output-v1",
        "solver_invoked": False,
        "cube_index": cube_index,
        "manifest": manifest,
        "cube_dimacs_base64": base64.b64encode(dimacs).decode("ascii"),
    })
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


def _fresh_cube_material(cube_index: int) -> tuple[dict[str, Any], bytes, dict[str, Any]]:
    argv = [
        str(v2.SCIENCE_PYTHON), "-I", "-B",
        str((PROJECT / RUNNER_RELATIVE_PATH).resolve(strict=True)),
        "__build", "--cube-index", str(cube_index),
    ]
    process, stdout, stderr = v2._run_capped_process(
        argv,
        timeout_s=v2.PREPARE_TIMEOUT_S,
        stdout_cap=v2.PREPARE_LOG_MAX_BYTES,
        stderr_cap=v2.CHECKER_LOG_MAX_BYTES,
        cwd=PROJECT,
        file_size_cap=v2.PREPARE_LOG_MAX_BYTES,
    )
    if not v2._process_clean(process, rc=0) or stderr != b"":
        raise CubeProofRunnerError("isolated cube builder failed")
    value = v2._decode_json(stdout, canonical=True)
    expected_fields = {
        "schema_version", "kind", "solver_invoked", "cube_index", "manifest",
        "cube_dimacs_base64", "record_sha256",
    }
    if (
        set(value) != expected_fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != "paper400-cube16-fresh-builder-output-v1"
        or value.get("solver_invoked") is not False
        or value.get("cube_index") != cube_index
    ):
        raise CubeProofRunnerError("cube builder schema/self-hash mismatch")
    try:
        dimacs = base64.b64decode(value["cube_dimacs_base64"], validate=True)
    except (TypeError, ValueError) as exc:
        raise CubeProofRunnerError("cube builder DIMACS encoding invalid") from exc
    manifest = value.get("manifest")
    if type(manifest) is not dict or len(manifest.get("cubes", [])) != 16:
        raise CubeProofRunnerError("cube builder manifest malformed")
    cube = manifest["cubes"][cube_index]
    if (
        manifest.get("test_only") is not False
        or manifest.get("base", {}).get("cnf_sha256") != v2.EXPECTED_BASE_CNF_SHA256
        or cube.get("cube_num_variables") != EXPECTED_NUM_VARIABLES
        or cube.get("cube_num_clauses") != EXPECTED_CUBE_NUM_CLAUSES
        or len(dimacs) != cube.get("cube_dimacs_bytes")
        or hashlib.sha256(dimacs).hexdigest() != cube.get("cube_dimacs_sha256")
    ):
        raise CubeProofRunnerError("fresh cube material binding mismatch")
    return manifest, dimacs, process


def _cube_sat_helper(cube_index: int, model_fd: int) -> int:
    if sys.flags.isolated != 1 or sys.flags.dont_write_bytecode != 1:
        raise CubeProofRunnerError("SAT helper requires -I -B")
    duplicate = os.dup(model_fd)
    try:
        payload = v2._read_fd_stable(duplicate, cap=v2.SOLVER_STDOUT_MAX_BYTES)
    finally:
        os.close(duplicate)
    sys.path.insert(0, str(PROJECT))
    from investigations import paper400_dic5_cube16 as cube16

    instance = cube16.optimized.build_optimized_instance()
    manifest = cube16.build_coverage_manifest(instance, strict_base=True)
    bits = v2._parse_complete_model(payload, num_variables=EXPECTED_NUM_VARIABLES)
    import numpy as np

    terminal = cube16.build_cube_terminal(
        manifest,
        instance,
        cube_index=cube_index,
        outcome="sat",
        full_model=np.asarray(bits, dtype=np.uint8),
        solver={
            "name": EXPECTED_SOLVER_NAME,
            "version": EXPECTED_SOLVER_VERSION,
            "executable_sha256": v2.EXPECTED_SOLVER_SHA256,
        },
        invocation_sha256=hashlib.sha256(payload).hexdigest(),
        elapsed_s=0.0,
        solver_time_s=0.0,
        solver_stats={},
    )
    classification = cube16.classify_cube_terminal(
        terminal, manifest, instance,
    )
    if classification.get("strict_verified_sat") is not True:
        raise CubeProofRunnerError("SAT helper rejected complete cube model")
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-sat-replay-v1",
        "cube_index": cube_index,
        "solver_stdout_sha256": hashlib.sha256(payload).hexdigest(),
        "terminal": terminal,
        "classification": classification,
        "passed": True,
        "solver_invoked": False,
    })
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


def _run_sat_replay(
    cube_index: int, stdout: bytes,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    model_fd, _ = v2._sealed_memfd_from_bytes("qcode-cube-sat-model", stdout)
    try:
        argv = [
            str(v2.SCIENCE_PYTHON), "-I", "-B",
            str((PROJECT / RUNNER_RELATIVE_PATH).resolve(strict=True)),
            "__sat_replay", "--cube-index", str(cube_index),
            "--model-fd", str(model_fd),
        ]
        process, child_stdout, child_stderr = v2._run_capped_process(
            argv,
            timeout_s=v2.PREPARE_TIMEOUT_S,
            stdout_cap=v2.CHECKER_LOG_MAX_BYTES,
            stderr_cap=v2.CHECKER_LOG_MAX_BYTES,
            cwd=PROJECT,
            pass_fds=(model_fd,),
            file_size_cap=v2.CHECKER_LOG_MAX_BYTES,
        )
    finally:
        os.close(model_fd)
    if not v2._process_clean(process, rc=0) or child_stderr != b"":
        return process, None
    try:
        replay = v2._decode_json(child_stdout, canonical=True)
    except v2.ProofRunnerError:
        return process, None
    if (
        not selfhash_valid(replay)
        or replay.get("kind") != "paper400-cube16-sat-replay-v1"
        or replay.get("cube_index") != cube_index
        or replay.get("solver_stdout_sha256") != hashlib.sha256(stdout).hexdigest()
        or replay.get("passed") is not True
        or replay.get("solver_invoked") is not False
        or replay.get("classification", {}).get("strict_verified_sat") is not True
    ):
        return process, None
    return process, replay


def preflight_only(
    cube_index: int, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    context = _require_cli("preflight", None, cube_index, _production_nonce)
    manifest, dimacs, process = _fresh_cube_material(cube_index)
    source = _source_binding()
    tools = _toolchain_binding()
    cube = manifest["cubes"][cube_index]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-proof-preflight-v1",
        "gate": GATE,
        "direct_cli_context": context,
        "manifest_sha256": manifest["manifest_sha256"],
        "cube_index": cube_index,
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": hashlib.sha256(dimacs).hexdigest(),
        "cube_dimacs_bytes": len(dimacs),
        "builder_process": process,
        "source_binding": source,
        "toolchain_binding": tools,
        "solver_invoked": False,
        "proof_checker_invoked": False,
        "root_created": False,
        "publication_certificate": False,
        "upload_authorized": False,
    })


def _static_value(
    root: Path,
    cube_index: int,
    manifest: Mapping[str, Any],
    cover_record: Mapping[str, Any],
    dimacs_record: Mapping[str, Any],
    source: Mapping[str, Any],
    tools: Mapping[str, Any],
    builder_process: Mapping[str, Any],
) -> dict[str, Any]:
    cube = manifest["cubes"][cube_index]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-static-commit-v1",
        "gate": GATE,
        "state": STATE_STATIC,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": True,
        "root": str(root),
        "root_identity": v2._root_identity(root),
        "cube_index": cube_index,
        "manifest_sha256": manifest["manifest_sha256"],
        "cube": {
            key: cube[key] for key in (
                "cube_index", "cube_id", "cube_sha256", "cube_cnf_sha256",
                "cube_dimacs_sha256", "cube_num_variables",
                "cube_num_clauses", "cube_dimacs_bytes", "unit_clauses",
            )
        },
        "cover_artifact": dict(cover_record),
        "dimacs_artifact": dict(dimacs_record),
        "source_binding": dict(source),
        "toolchain_binding": dict(tools),
        "builder_process": dict(builder_process),
        "resource_policy": {
            "solver_timeout_s": v2.SOLVER_TIMEOUT_S,
            "checker_timeout_s": v2.CHECKER_TIMEOUT_S,
            "proof_max_bytes": PROOF_MAX_BYTES,
            "lrat_max_bytes": LRAT_MAX_BYTES,
            "disk_reserve_margin_bytes": v2.DISK_RESERVE_MARGIN_BYTES,
            "initial_parallelism": INITIAL_PARALLELISM,
            "two_worker_solve": two_worker_capacity_requirement(PROOF_MAX_BYTES),
            "two_worker_lrat": two_worker_capacity_requirement(LRAT_MAX_BYTES),
            "planning_rss_per_worker_bytes": PER_WORKER_PLANNING_RSS_BYTES,
            "planning_rss_is_proof": False,
            "fresh_gate_before_solver": True,
            "fresh_gate_before_lrat": True,
        },
        "state_machine": {
            "resume": False,
            "retry_same_root": False,
            "workers_per_solver": 1,
            "cube_unsat_is_global_lower_bound": False,
            "final_requires_fresh_drat_and_lrat_replay": True,
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })


def prepare_root(
    root: Path,
    cube_index: int,
    *,
    _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=False)
    _require_cli("prepare", target, cube_index, _production_nonce)
    manifest, dimacs, builder_process = _fresh_cube_material(cube_index)
    source = _source_binding()
    tools = _toolchain_binding()
    v2._mkdir_root(target)
    for name in ("static", "state", "artifacts", "logs"):
        v2._mkdir_new(target, name)
    v2._atomic_publish_bytes(
        target / "static", STATIC_COVER.name, canonical_bytes(manifest) + b"\n",
    )
    v2._atomic_publish_bytes(target / "static", STATIC_DIMACS.name, dimacs)
    cover_record = v2._physical_record(
        target / STATIC_COVER, target, "cube16-cover-manifest",
        cap=v2.JSON_MAX_BYTES,
    )
    dimacs_record = v2._physical_record(
        target / STATIC_DIMACS, target, "bound-cube-dimacs",
        cap=max(len(dimacs), 1),
    )
    commit = _static_value(
        target, cube_index, manifest, cover_record, dimacs_record,
        source, tools, builder_process,
    )
    v2._atomic_publish_json(target / "state", STATIC_COMMIT.name, commit)
    replay = _validate_static(target, fresh_source_and_tools=True)
    if not v2.json_type_equal(replay["static"], commit):
        raise CubeProofRunnerError("post-commit static replay mismatch")
    return commit


def _validate_static(root: Path, *, fresh_source_and_tools: bool) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    static_record = v2._strict_json(target / STATIC_COMMIT)
    if (
        set(static_record) != STATIC_FIELDS
        or not selfhash_valid(static_record)
        or type(static_record.get("schema_version")) is not int
        or static_record.get("schema_version") != SCHEMA_VERSION
        or static_record.get("kind") != "paper400-cube16-static-commit-v1"
        or static_record.get("gate") != GATE
        or static_record.get("state") != STATE_STATIC
        or static_record.get("authority") != AUTHORITY_PRODUCTION
        or static_record.get("test_only") is not False
        or static_record.get("production_eligible") is not True
        or static_record.get("root") != str(target)
        or not v2.json_type_equal(static_record.get("root_identity"), v2._root_identity(target))
        or static_record.get("publication_certificate") is not False
        or static_record.get("upload_authorized") is not False
    ):
        raise CubeProofRunnerError("static commit schema/authority mismatch")
    cube_index = static_record.get("cube_index")
    if type(cube_index) is not int or not 0 <= cube_index < 16:
        raise CubeProofRunnerError("static cube index invalid")
    manifest = v2._strict_json(target / STATIC_COVER)
    cube = manifest.get("cubes", [])[cube_index]
    dimacs = v2._read_file_stable(
        target / STATIC_DIMACS, cap=max(int(cube.get("cube_dimacs_bytes", 0)), 1),
    )
    cover_record = v2._physical_record(
        target / STATIC_COVER, target, "cube16-cover-manifest",
        cap=v2.JSON_MAX_BYTES,
    )
    dimacs_record = v2._physical_record(
        target / STATIC_DIMACS, target, "bound-cube-dimacs",
        cap=max(len(dimacs), 1),
    )
    if (
        manifest.get("manifest_sha256") != static_record.get("manifest_sha256")
        or not v2.json_type_equal(static_record.get("cube"), {
            key: cube[key] for key in (
                "cube_index", "cube_id", "cube_sha256", "cube_cnf_sha256",
                "cube_dimacs_sha256", "cube_num_variables", "cube_num_clauses",
                "cube_dimacs_bytes", "unit_clauses",
            )
        })
        or hashlib.sha256(dimacs).hexdigest() != cube.get("cube_dimacs_sha256")
        or len(dimacs) != cube.get("cube_dimacs_bytes")
        or not v2.json_type_equal(static_record.get("cover_artifact"), cover_record)
        or not v2.json_type_equal(static_record.get("dimacs_artifact"), dimacs_record)
    ):
        raise CubeProofRunnerError("static cube artifact binding mismatch")
    if fresh_source_and_tools:
        fresh_manifest, fresh_dimacs, builder_process = _fresh_cube_material(cube_index)
        source = _source_binding()
        tools = _toolchain_binding()
        if (
            not v2.json_type_equal(fresh_manifest, manifest)
            or fresh_dimacs != dimacs
            or not v2.json_type_equal(source, static_record.get("source_binding"))
            or not v2.json_type_equal(tools, static_record.get("toolchain_binding"))
        ):
            raise CubeProofRunnerError("fresh static source/tool/cube replay mismatch")
        expected = _static_value(
            target, cube_index, manifest, cover_record, dimacs_record,
            source, tools, static_record["builder_process"],
        )
        if not v2.json_type_equal(expected, static_record):
            raise CubeProofRunnerError("static canonical reconstruction mismatch")
    return {
        "static": static_record,
        "manifest": manifest,
        "cube": cube,
        "dimacs": dimacs,
    }


def _solver_invocation(
    argv: Sequence[str],
    solver: Mapping[str, Any],
    runtime: Mapping[str, Any],
    cube_memfd: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-solver-invocation-v1",
        "argv_roles": [
            "sealed-loader", "--inhibit-cache", "--library-path",
            "private-runtime", "--argv0", EXPECTED_SOLVER_NAME,
            "sealed-cadical195", "-q", "-t", str(v2.SOLVER_TIMEOUT_S),
            "sealed-cube-dimacs", "private-binary-drat",
        ],
        "actual_argv_sha256": canonical_sha256(list(argv)),
        "solver": dict(solver),
        "dynamic_runtime": dict(runtime),
        "cube_dimacs": dict(cube_memfd),
        "proof_format": "binary-drat-default",
        "timeout_s": v2.SOLVER_TIMEOUT_S,
        "workers": 1,
        "resume": False,
        "proof_cap_bytes": PROOF_MAX_BYTES,
        "environment": v2._clean_env(),
    })


def solve_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    _require_cli("solve", target, None, _production_nonce)
    static = _validate_static(target, fresh_source_and_tools=True)
    if (target / SOLVE_CLAIM).exists() or (target / RAW_COMMIT).exists():
        raise CubeProofRunnerError("solve stage already claimed or committed")
    gate = _two_worker_resource_gate(target, output_cap=PROOF_MAX_BYTES)
    root_before = v2._root_identity(target)
    claim = v2._create_claim(target, SOLVE_CLAIM, "cube-solve")
    claim_record = v2._physical_record(
        target / SOLVE_CLAIM, target, "cube-solve-claim", cap=v2.JSON_MAX_BYTES,
    )
    proof_fd, private_name = v2._create_private_output(
        target / "artifacts", DRAT_ARTIFACT.name,
    )
    solver_fd = cube_fd = -1
    runtime_handle: dict[str, Any] | None = None
    process: dict[str, Any]
    stdout = stderr = b""
    invocation: dict[str, Any]
    try:
        solver_fd, solver_record = v2._seal_memfd_from_path(
            v2.SOLVER_PATH,
            expected_sha256=v2.EXPECTED_SOLVER_SHA256,
            expected_bytes=v2.EXPECTED_SOLVER_BYTES,
            executable=True,
        )
        cube_fd, cube_record = v2._seal_memfd_from_path(
            target / STATIC_DIMACS,
            expected_sha256=static["cube"]["cube_dimacs_sha256"],
            expected_bytes=static["cube"]["cube_dimacs_bytes"],
            executable=False,
        )
        runtime_handle = v2._stage_dynamic_runtime()
        runtime = runtime_handle["record"]
        loader_fd = runtime_handle["loader_fd"]
        runtime_dir_fd = runtime_handle["directory_fd"]
        argv = [
            f"/proc/self/fd/{loader_fd}", "--inhibit-cache",
            "--library-path", runtime["library_path"],
            "--argv0", EXPECTED_SOLVER_NAME, f"/proc/self/fd/{solver_fd}",
            "-q", "-t", str(v2.SOLVER_TIMEOUT_S),
            f"/proc/self/fd/{cube_fd}", f"/proc/self/fd/{proof_fd}",
        ]
        invocation = _solver_invocation(argv, solver_record, runtime, cube_record)
        process, stdout, stderr = v2._run_capped_process(
            argv,
            timeout_s=v2.SOLVER_TIMEOUT_S,
            stdout_cap=v2.SOLVER_STDOUT_MAX_BYTES,
            stderr_cap=v2.SOLVER_STDERR_MAX_BYTES,
            cwd=target,
            pass_fds=(loader_fd, runtime_dir_fd, solver_fd, cube_fd, proof_fd),
            file_size_cap=PROOF_MAX_BYTES,
            watched_fds=((proof_fd, PROOF_MAX_BYTES),),
        )
        v2._validate_staged_dynamic_runtime(runtime_handle)
    finally:
        if solver_fd >= 0:
            os.close(solver_fd)
        if cube_fd >= 0:
            os.close(cube_fd)
        if runtime_handle is not None:
            v2._destroy_dynamic_runtime(runtime_handle)
    proof_sha: str | None = None
    proof_bytes: int | None = None
    proof_error: str | None = None
    try:
        os.fsync(proof_fd)
        proof_sha, proof_bytes, _ = v2._hash_fd_stable(
            proof_fd, cap=PROOF_MAX_BYTES,
        )
    except (OSError, v2.ProofRunnerError) as exc:
        proof_error = f"{type(exc).__name__}: {exc}"
    snapshot = v2._instant_resource(target)
    oom_delta = v2._oom_delta(gate["base_v2_gate"], snapshot)
    no_oom = all(value == 0 for value in oom_delta.values())
    if not v2.json_type_equal(root_before, v2._root_identity(target)):
        v2._discard_private(target / "artifacts", private_name, proof_fd)
        raise CubeProofRunnerError("root identity changed during cube solve")
    v2._atomic_publish_bytes(target / "logs", "solver.stdout", stdout)
    v2._atomic_publish_bytes(target / "logs", "solver.stderr", stderr)
    logs = [
        v2._physical_record(
            target / "logs/solver.stdout", target, "solver-stdout",
            cap=v2.SOLVER_STDOUT_MAX_BYTES,
        ),
        v2._physical_record(
            target / "logs/solver.stderr", target, "solver-stderr",
            cap=v2.SOLVER_STDERR_MAX_BYTES,
        ),
    ]
    valid_unsat = bool(
        v2._solver_semantics(process, stdout, stderr, expected="UNSATISFIABLE")
        and no_oom and proof_error is None and type(proof_sha) is str
        and type(proof_bytes) is int and 0 < proof_bytes <= PROOF_MAX_BYTES
    )
    valid_sat_process = bool(
        v2._solver_semantics(process, stdout, stderr, expected="SATISFIABLE")
        and no_oom
    )
    proof_record: dict[str, Any] | None = None
    sat_process: dict[str, Any] | None = None
    sat_replay: dict[str, Any] | None = None
    failures: list[str] = []
    if valid_unsat:
        assert proof_sha is not None and proof_bytes is not None
        v2._publish_private_output(
            target / "artifacts", private_name, proof_fd, DRAT_ARTIFACT.name,
            expected_sha256=proof_sha, expected_bytes=proof_bytes,
        )
        proof_fd = -1
        proof_record = v2._physical_record(
            target / DRAT_ARTIFACT, target, "raw-binary-drat",
            cap=PROOF_MAX_BYTES,
        )
        state = STATE_RAW_UNSAT
    else:
        v2._discard_private(target / "artifacts", private_name, proof_fd)
        proof_fd = -1
        if valid_sat_process:
            sat_process, sat_replay = _run_sat_replay(
                static["cube"]["cube_index"], stdout,
            )
        if sat_replay is not None:
            state = STATE_SAT
        else:
            state = STATE_UNRESOLVED
            failures.append(proof_error or "solver did not yield strict UNSAT or verified SAT")
    raw = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-raw-result-v1",
        "gate": GATE,
        "state": state,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": state in {STATE_RAW_UNSAT, STATE_SAT},
        "root": str(target),
        "root_identity": root_before,
        "cube_index": static["cube"]["cube_index"],
        "manifest_sha256": static["manifest"]["manifest_sha256"],
        "static_predecessor_sha256": static["static"]["record_sha256"],
        "claim": claim,
        "claim_artifact": claim_record,
        "resource_gate_before": gate,
        "resource_snapshot_after": snapshot,
        "oom_event_delta": oom_delta,
        "invocation": invocation,
        "process": process,
        "logs": logs,
        "proof": proof_record,
        "sat_replay_process": sat_process,
        "sat_terminal": None if sat_replay is None else sat_replay["terminal"],
        "sat_classification": None if sat_replay is None else sat_replay["classification"],
        "failures": failures,
        "decision_complete": state in {STATE_RAW_UNSAT, STATE_SAT},
        "strict_raw_unsat": state == STATE_RAW_UNSAT,
        "strict_verified_sat": state == STATE_SAT,
        "solver_invocations": 1,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    v2._atomic_publish_json(target / "state", RAW_COMMIT.name, raw)
    replay = _validate_raw(target, fresh_source_and_tools=True)
    if not v2.json_type_equal(replay["raw"], raw):
        raise CubeProofRunnerError("post-commit RAW replay mismatch")
    return raw


def _validate_raw(root: Path, *, fresh_source_and_tools: bool) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    static = _validate_static(target, fresh_source_and_tools=fresh_source_and_tools)
    raw = v2._strict_json(target / RAW_COMMIT)
    if (
        set(raw) != RAW_FIELDS or not selfhash_valid(raw)
        or type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
        or raw.get("kind") != "paper400-cube16-raw-result-v1"
        or raw.get("gate") != GATE
        or raw.get("state") not in {STATE_RAW_UNSAT, STATE_SAT, STATE_UNRESOLVED}
        or raw.get("authority") != AUTHORITY_PRODUCTION
        or raw.get("test_only") is not False
        or raw.get("root") != str(target)
        or not v2.json_type_equal(raw.get("root_identity"), v2._root_identity(target))
        or not v2.json_type_equal(raw.get("cube_index"), static["cube"]["cube_index"])
        or raw.get("manifest_sha256") != static["manifest"]["manifest_sha256"]
        or raw.get("static_predecessor_sha256") != static["static"]["record_sha256"]
        or raw.get("solver_invocations") != 1
        or raw.get("publication_certificate") is not False
        or raw.get("upload_authorized") is not False
        or not v2._validate_process_record(raw.get("process"))
    ):
        raise CubeProofRunnerError("RAW schema/common binding mismatch")
    stdout = v2._read_file_stable(
        target / "logs/solver.stdout", cap=v2.SOLVER_STDOUT_MAX_BYTES,
    )
    stderr = v2._read_file_stable(
        target / "logs/solver.stderr", cap=v2.SOLVER_STDERR_MAX_BYTES,
    )
    expected_logs = [
        v2._physical_record(
            target / "logs/solver.stdout", target, "solver-stdout",
            cap=v2.SOLVER_STDOUT_MAX_BYTES,
        ),
        v2._physical_record(
            target / "logs/solver.stderr", target, "solver-stderr",
            cap=v2.SOLVER_STDERR_MAX_BYTES,
        ),
    ]
    if not v2.json_type_equal(raw.get("logs"), expected_logs):
        raise CubeProofRunnerError("RAW log binding mismatch")
    claim = v2._strict_json(target / SOLVE_CLAIM)
    try:
        v2._validate_claim_record(claim, action="cube-solve", target=target)
    except v2.ProofRunnerError as exc:
        raise CubeProofRunnerError("RAW solve claim invalid") from exc
    gate = raw.get("resource_gate_before")
    snapshot = raw.get("resource_snapshot_after")
    source_tcb = static["static"]["toolchain_binding"].get("dynamic_elf_tcb")
    if (
        not _validate_two_worker_gate_record(gate, output_cap=PROOF_MAX_BYTES)
        or not v2._validate_resource_snapshot(snapshot)
        or not v2.json_type_equal(
            raw.get("oom_event_delta"),
            v2._oom_delta(gate["base_v2_gate"], snapshot),
        )
        or not v2.json_type_equal(raw.get("claim"), claim)
        or not v2.json_type_equal(
            raw.get("claim_artifact"),
            v2._physical_record(
                target / SOLVE_CLAIM, target, "cube-solve-claim",
                cap=v2.JSON_MAX_BYTES,
            ),
        )
        or not _validate_solver_invocation_record(
            raw.get("invocation"), process=raw["process"], target=target,
            cube=static["cube"], source_tcb=source_tcb,
        )
        or raw["process"].get("stdout") != v2._hash_record(stdout)
        or raw["process"].get("stderr") != v2._hash_record(stderr)
    ):
        raise CubeProofRunnerError("RAW claim/resource/invocation binding mismatch")
    state = raw["state"]
    no_oom = all(value == 0 for value in raw.get("oom_event_delta", {}).values())
    proof = raw.get("proof")
    strict_unsat = bool(
        state == STATE_RAW_UNSAT and no_oom
        and v2._solver_semantics(raw["process"], stdout, stderr, expected="UNSATISFIABLE")
        and type(proof) is dict
        and v2.json_type_equal(proof, v2._physical_record(
            target / DRAT_ARTIFACT, target, "raw-binary-drat",
            cap=PROOF_MAX_BYTES,
        ))
        and raw.get("sat_terminal") is None
        and raw.get("sat_classification") is None
    )
    classification = raw.get("sat_classification")
    strict_sat = bool(
        state == STATE_SAT and no_oom and proof is None
        and v2._solver_semantics(raw["process"], stdout, stderr, expected="SATISFIABLE")
        and type(classification) is dict
        and classification.get("strict_verified_sat") is True
        and classification.get("classification") == "VERIFIED_SAT_LOW_OPERATOR"
        and classification.get("cube_index") == static["cube"]["cube_index"]
        and selfhash_valid(classification)
        and type(raw.get("sat_terminal")) is dict
    )
    unresolved = bool(
        state == STATE_UNRESOLVED and proof is None
        and type(raw.get("failures")) is list and len(raw["failures"]) > 0
    )
    if not (strict_unsat or strict_sat or unresolved):
        raise CubeProofRunnerError("RAW state truth table mismatch")
    if (
        raw.get("strict_raw_unsat") is not strict_unsat
        or raw.get("strict_verified_sat") is not strict_sat
        or raw.get("decision_complete") is not (strict_unsat or strict_sat)
        or raw.get("production_eligible") is not (strict_unsat or strict_sat)
    ):
        raise CubeProofRunnerError("RAW decision booleans mismatch")
    return {
        "static": static,
        "raw": raw,
        "state": state,
        "strict_unsat": strict_unsat,
        "strict_sat": strict_sat,
        "proof": proof,
    }


def _checker_invocation(
    role: str,
    argv: Sequence[str],
    checker: Mapping[str, Any],
    runtime: Mapping[str, Any],
    cube_memfd: Mapping[str, Any],
    proof_record: Mapping[str, Any],
    output_role: str | None,
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-checker-invocation-v1",
        "role": role,
        "actual_argv_sha256": canonical_sha256(list(argv)),
        "checker": dict(checker),
        "dynamic_runtime": dict(runtime),
        "cube_dimacs": dict(cube_memfd),
        "proof_input": _artifact_reference(proof_record),
        "output_role": output_role,
        "timeout_s": v2.CHECKER_TIMEOUT_S,
        "environment": v2._clean_env(),
    })


def _run_checker(
    *,
    target: Path,
    cube: Mapping[str, Any],
    role: str,
    checker_path: Path,
    checker_sha256: str,
    proof_path: Path,
    proof_record: Mapping[str, Any],
    proof_cap: int,
    marker: bytes,
    output_fd: int | None = None,
) -> tuple[dict[str, Any], bytes, bytes, dict[str, Any]]:
    if checker_path == v2.DRAT_TRIM_PATH and checker_sha256 == v2.EXPECTED_DRAT_TRIM_SHA256:
        checker_bytes = v2.EXPECTED_DRAT_TRIM_BYTES
    elif checker_path == v2.LRAT_CHECK_PATH and checker_sha256 == v2.EXPECTED_LRAT_CHECK_SHA256:
        checker_bytes = v2.EXPECTED_LRAT_CHECK_BYTES
    else:
        raise CubeProofRunnerError("checker path/hash is not pinned")
    checker_fd = cube_fd = proof_fd = -1
    runtime_handle: dict[str, Any] | None = None
    try:
        checker_fd, checker_record = v2._seal_memfd_from_path(
            checker_path,
            expected_sha256=checker_sha256,
            expected_bytes=checker_bytes,
            executable=True,
        )
        cube_fd, cube_record = v2._seal_memfd_from_path(
            target / STATIC_DIMACS,
            expected_sha256=cube["cube_dimacs_sha256"],
            expected_bytes=cube["cube_dimacs_bytes"],
            executable=False,
        )
        proof_fd, bound = v2._open_bound_input(
            proof_path, target, proof_record["role"],
            expected_sha256=proof_record["file_sha256"], cap=proof_cap,
        )
        runtime_handle = v2._stage_dynamic_runtime()
        runtime = runtime_handle["record"]
        loader_fd = runtime_handle["loader_fd"]
        runtime_dir_fd = runtime_handle["directory_fd"]
        prefix = [
            f"/proc/self/fd/{loader_fd}", "--inhibit-cache",
            "--library-path", runtime["library_path"], "--argv0", role,
            f"/proc/self/fd/{checker_fd}", f"/proc/self/fd/{cube_fd}",
            f"/proc/self/fd/{proof_fd}",
        ]
        if role in {"drat-verify", "final-drat-replay"}:
            argv = prefix + ["-t", str(v2.CHECKER_TIMEOUT_S)]
        elif role == "drat-to-lrat":
            if output_fd is None:
                raise CubeProofRunnerError("LRAT conversion output missing")
            argv = prefix + [
                "-L", f"/proc/self/fd/{output_fd}",
                "-t", str(v2.CHECKER_TIMEOUT_S),
            ]
        elif role in {"lrat-check", "final-lrat-replay"}:
            argv = prefix
        else:
            raise CubeProofRunnerError("unknown checker role")
        pass_fds = [loader_fd, runtime_dir_fd, checker_fd, cube_fd, proof_fd]
        watched: list[tuple[int, int]] = []
        if output_fd is not None:
            pass_fds.append(output_fd)
            watched.append((output_fd, LRAT_MAX_BYTES))
        invocation = _checker_invocation(
            role, argv, checker_record, runtime, cube_record, bound,
            "lrat" if output_fd is not None else None,
        )
        process, stdout, stderr = v2._run_capped_process(
            argv,
            timeout_s=v2.CHECKER_TIMEOUT_S,
            stdout_cap=v2.CHECKER_LOG_MAX_BYTES,
            stderr_cap=v2.CHECKER_LOG_MAX_BYTES,
            cwd=target,
            pass_fds=pass_fds,
            file_size_cap=LRAT_MAX_BYTES if output_fd is not None else proof_cap,
            watched_fds=watched,
        )
        v2._assert_bound_input_unchanged(
            proof_fd, proof_path, target, proof_record["role"],
            expected_record=bound, cap=proof_cap,
        )
        v2._validate_staged_dynamic_runtime(runtime_handle)
        result = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-cube16-checker-result-v1",
            "role": role,
            "invocation": invocation,
            "process": process,
            "semantic_marker": marker.decode("ascii"),
            "verified": v2._checker_success(
                process, stdout, stderr, marker=marker,
            ),
        })
        return result, stdout, stderr, bound
    finally:
        if checker_fd >= 0:
            os.close(checker_fd)
        if cube_fd >= 0:
            os.close(cube_fd)
        if proof_fd >= 0:
            os.close(proof_fd)
        if runtime_handle is not None:
            v2._destroy_dynamic_runtime(runtime_handle)


def _publish_logs(
    target: Path, prefix: str, stdout: bytes, stderr: bytes,
) -> list[dict[str, Any]]:
    v2._atomic_publish_bytes(target / "logs", f"{prefix}.stdout", stdout)
    v2._atomic_publish_bytes(target / "logs", f"{prefix}.stderr", stderr)
    return [
        v2._physical_record(
            target / "logs" / f"{prefix}.stdout", target,
            f"{prefix}-stdout", cap=v2.CHECKER_LOG_MAX_BYTES,
        ),
        v2._physical_record(
            target / "logs" / f"{prefix}.stderr", target,
            f"{prefix}-stderr", cap=v2.CHECKER_LOG_MAX_BYTES,
        ),
    ]


def verify_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    _require_cli("verify", target, None, _production_nonce)
    raw = _validate_raw(target, fresh_source_and_tools=True)
    if raw["state"] != STATE_RAW_UNSAT or raw["strict_unsat"] is not True:
        raise CubeProofRunnerError("verify requires strict RAW_UNSAT")
    if (target / VERIFY_CLAIM).exists() or (target / DRAT_COMMIT).exists():
        raise CubeProofRunnerError("verify stage already claimed or committed")
    gate = _two_worker_resource_gate(target, output_cap=LRAT_MAX_BYTES)
    root_before = v2._root_identity(target)
    claim = v2._create_claim(target, VERIFY_CLAIM, "cube-verify")
    claim_record = v2._physical_record(
        target / VERIFY_CLAIM, target, "cube-verify-claim", cap=v2.JSON_MAX_BYTES,
    )
    proof_record = raw["proof"]
    assert type(proof_record) is dict
    drat, out, err, bound_drat = _run_checker(
        target=target,
        cube=raw["static"]["cube"],
        role="drat-verify",
        checker_path=v2.DRAT_TRIM_PATH,
        checker_sha256=v2.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=proof_record,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
    )
    drat_logs = _publish_logs(target, "drat-verify", out, err)
    snapshot = v2._instant_resource(target)
    oom = v2._oom_delta(gate["base_v2_gate"], snapshot)
    drat_passed = bool(
        drat["verified"] is True
        and all(value == 0 for value in oom.values())
        and v2.json_type_equal(root_before, v2._root_identity(target))
    )
    drat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-drat-verification-v1",
        "gate": GATE,
        "state": STATE_DRAT if drat_passed else STATE_UNRESOLVED,
        "root": str(target),
        "cube_index": raw["static"]["cube"]["cube_index"],
        "manifest_sha256": raw["static"]["manifest"]["manifest_sha256"],
        "raw_predecessor_sha256": raw["raw"]["record_sha256"],
        "claim": claim,
        "claim_artifact": claim_record,
        "resource_gate_before": gate,
        "resource_snapshot_after": snapshot,
        "oom_event_delta": oom,
        "bound_drat": bound_drat,
        "checker": drat,
        "logs": drat_logs,
        "verified": drat_passed,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    v2._atomic_publish_json(target / "state", DRAT_COMMIT.name, drat_record)
    if not drat_passed:
        return drat_record
    lrat_gate = _two_worker_resource_gate(target, output_cap=LRAT_MAX_BYTES)
    lrat_fd, private_name = v2._create_private_output(
        target / "artifacts", LRAT_ARTIFACT.name,
    )
    conversion, out, err, conversion_bound = _run_checker(
        target=target,
        cube=raw["static"]["cube"],
        role="drat-to-lrat",
        checker_path=v2.DRAT_TRIM_PATH,
        checker_sha256=v2.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=proof_record,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
        output_fd=lrat_fd,
    )
    conversion_logs = _publish_logs(target, "drat-to-lrat", out, err)
    lrat_sha: str | None = None
    lrat_bytes: int | None = None
    lrat_error: str | None = None
    try:
        os.fsync(lrat_fd)
        lrat_sha, lrat_bytes, _ = v2._hash_fd_stable(
            lrat_fd, cap=LRAT_MAX_BYTES,
        )
    except (OSError, v2.ProofRunnerError) as exc:
        lrat_error = f"{type(exc).__name__}: {exc}"
    conversion_snapshot = v2._instant_resource(target)
    conversion_oom = v2._oom_delta(lrat_gate["base_v2_gate"], conversion_snapshot)
    conversion_passed = bool(
        conversion["verified"] is True
        and all(value == 0 for value in conversion_oom.values())
        and lrat_error is None and type(lrat_sha) is str
        and type(lrat_bytes) is int and 0 < lrat_bytes <= LRAT_MAX_BYTES
    )
    lrat_artifact: dict[str, Any] | None = None
    if conversion_passed:
        assert lrat_sha is not None and lrat_bytes is not None
        v2._publish_private_output(
            target / "artifacts", private_name, lrat_fd, LRAT_ARTIFACT.name,
            expected_sha256=lrat_sha, expected_bytes=lrat_bytes,
        )
        lrat_fd = -1
        lrat_artifact = v2._physical_record(
            target / LRAT_ARTIFACT, target, "converted-lrat",
            cap=LRAT_MAX_BYTES,
        )
    else:
        v2._discard_private(target / "artifacts", private_name, lrat_fd)
        lrat_fd = -1
    lrat_check = None
    lrat_logs = None
    bound_lrat = None
    if conversion_passed and lrat_artifact is not None:
        lrat_check, out, err, bound_lrat = _run_checker(
            target=target,
            cube=raw["static"]["cube"],
            role="lrat-check",
            checker_path=v2.LRAT_CHECK_PATH,
            checker_sha256=v2.EXPECTED_LRAT_CHECK_SHA256,
            proof_path=target / LRAT_ARTIFACT,
            proof_record=lrat_artifact,
            proof_cap=LRAT_MAX_BYTES,
            marker=b"c VERIFIED",
        )
        lrat_logs = _publish_logs(target, "lrat-check", out, err)
    final_snapshot = v2._instant_resource(target)
    final_oom = v2._oom_delta(lrat_gate["base_v2_gate"], final_snapshot)
    lrat_passed = bool(
        conversion_passed and type(lrat_check) is dict
        and lrat_check.get("verified") is True
        and all(value == 0 for value in final_oom.values())
        and v2.json_type_equal(root_before, v2._root_identity(target))
    )
    lrat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-lrat-verification-v1",
        "gate": GATE,
        "state": STATE_LRAT if lrat_passed else STATE_UNRESOLVED,
        "root": str(target),
        "cube_index": raw["static"]["cube"]["cube_index"],
        "manifest_sha256": raw["static"]["manifest"]["manifest_sha256"],
        "drat_predecessor_sha256": drat_record["record_sha256"],
        "resource_gate_before_conversion": lrat_gate,
        "resource_snapshot_after_conversion": conversion_snapshot,
        "resource_snapshot_after_lrat": final_snapshot,
        "oom_event_delta": final_oom,
        "bound_drat": conversion_bound,
        "conversion": conversion,
        "conversion_logs": conversion_logs,
        "lrat_error": lrat_error,
        "lrat_artifact": lrat_artifact,
        "bound_lrat": bound_lrat,
        "lrat_checker": lrat_check,
        "lrat_checker_logs": lrat_logs,
        "verified": lrat_passed,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    v2._atomic_publish_json(target / "state", LRAT_COMMIT.name, lrat_record)
    return lrat_record


def _validate_lrat(root: Path, *, fresh_source_and_tools: bool) -> dict[str, Any]:
    raw = _validate_raw(root, fresh_source_and_tools=fresh_source_and_tools)
    target = Path(root)
    drat = v2._strict_json(target / DRAT_COMMIT)
    lrat = v2._strict_json(target / LRAT_COMMIT)
    if (
        not selfhash_valid(drat) or not selfhash_valid(lrat)
        or drat.get("kind") != "paper400-cube16-drat-verification-v1"
        or drat.get("state") != STATE_DRAT or drat.get("verified") is not True
        or drat.get("raw_predecessor_sha256") != raw["raw"]["record_sha256"]
        or lrat.get("kind") != "paper400-cube16-lrat-verification-v1"
        or lrat.get("state") != STATE_LRAT or lrat.get("verified") is not True
        or lrat.get("drat_predecessor_sha256") != drat["record_sha256"]
        or lrat.get("cube_index") != raw["static"]["cube"]["cube_index"]
        or lrat.get("manifest_sha256") != raw["static"]["manifest"]["manifest_sha256"]
    ):
        raise CubeProofRunnerError("LRAT chain schema/state mismatch")
    proof = raw["proof"]
    lrat_artifact = lrat.get("lrat_artifact")
    if (
        type(proof) is not dict or type(lrat_artifact) is not dict
        or not v2.json_type_equal(proof, v2._physical_record(
            target / DRAT_ARTIFACT, target, "raw-binary-drat",
            cap=PROOF_MAX_BYTES,
        ))
        or not v2.json_type_equal(lrat_artifact, v2._physical_record(
            target / LRAT_ARTIFACT, target, "converted-lrat",
            cap=LRAT_MAX_BYTES,
        ))
        or lrat.get("lrat_checker", {}).get("verified") is not True
        or lrat.get("conversion", {}).get("verified") is not True
    ):
        raise CubeProofRunnerError("LRAT proof artifact/checker binding mismatch")
    return {"raw": raw, "drat": drat, "lrat": lrat}


def _fresh_proof_replay(
    target: Path, chain: Mapping[str, Any],
) -> dict[str, Any]:
    raw = chain["raw"]
    proof = raw["proof"]
    lrat_artifact = chain["lrat"]["lrat_artifact"]
    assert type(proof) is dict and type(lrat_artifact) is dict
    drat, drat_out, drat_err, bound_drat = _run_checker(
        target=target,
        cube=raw["static"]["cube"],
        role="final-drat-replay",
        checker_path=v2.DRAT_TRIM_PATH,
        checker_sha256=v2.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=proof,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
    )
    lrat, lrat_out, lrat_err, bound_lrat = _run_checker(
        target=target,
        cube=raw["static"]["cube"],
        role="final-lrat-replay",
        checker_path=v2.LRAT_CHECK_PATH,
        checker_sha256=v2.EXPECTED_LRAT_CHECK_SHA256,
        proof_path=target / LRAT_ARTIFACT,
        proof_record=lrat_artifact,
        proof_cap=LRAT_MAX_BYTES,
        marker=b"c VERIFIED",
    )
    passed = drat["verified"] is True and lrat["verified"] is True
    if not passed:
        raise CubeProofRunnerError("final fresh DRAT/LRAT replay failed")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-fresh-proof-replay-v1",
        "cube_index": raw["static"]["cube"]["cube_index"],
        "manifest_sha256": raw["static"]["manifest"]["manifest_sha256"],
        "bound_drat": bound_drat,
        "bound_lrat": bound_lrat,
        "drat_checker": drat,
        "lrat_checker": lrat,
        "drat_stdout": v2._hash_record(drat_out),
        "drat_stderr": v2._hash_record(drat_err),
        "lrat_stdout": v2._hash_record(lrat_out),
        "lrat_stderr": v2._hash_record(lrat_err),
        "all_fresh_replay_passed": True,
        "solver_invoked": False,
    })


def _certificate_value(
    chain: Mapping[str, Any], fresh: Mapping[str, Any],
) -> dict[str, Any]:
    raw = chain["raw"]
    static = raw["static"]
    cube = static["cube"]
    drat_artifact = raw["proof"]
    lrat_artifact = chain["lrat"]["lrat_artifact"]
    assert type(drat_artifact) is dict and type(lrat_artifact) is dict
    proof_chain = seal({
        "format": "binary-drat+converted-lrat-v1",
        "binary_drat": _artifact_reference(drat_artifact),
        "converted_lrat": _artifact_reference(lrat_artifact),
        "drat_checker_sha256": v2.EXPECTED_DRAT_TRIM_SHA256,
        "lrat_checker_sha256": v2.EXPECTED_LRAT_CHECK_SHA256,
        "trusted_policy_sha256": v2.EXPECTED_POLICY_CANONICAL_SHA256,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
        "drat_record_sha256": chain["drat"]["record_sha256"],
        "lrat_record_sha256": chain["lrat"]["record_sha256"],
        "fresh_replay_record_sha256": fresh["record_sha256"],
    }, "chain_sha256")
    predecessor_hash = canonical_sha256([
        static["static"]["record_sha256"], raw["raw"]["record_sha256"],
        chain["drat"]["record_sha256"], chain["lrat"]["record_sha256"],
    ])
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CUBE_CERTIFICATE_KIND,
        "gate": GATE,
        "state": STATE_FINAL,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": True,
        "manifest_sha256": static["manifest"]["manifest_sha256"],
        "base_cnf_sha256": static["manifest"]["base"]["cnf_sha256"],
        "base_dimacs_sha256": static["manifest"]["base"]["dimacs_sha256"],
        "cube_index": cube["cube_index"],
        "cube_id": cube["cube_id"],
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": cube["cube_dimacs_sha256"],
        "cube_num_variables": cube["cube_num_variables"],
        "cube_num_clauses": cube["cube_num_clauses"],
        "cube_dimacs_bytes": cube["cube_dimacs_bytes"],
        "unit_clauses": cube["unit_clauses"],
        "solver": {
            "name": EXPECTED_SOLVER_NAME,
            "version": EXPECTED_SOLVER_VERSION,
            "executable_sha256": v2.EXPECTED_SOLVER_SHA256,
        },
        "cube16_source_sha256": EXPECTED_CUBE_SHA256,
        "aggregate_source_sha256": EXPECTED_AGGREGATE_SHA256,
        "decision": {
            "outcome": "unsat", "status_name": "UNSATISFIABLE",
            "decision_complete": True, "clean_exit": True,
            "timed_out": False, "solver_invocations": 1,
        },
        "proof_chain": proof_chain,
        "source_binding_sha256": static["static"]["source_binding"]["record_sha256"],
        "toolchain_binding_sha256": static["static"]["toolchain_binding"]["record_sha256"],
        "predecessor_chain_sha256": predecessor_hash,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "certificate_sha256")


def finalize_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    _require_cli("finalize", target, None, _production_nonce)
    chain = _validate_lrat(target, fresh_source_and_tools=True)
    if (
        (target / FINALIZE_CLAIM).exists()
        or (target / CERTIFICATE).exists()
        or (target / FINAL_COMMIT).exists()
    ):
        raise CubeProofRunnerError("finalize stage already claimed or committed")
    gate = _two_worker_resource_gate(target, output_cap=0)
    root_before = v2._root_identity(target)
    claim = v2._create_claim(target, FINALIZE_CLAIM, "cube-finalize")
    fresh = _fresh_proof_replay(target, chain)
    snapshot = v2._instant_resource(target)
    oom = v2._oom_delta(gate["base_v2_gate"], snapshot)
    if any(value != 0 for value in oom.values()):
        raise CubeProofRunnerError("OOM event during final cube replay")
    if not v2.json_type_equal(root_before, v2._root_identity(target)):
        raise CubeProofRunnerError("root identity changed during final replay")
    certificate = _certificate_value(chain, fresh)
    v2._atomic_publish_json(target, CERTIFICATE.name, certificate)
    certificate_record = v2._physical_record(
        target / CERTIFICATE, target, "proof-carrying-cube-certificate",
        cap=v2.JSON_MAX_BYTES,
    )
    commit = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-cube16-final-commit-v1",
        "gate": GATE,
        "state": STATE_FINAL,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": True,
        "root": str(target),
        "cube_index": chain["raw"]["static"]["cube"]["cube_index"],
        "manifest_sha256": chain["raw"]["static"]["manifest"]["manifest_sha256"],
        "lrat_predecessor_sha256": chain["lrat"]["record_sha256"],
        "claim": claim,
        "resource_gate_before": gate,
        "resource_snapshot_after": snapshot,
        "oom_event_delta": oom,
        "fresh_replay": fresh,
        "certificate": certificate_record,
        "certificate_sha256": certificate["certificate_sha256"],
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
        "no_further_root_writes_after_this_commit": True,
    })
    v2._atomic_publish_json(target, FINAL_COMMIT.name, commit)
    return commit


def _validation_record(
    *,
    root: Path,
    manifest: Mapping[str, Any],
    cube: Mapping[str, Any],
    state: str,
    certificate: Mapping[str, Any] | None,
    sat_terminal: Mapping[str, Any] | None,
    failures: Sequence[str],
    fresh_proof_replay: bool,
) -> dict[str, Any]:
    strict_unsat = state == STATE_FINAL and not failures and fresh_proof_replay
    strict_sat = state == STATE_SAT and not failures
    valid = strict_unsat or strict_sat
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CUBE_VALIDATION_KIND,
        "gate": GATE,
        "root": str(root),
        "manifest_sha256": manifest["manifest_sha256"],
        "cube_index": cube["cube_index"],
        "cube_id": cube["cube_id"],
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": cube["cube_dimacs_sha256"],
        "state": state if valid else STATE_UNRESOLVED,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "valid": valid,
        "strict_proof_unsat": strict_unsat,
        "strict_verified_sat": strict_sat,
        "fresh_proof_replay": bool(strict_unsat),
        "source_toolchain_fresh": True,
        "certificate": None if certificate is None else dict(certificate),
        "sat_terminal": None if sat_terminal is None else dict(sat_terminal),
        "failures": list(failures),
    }, "validation_sha256")


def validate_final_root(
    root: Path,
    *,
    bound_manifest: Mapping[str, Any] | None = None,
    execute_fresh_replay: bool,
    _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = v2._validate_root_argument(Path(root), must_exist=True)
    if _production_nonce is _PRODUCTION_NONCE:
        _require_cli("validate", target, None, _production_nonce)
    static = _validate_static(target, fresh_source_and_tools=True)
    manifest = static["manifest"]
    cube = static["cube"]
    if bound_manifest is not None and not v2.json_type_equal(bound_manifest, manifest):
        return _validation_record(
            root=target, manifest=manifest, cube=cube, state=STATE_UNRESOLVED,
            certificate=None, sat_terminal=None,
            failures=["bound cover manifest mismatch"], fresh_proof_replay=False,
        )
    raw = _validate_raw(target, fresh_source_and_tools=True)
    if raw["strict_sat"] is True:
        return _validation_record(
            root=target, manifest=manifest, cube=cube, state=STATE_SAT,
            certificate=None, sat_terminal=raw["raw"]["sat_classification"],
            failures=[], fresh_proof_replay=False,
        )
    if raw["strict_unsat"] is not True:
        return _validation_record(
            root=target, manifest=manifest, cube=cube, state=STATE_UNRESOLVED,
            certificate=None, sat_terminal=None,
            failures=["root has no strict SAT or proof-carrying UNSAT terminal"],
            fresh_proof_replay=False,
        )
    chain = _validate_lrat(target, fresh_source_and_tools=True)
    certificate = v2._strict_json(target / CERTIFICATE)
    commit = v2._strict_json(target / FINAL_COMMIT)
    failures: list[str] = []
    if (
        not selfhash_valid(certificate, "certificate_sha256")
        or certificate.get("kind") != CUBE_CERTIFICATE_KIND
        or certificate.get("state") != STATE_FINAL
        or certificate.get("manifest_sha256") != manifest["manifest_sha256"]
        or certificate.get("cube_sha256") != cube["cube_sha256"]
        or certificate.get("cube_cnf_sha256") != cube["cube_cnf_sha256"]
        or certificate.get("global_distance_claim") is not None
        or certificate.get("publication_certificate") is not False
    ):
        failures.append("final cube certificate schema/binding mismatch")
    if (
        not selfhash_valid(commit)
        or commit.get("kind") != "paper400-cube16-final-commit-v1"
        or commit.get("state") != STATE_FINAL
        or commit.get("certificate_sha256") != certificate.get("certificate_sha256")
        or commit.get("lrat_predecessor_sha256") != chain["lrat"]["record_sha256"]
        or commit.get("no_further_root_writes_after_this_commit") is not True
    ):
        failures.append("final COMMIT schema/binding mismatch")
    fresh_passed = False
    if not failures and execute_fresh_replay:
        fresh = _fresh_proof_replay(target, chain)
        fresh_passed = fresh.get("all_fresh_replay_passed") is True
        if not fresh_passed:
            failures.append("fresh proof replay failed")
    elif not execute_fresh_replay:
        failures.append("fresh proof replay was not executed")
    return _validation_record(
        root=target, manifest=manifest, cube=cube,
        state=STATE_FINAL if not failures else STATE_UNRESOLVED,
        certificate=certificate if not failures else None,
        sat_terminal=None,
        failures=failures,
        fresh_proof_replay=fresh_passed,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    subparsers = parser.add_subparsers(dest="action", required=True)
    preflight = subparsers.add_parser("preflight", allow_abbrev=False)
    preflight.add_argument("--cube-index", required=True, type=int)
    prepare = subparsers.add_parser("prepare", allow_abbrev=False)
    prepare.add_argument("--root", required=True, type=Path)
    prepare.add_argument("--cube-index", required=True, type=int)
    for action in ("solve", "verify", "finalize", "validate"):
        child = subparsers.add_parser(action, allow_abbrev=False)
        child.add_argument("--root", required=True, type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    effective = list(sys.argv[1:] if argv is None else argv)
    if len(effective) == 3 and effective[:2] == ["__build", "--cube-index"]:
        return _cube_builder_helper(int(effective[2]))
    if (
        len(effective) == 5
        and effective[0] == "__sat_replay"
        and effective[1] == "--cube-index"
        and effective[3] == "--model-fd"
    ):
        return _cube_sat_helper(int(effective[2]), int(effective[4]))
    args = build_parser().parse_args(effective)
    if args.action == "preflight":
        result = preflight_only(
            args.cube_index, _production_nonce=_PRODUCTION_NONCE,
        )
    elif args.action == "prepare":
        result = prepare_root(
            args.root, args.cube_index, _production_nonce=_PRODUCTION_NONCE,
        )
    elif args.action == "solve":
        result = solve_root(args.root, _production_nonce=_PRODUCTION_NONCE)
    elif args.action == "verify":
        result = verify_root(args.root, _production_nonce=_PRODUCTION_NONCE)
    elif args.action == "finalize":
        result = finalize_root(args.root, _production_nonce=_PRODUCTION_NONCE)
    elif args.action == "validate":
        result = validate_final_root(
            args.root,
            bound_manifest=None,
            execute_fresh_replay=True,
            _production_nonce=_PRODUCTION_NONCE,
        )
    else:
        raise CubeProofRunnerError("unreachable action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    if args.action == "solve":
        return 0 if result.get("state") in {STATE_RAW_UNSAT, STATE_SAT} else 2
    if args.action == "verify":
        return 0 if result.get("state") == STATE_LRAT else 2
    if args.action == "validate":
        return 0 if result.get("valid") is True else 2
    return 0


if __name__ == "__main__":
    try:
        _exit = main()
    except v2._ForwardedParentSignal as forwarded:
        v2._terminate_by_forwarded_signal(forwarded.signum)
    raise SystemExit(_exit)


__all__ = [
    "CubeProofRunnerError", "GATE", "INITIAL_PARALLELISM", "STATE_FINAL",
    "STATE_LRAT", "STATE_RAW_UNSAT", "STATE_SAT", "STATE_UNRESOLVED",
    "build_parser", "canonical_bytes", "canonical_sha256", "finalize_root",
    "main", "preflight_only", "prepare_root", "seal", "selfhash_valid",
    "solve_root", "two_worker_capacity_requirement", "validate_final_root",
    "verify_root",
]
