#!/usr/bin/env python3
"""Plan-only native LRAT launch protocol for future Paper400 leaves.

This module deliberately has no solver-launch, checkpoint, terminal-publication,
aggregation, or cleanup command.  It prepares and validates an immutable plan
for *new* generation-zero leaves.  A separate launcher may consume that plan,
publish pre-exec process-identity receipts, and release its own gates only after
every participant is present in an all-start barrier record.

The plan switches proof production at leaf creation time by invoking the
pinned CaDiCaL 1.9.5 binary with exact ``--lrat --no-binary`` options.  It
never converts or appends to an existing DRAT/LRAT stream, and it cannot adopt
a DMTCP checkpoint.  Completed
proofs must pass the pinned ``lrat-check`` twice in distinct processes (the
second run is a fresh replay) before the existing certification layer may
consume them.  This module only describes that handoff; it never authenticates
an UNSAT result itself.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_VERSION = 1
SPEC_KIND = "paper400-native-lrat-future-launch-spec-v1"
PLAN_KIND = "paper400-native-lrat-future-launch-plan-v1"
PREEXEC_OBSERVATION_KIND = "paper400-native-lrat-preexec-observation-v1"
START_RECEIPT_KIND = "paper400-native-lrat-start-receipt-v1"
BARRIER_KIND = "paper400-native-lrat-all-start-barrier-v1"
CPU_LEASE_KIND = "paper400-exclusive-cpu-lease-v1"

SOLVER_PATH = Path("/home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical")
SOLVER_SHA256 = "6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21"
SOLVER_VERSION = "1.9.5"
SOLVER_UPSTREAM_COMMIT = "146207318796f094dcded87349a64f0c6927309e"
AUDIT_PATH = Path(
    "/home/jing/paper400-toolchain/audit/standalone-audit-manifest.json"
)
AUDIT_SHA256 = "e274b8e5ab4e9456096243ad5ce3a3a8248374590a0ebf49ce36653357294e6a"

LRAT_CHECKER_PATH = Path(
    "/home/jing/paper400-toolchain/proof-checkers/bin/lrat-check"
)
LRAT_CHECKER_SHA256 = (
    "c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79"
)
LRAT_CHECKER_SOURCE_COMMIT = "2e5e29cb0019d5cfd547d4208dca1b3ec290349f"
TRUSTED_POLICY_PATH = Path(
    "/home/jing/paper400-toolchain/audit/trusted-checker-policy.json"
)
TRUSTED_POLICY_FILE_SHA256 = (
    "af3a2089ebf0df9b1120e1cfd3164cc6a2e9bf07bb35c057f3f85890d0f854e2"
)
TRUSTED_POLICY_INTERNAL_SHA256 = (
    "c5575a34b4cee90f3967e951f885653740fbbe7c2edf2c1323ab552d9872ea86"
)
LRAT_CHECKER_SEMANTIC_STDOUT_SHA256 = (
    "2ce44b85e9a3e98cd83237e029479737ad93272311d7d643d428bb640fc24dcc"
)
LRAT_CHECKER_TIMEOUT_SECONDS = 604800
LRAT_CHECKER_MAX_PROOF_BYTES = 1 << 40

MAX_JSON_BYTES = 16 << 20
MAX_CNF_BYTES = 16 << 30
MAX_TOOL_BYTES = 64 << 20
HASH_CHUNK_BYTES = 8 << 20
MAX_PARTICIPANTS = 224
SOLVER_CNF_FD = 201
SOLVER_PROOF_FD = 202
CHECKER_CNF_FD = 211
CHECKER_PROOF_FD = 212
IDENTIFIER = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]{0,127}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")


class NativeLratPlanError(RuntimeError):
    """A future-leaf plan or receipt failed closed."""


@dataclass(frozen=True)
class ToolchainPins:
    """Injectable only for isolated tests; the CLI always uses ``DEFAULT_PINS``."""

    solver_path: Path
    solver_sha256: str
    solver_version: str
    solver_upstream_commit: str
    audit_path: Path
    audit_sha256: str
    lrat_checker_path: Path
    lrat_checker_sha256: str
    lrat_checker_source_commit: str
    trusted_policy_path: Path
    trusted_policy_file_sha256: str
    trusted_policy_internal_sha256: str
    lrat_checker_semantic_stdout_sha256: str
    lrat_checker_timeout_seconds: int = LRAT_CHECKER_TIMEOUT_SECONDS
    lrat_checker_max_proof_bytes: int = LRAT_CHECKER_MAX_PROOF_BYTES


DEFAULT_PINS = ToolchainPins(
    solver_path=SOLVER_PATH,
    solver_sha256=SOLVER_SHA256,
    solver_version=SOLVER_VERSION,
    solver_upstream_commit=SOLVER_UPSTREAM_COMMIT,
    audit_path=AUDIT_PATH,
    audit_sha256=AUDIT_SHA256,
    lrat_checker_path=LRAT_CHECKER_PATH,
    lrat_checker_sha256=LRAT_CHECKER_SHA256,
    lrat_checker_source_commit=LRAT_CHECKER_SOURCE_COMMIT,
    trusted_policy_path=TRUSTED_POLICY_PATH,
    trusted_policy_file_sha256=TRUSTED_POLICY_FILE_SHA256,
    trusted_policy_internal_sha256=TRUSTED_POLICY_INTERNAL_SHA256,
    lrat_checker_semantic_stdout_sha256=LRAT_CHECKER_SEMANTIC_STDOUT_SHA256,
)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    if field in value:
        raise NativeLratPlanError(f"record already contains seal field {field}")
    result = dict(value)
    result[field] = _digest(result)
    return result


def selfhash_valid(value: Any, field: str = "record_sha256") -> bool:
    return (
        type(value) is dict
        and type(value.get(field)) is str
        and SHA256.fullmatch(value[field]) is not None
        and value[field] == _digest({key: item for key, item in value.items() if key != field})
    )


def _expect_exact_keys(value: Mapping[str, Any], expected: set[str], role: str) -> None:
    if set(value) != expected:
        missing = sorted(expected - set(value))
        extra = sorted(set(value) - expected)
        raise NativeLratPlanError(
            f"{role} keys mismatch (missing={missing}, extra={extra})"
        )


def _identifier(value: Any, role: str) -> str:
    if type(value) is not str or IDENTIFIER.fullmatch(value) is None:
        raise NativeLratPlanError(f"invalid {role}")
    return value


def _sha256(value: Any, role: str) -> str:
    if type(value) is not str or SHA256.fullmatch(value) is None:
        raise NativeLratPlanError(f"invalid {role}")
    return value


def _positive_int(value: Any, role: str) -> int:
    if type(value) is not int or value <= 0:
        raise NativeLratPlanError(f"invalid {role}")
    return value


def _canonical_existing_file(path: Path, role: str) -> Path:
    target = Path(path)
    if not target.is_absolute():
        raise NativeLratPlanError(f"{role} path is not absolute")
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise NativeLratPlanError(f"cannot resolve {role}: {target}") from exc
    if resolved != target or stat.S_ISLNK(lexical.st_mode):
        raise NativeLratPlanError(f"{role} path is not canonical or is a symlink")
    return target


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev), int(info.st_ino), int(info.st_mode), int(info.st_uid),
        int(info.st_nlink), int(info.st_size), int(info.st_mtime_ns),
        int(info.st_ctime_ns),
    )


def _bind_file(
    path: Path,
    *,
    role: str,
    cap: int,
    executable: bool | None = None,
    capture_prefix_bytes: int = 0,
) -> tuple[dict[str, Any], bytes]:
    target = _canonical_existing_file(Path(path), role)
    lexical = target.lstat()
    if (
        not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or lexical.st_nlink != 1
        or lexical.st_size < 0
        or lexical.st_size > cap
        or (executable is True and not (lexical.st_mode & stat.S_IXUSR))
        or (executable is False and (lexical.st_mode & stat.S_IXUSR))
    ):
        raise NativeLratPlanError(f"unsafe {role} binding: {target}")
    descriptor = os.open(target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    digest = hashlib.sha256()
    prefix = bytearray()
    total = 0
    try:
        before = os.fstat(descriptor)
        if _identity(before) != _identity(lexical):
            raise NativeLratPlanError(f"{role} changed before hashing")
        while True:
            chunk = os.read(descriptor, HASH_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise NativeLratPlanError(f"{role} exceeds configured cap")
            digest.update(chunk)
            if len(prefix) < capture_prefix_bytes:
                prefix.extend(chunk[: capture_prefix_bytes - len(prefix)])
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if _identity(before) != _identity(after) or total != before.st_size:
        raise NativeLratPlanError(f"{role} changed while hashing")
    return ({
        "role": role,
        "path": str(target),
        "sha256": digest.hexdigest(),
        "bytes": total,
        "device": int(before.st_dev),
        "inode": int(before.st_ino),
        "mode": stat.S_IMODE(before.st_mode),
        "uid": int(before.st_uid),
        "links": int(before.st_nlink),
        "mtime_ns": int(before.st_mtime_ns),
        "ctime_ns": int(before.st_ctime_ns),
    }, bytes(prefix))


def _read_json_file(path: Path, role: str) -> tuple[dict[str, Any], dict[str, Any]]:
    binding, payload = _bind_file(
        path, role=role, cap=MAX_JSON_BYTES, executable=False,
        capture_prefix_bytes=MAX_JSON_BYTES,
    )
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLratPlanError(f"invalid JSON in {role}") from exc
    if type(value) is not dict:
        raise NativeLratPlanError(f"{role} is not a JSON object")
    return binding, value


def _bind_cnf(path: Path) -> dict[str, Any]:
    binding, prefix = _bind_file(
        path, role="leaf-cnf", cap=MAX_CNF_BYTES, executable=False,
        capture_prefix_bytes=1 << 20,
    )
    header: tuple[int, int] | None = None
    try:
        text = prefix.decode("ascii")
    except UnicodeDecodeError as exc:
        raise NativeLratPlanError("leaf CNF prefix is not ASCII DIMACS") from exc
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        if len(fields) == 4 and fields[:2] == ["p", "cnf"]:
            try:
                variables, clauses = int(fields[2]), int(fields[3])
            except ValueError as exc:
                raise NativeLratPlanError("invalid DIMACS header") from exc
            if variables < 0 or clauses < 0:
                raise NativeLratPlanError("negative DIMACS header")
            header = (variables, clauses)
        break
    if header is None:
        raise NativeLratPlanError("leaf CNF lacks an early canonical DIMACS header")
    return {**binding, "dimacs_variables": header[0], "dimacs_clauses": header[1]}


def _bind_directory(path: Path, role: str) -> dict[str, Any]:
    target = _canonical_existing_file(Path(path), role)
    info = target.lstat()
    if (
        not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or (stat.S_IMODE(info.st_mode) & 0o022) != 0
    ):
        raise NativeLratPlanError(f"unsafe {role} directory: {target}")
    return {
        "role": role,
        "path": str(target),
        "device": int(info.st_dev),
        "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode),
        "uid": int(info.st_uid),
    }


def _proof_output_contract(path_value: Any, *, require_absent: bool) -> dict[str, Any]:
    if type(path_value) is not str:
        raise NativeLratPlanError("proof output path is not a string")
    path = Path(path_value)
    if not path.is_absolute() or path.suffix != ".lrat":
        raise NativeLratPlanError("proof output must be an absolute .lrat path")
    try:
        parent = path.parent.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise NativeLratPlanError("proof output parent cannot be resolved") from exc
    canonical = parent / path.name
    if canonical != path:
        raise NativeLratPlanError("proof output path is not canonical")
    if require_absent and path.exists():
        raise NativeLratPlanError("proof output already exists; append/adoption is forbidden")
    if path.is_symlink():
        raise NativeLratPlanError("proof output is a symlink")
    return {
        "role": "native-lrat-proof-output",
        "path": str(path),
        "parent": _bind_directory(parent, "proof-output-parent"),
        "required_suffix": ".lrat",
        "must_not_exist_before_launch": True,
        "creation_flags": ["O_CLOEXEC", "O_CREAT", "O_EXCL", "O_NOFOLLOW", "O_WRONLY"],
        "creation_mode": 0o600,
        "append_permitted": False,
        "replace_permitted": False,
        "proof_format": "native-lrat",
    }


def _toolchain_binding(pins: ToolchainPins) -> dict[str, Any]:
    solver, _ = _bind_file(
        pins.solver_path, role="cadical-1.9.5", cap=MAX_TOOL_BYTES,
        executable=True,
    )
    audit, audit_json = _read_json_file(pins.audit_path, "cadical-audit-manifest")
    checker, _ = _bind_file(
        pins.lrat_checker_path, role="lrat-check", cap=MAX_TOOL_BYTES,
        executable=True,
    )
    policy, policy_json = _read_json_file(
        pins.trusted_policy_path, "trusted-checker-policy",
    )
    for actual, expected, role in (
        (solver["sha256"], pins.solver_sha256, "CaDiCaL binary"),
        (audit["sha256"], pins.audit_sha256, "CaDiCaL audit manifest"),
        (checker["sha256"], pins.lrat_checker_sha256, "LRAT checker"),
        (policy["sha256"], pins.trusted_policy_file_sha256, "checker policy"),
    ):
        if actual != expected:
            raise NativeLratPlanError(f"pinned {role} SHA-256 mismatch")
    try:
        generated = audit_json["build"]["generated_files"]["build/cadical"]
        version = audit_json["cli_audit"]["version"]
        upstream = audit_json["upstream"]
    except (KeyError, TypeError) as exc:
        raise NativeLratPlanError("CaDiCaL audit manifest is incomplete") from exc
    if (
        audit_json.get("schema_version") != 1
        or audit_json.get("kind") != "cadical-rel-1.9.5-standalone-audit-v1"
        or audit_json.get("status") != "PASS"
        or audit_json.get("scope") != {"n400_solver_invoked": False}
        or generated.get("sha256") != pins.solver_sha256
        or generated.get("bytes") != solver["bytes"]
        or version.get("returncode") != 0
        or version.get("stdout") != pins.solver_version
        or audit_json.get("cli_audit", {}).get("default_proof_format") != "binary DRAT"
        or audit_json.get("cli_audit", {}).get("exit_codes")
        != {"sat": 10, "unsat": 20, "unknown": 0}
        or upstream.get("commit_git_sha1") != pins.solver_upstream_commit
    ):
        raise NativeLratPlanError("CaDiCaL binary/source audit identity mismatch")
    try:
        policy_checker = policy_json["checkers"][
            "lrat-check-v05.22.2023-gcc11.4.0-x86_64"
        ]
    except (KeyError, TypeError) as exc:
        raise NativeLratPlanError("trusted LRAT checker policy is incomplete") from exc
    if (
        policy_json.get("schema_version") != 1
        or policy_json.get("kind") != "paper400-trusted-checker-policy-v1"
        or not selfhash_valid(policy_json, "policy_sha256")
        or policy_json.get("policy_sha256") != pins.trusted_policy_internal_sha256
        or policy_checker.get("binary_sha256") != pins.lrat_checker_sha256
        or policy_checker.get("source_commit") != pins.lrat_checker_source_commit
        or policy_checker.get("checker_role") != "lrat-check"
        or policy_checker.get("proof_format") != "lrat"
        or policy_checker.get("argv_roles") != ["binary", "dimacs", "proof"]
        or policy_checker.get("semantic_stdout_sha256")
        != pins.lrat_checker_semantic_stdout_sha256
        or policy_checker.get("timeout_s") != pins.lrat_checker_timeout_seconds
        or policy_checker.get("max_proof_bytes") != pins.lrat_checker_max_proof_bytes
    ):
        raise NativeLratPlanError("trusted LRAT checker policy identity mismatch")
    return {
        "solver": {
            **solver,
            "version": pins.solver_version,
            "upstream_commit_git_sha1": pins.solver_upstream_commit,
        },
        "solver_audit_manifest": audit,
        "lrat_checker": {
            **checker,
            "source_commit_git_sha1": pins.lrat_checker_source_commit,
        },
        "trusted_checker_policy": {
            **policy,
            "internal_policy_sha256": pins.trusted_policy_internal_sha256,
        },
    }


def _normalise_request(spec: Mapping[str, Any]) -> dict[str, Any]:
    _expect_exact_keys(spec, {
        "schema_version", "kind", "campaign_id", "launch_id", "generation",
        "fresh_leaf_generation", "resume", "checkpoint_source",
        "existing_proof_path", "existing_proof_format", "all_start_barrier",
        "leaves",
    }, "launch spec")
    if spec.get("schema_version") != SCHEMA_VERSION or spec.get("kind") != SPEC_KIND:
        raise NativeLratPlanError("unsupported launch spec")
    if (
        spec.get("generation") != 0
        or spec.get("fresh_leaf_generation") is not True
        or spec.get("resume") is not False
        or spec.get("checkpoint_source") is not None
        or spec.get("existing_proof_path") is not None
        or spec.get("existing_proof_format") is not None
    ):
        raise NativeLratPlanError(
            "native LRAT is only valid for a fresh generation-zero leaf; "
            "resume, checkpoints, existing proofs, and format switches are forbidden"
        )
    campaign_id = _identifier(spec.get("campaign_id"), "campaign id")
    launch_id = _identifier(spec.get("launch_id"), "launch id")
    barrier = spec.get("all_start_barrier")
    if type(barrier) is not dict:
        raise NativeLratPlanError("all-start barrier is missing")
    _expect_exact_keys(
        barrier, {"barrier_id", "timeout_seconds", "require_every_leaf"},
        "all-start barrier",
    )
    barrier_id = _identifier(barrier.get("barrier_id"), "barrier id")
    timeout_seconds = _positive_int(barrier.get("timeout_seconds"), "barrier timeout")
    if barrier.get("require_every_leaf") is not True:
        raise NativeLratPlanError("all-start barrier must require every leaf")
    leaves = spec.get("leaves")
    if type(leaves) is not list or not 1 <= len(leaves) <= MAX_PARTICIPANTS:
        raise NativeLratPlanError("invalid future-leaf participant count")
    normalised_leaves: list[dict[str, Any]] = []
    leaf_ids: set[str] = set()
    cpus: set[int] = set()
    lease_ids: set[str] = set()
    outputs: set[str] = set()
    cnfs: set[str] = set()
    for value in leaves:
        if type(value) is not dict:
            raise NativeLratPlanError("leaf specification is not an object")
        _expect_exact_keys(value, {"leaf_id", "cnf_path", "proof_output_path", "cpu_lease"}, "leaf")
        leaf_id = _identifier(value.get("leaf_id"), "leaf id")
        if leaf_id in leaf_ids:
            raise NativeLratPlanError("duplicate leaf id")
        lease = value.get("cpu_lease")
        if type(lease) is not dict:
            raise NativeLratPlanError("CPU lease is missing")
        _expect_exact_keys(lease, {
            "kind", "lease_id", "lease_token_sha256", "catalog_record_sha256",
            "cpu", "generation", "exclusive", "state",
        }, "CPU lease")
        cpu = lease.get("cpu")
        if type(cpu) is not int or cpu < 0:
            raise NativeLratPlanError("invalid leased CPU")
        lease_id = _identifier(lease.get("lease_id"), "lease id")
        if (
            lease.get("kind") != CPU_LEASE_KIND
            or lease.get("generation") != 0
            or lease.get("exclusive") is not True
            or lease.get("state") != "RESERVED"
        ):
            raise NativeLratPlanError("CPU lease is not an exclusive generation-zero reservation")
        lease_token = _sha256(lease.get("lease_token_sha256"), "lease token hash")
        catalog_hash = _sha256(lease.get("catalog_record_sha256"), "lease catalog hash")
        cnf = value.get("cnf_path")
        output = value.get("proof_output_path")
        if type(cnf) is not str or type(output) is not str:
            raise NativeLratPlanError("leaf paths must be strings")
        if cpu in cpus or lease_id in lease_ids or output in outputs:
            raise NativeLratPlanError("CPU, lease, and proof output must be exclusive per leaf")
        if output == cnf:
            raise NativeLratPlanError("proof output aliases its CNF")
        leaf_ids.add(leaf_id)
        cpus.add(cpu)
        lease_ids.add(lease_id)
        outputs.add(output)
        cnfs.add(cnf)
        normalised_leaves.append({
            "leaf_id": leaf_id,
            "cnf_path": cnf,
            "proof_output_path": output,
            "cpu_lease": {
                "kind": CPU_LEASE_KIND,
                "lease_id": lease_id,
                "lease_token_sha256": lease_token,
                "catalog_record_sha256": catalog_hash,
                "cpu": cpu,
                "generation": 0,
                "exclusive": True,
                "state": "RESERVED",
            },
        })
    if outputs & cnfs:
        raise NativeLratPlanError("a proof output aliases another participant's CNF")
    normalised_leaves.sort(key=lambda item: item["leaf_id"])
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": SPEC_KIND,
        "campaign_id": campaign_id,
        "launch_id": launch_id,
        "generation": 0,
        "fresh_leaf_generation": True,
        "resume": False,
        "checkpoint_source": None,
        "existing_proof_path": None,
        "existing_proof_format": None,
        "all_start_barrier": {
            "barrier_id": barrier_id,
            "timeout_seconds": timeout_seconds,
            "require_every_leaf": True,
        },
        "leaves": normalised_leaves,
    }


def build_plan(
    spec: Mapping[str, Any],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
    require_outputs_absent: bool = True,
) -> dict[str, Any]:
    """Build a deterministic, sealed, non-authoritative future launch plan."""

    request = _normalise_request(spec)
    toolchain = _toolchain_binding(pins)
    planner, _ = _bind_file(
        planner_path, role="native-lrat-planner-source-v1", cap=MAX_TOOL_BYTES,
        executable=False,
    )
    participants: list[dict[str, Any]] = []
    for index, leaf in enumerate(request["leaves"]):
        cnf = _bind_cnf(Path(leaf["cnf_path"]))
        proof = _proof_output_contract(
            leaf["proof_output_path"], require_absent=require_outputs_absent,
        )
        # CaDiCaL 1.9.5 passes its independent ``binary`` option to the LRAT
        # tracer.  The pinned legacy lrat-check parses ASCII with fscanf, so
        # ``--no-binary`` is part of the compatibility boundary, not an
        # optional presentation choice.
        solver_argv = [
            toolchain["solver"]["path"], "--lrat", "--no-binary",
            f"/proc/self/fd/{SOLVER_CNF_FD}",
            f"/proc/self/fd/{SOLVER_PROOF_FD}",
        ]
        checker_argv = [
            toolchain["lrat_checker"]["path"],
            f"/proc/self/fd/{CHECKER_CNF_FD}",
            f"/proc/self/fd/{CHECKER_PROOF_FD}",
        ]
        participants.append({
            "participant_index": index,
            "leaf_id": leaf["leaf_id"],
            "generation": 0,
            "cnf": cnf,
            "proof_output": proof,
            "cpu_lease": leaf["cpu_lease"],
            "solver_invocation": {
                "argv": solver_argv,
                "argv_sha256": _digest(solver_argv),
                "proof_format": "native-lrat",
                "environment_inheritance_permitted": False,
                "working_directory": proof["parent"]["path"],
                "literal_cnf_or_proof_path_in_argv_permitted": False,
                "pass_fds": [SOLVER_CNF_FD, SOLVER_PROOF_FD],
                "fd_bindings": {
                    "cnf": {
                        "fd": SOLVER_CNF_FD,
                        "proc_path": f"/proc/self/fd/{SOLVER_CNF_FD}",
                        "open_flags": ["O_CLOEXEC", "O_NOFOLLOW", "O_RDONLY"],
                        "expected_file": cnf,
                        "clear_fd_cloexec_only_immediately_before_exec": True,
                    },
                    "proof": {
                        "fd": SOLVER_PROOF_FD,
                        "proc_path": f"/proc/self/fd/{SOLVER_PROOF_FD}",
                        "open_flags": proof["creation_flags"],
                        "expected_literal_path": proof["path"],
                        "must_be_created_before_child_spawn": True,
                        "must_be_empty_at_preexec_barrier": True,
                        "hold_inode_anchor_through_solver_exit": True,
                        "clear_fd_cloexec_only_immediately_before_exec": True,
                    },
                },
            },
            "start_identity_contract": {
                "generation": 0,
                "pid_required": True,
                "proc_start_ticks_required": True,
                "pid_and_start_ticks_must_be_observed_while_preexec_gate_held": True,
                "exact_singleton_cpu_required": leaf["cpu_lease"]["cpu"],
                "lease_id": leaf["cpu_lease"]["lease_id"],
                "lease_token_sha256": leaf["cpu_lease"]["lease_token_sha256"],
                "proof_output_must_be_o_excl_created_before_spawn": True,
                "proof_output_fd": SOLVER_PROOF_FD,
                "proof_output_inode_identity_required": True,
                "proof_output_must_still_be_empty": True,
            },
            "certification_handoff_contract": {
                "solver_unsat_exit_code": 20,
                "proof_writer_must_be_quiescent": True,
                "proof_file_identity_and_sha256_must_be_sealed_after_exit": True,
                "initial_lrat_check": {
                    "argv": checker_argv,
                    "argv_sha256": _digest(checker_argv),
                    "pass_fds": [CHECKER_CNF_FD, CHECKER_PROOF_FD],
                    "literal_cnf_or_proof_path_in_argv_permitted": False,
                    "expected_returncode": 0,
                    "expected_semantic_stdout_sha256": pins.lrat_checker_semantic_stdout_sha256,
                    "timeout_seconds": pins.lrat_checker_timeout_seconds,
                    "max_proof_bytes": pins.lrat_checker_max_proof_bytes,
                },
                "fresh_lrat_replay": {
                    "argv": checker_argv,
                    "argv_sha256": _digest(checker_argv),
                    "pass_fds": [CHECKER_CNF_FD, CHECKER_PROOF_FD],
                    "literal_cnf_or_proof_path_in_argv_permitted": False,
                    "expected_returncode": 0,
                    "expected_semantic_stdout_sha256": pins.lrat_checker_semantic_stdout_sha256,
                    "timeout_seconds": pins.lrat_checker_timeout_seconds,
                    "max_proof_bytes": pins.lrat_checker_max_proof_bytes,
                    "distinct_process_identity_from_initial_check_required": True,
                    "reopen_cnf_and_proof_from_sealed_paths_required": True,
                },
                "checker_fd_contract": {
                    "cnf_fd": CHECKER_CNF_FD,
                    "proof_fd": CHECKER_PROOF_FD,
                    "both_open_flags": ["O_CLOEXEC", "O_NOFOLLOW", "O_RDONLY"],
                    "clear_fd_cloexec_only_immediately_before_checker_exec": True,
                    "verify_exact_file_identity_before_and_after_each_check": True,
                },
                "existing_certification_layer_must_revalidate_all_bindings": True,
                "this_plan_is_not_a_certificate": True,
            },
        })
    membership = [item["leaf_id"] for item in participants]
    plan = {
        "schema_version": SCHEMA_VERSION,
        "kind": PLAN_KIND,
        "authority": "PLAN_ONLY",
        "production_deployed": False,
        "request": request,
        "request_sha256": _digest(request),
        "planner_source": planner,
        "toolchain": toolchain,
        "compatibility_gate": {
            "new_leaf_only": True,
            "generation": 0,
            "native_proof_format": "lrat",
            "solver_options": ["--lrat", "--no-binary"],
            "resume_permitted": False,
            "dmtcp_checkpoint_input": None,
            "existing_proof_adoption_permitted": False,
            "proof_format_switch_mid_generation_permitted": False,
            "proof_append_permitted": False,
            "literal_cnf_or_proof_path_in_solver_argv_permitted": False,
            "exclusive_proof_inode_anchor_required": True,
        },
        "participants": participants,
        "all_start_barrier": {
            "barrier_id": request["all_start_barrier"]["barrier_id"],
            "membership": membership,
            "expected_receipt_count": len(membership),
            "timeout_seconds": request["all_start_barrier"]["timeout_seconds"],
            "preexec_gate_required": True,
            "release_before_complete_barrier_permitted": False,
            "release_requires_exact_live_pid_start_cpu_and_lease_revalidation": True,
            "rapid_exit_before_complete_barrier_action": "ABORT_GROUP_NO_AUTORETRY",
            "abandoned_empty_outputs_require_separate_audited_cleanup_before_new_launch_id": True,
            "partial_proof_output_authoritative": False,
        },
        "deployment_gate": {
            "candidate_schema_only": True,
            "launch_eligible": False,
            "production_eligible": False,
            "remaining_required_components": [
                "pinned-native-lrat-ascii-smoke-audit",
                "isolated-fresh-root-marker-and-legacy-dmtcp-session-checkpoint-denial",
                "cpu-lease-catalog-and-reservation-live-replay",
                "trusted-preexec-launcher-with-live-proc-and-lease-recheck",
                "sealed-elf-loader-and-dynamic-runtime-closure",
                "native-lrat-certification-adapter-with-two-real-checker-runs",
                "independent-review-and-versioned-production-manifest",
            ],
        },
        "publication_boundaries": {
            "starts_solver": False,
            "releases_preexec_gate": False,
            "runs_checker": False,
            "publishes_terminal": False,
            "publishes_aggregate": False,
            "deletes_or_cleans_data": False,
            "existing_certification_layer_is_only_terminal_authority": True,
        },
    }
    return seal(plan, "plan_sha256")


def verify_plan(
    plan: Mapping[str, Any],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
    require_prelaunch: bool = False,
) -> dict[str, Any]:
    """Rebuild a plan from its embedded request and compare every field."""

    if not selfhash_valid(plan, "plan_sha256"):
        raise NativeLratPlanError("launch plan seal is invalid")
    if plan.get("schema_version") != SCHEMA_VERSION or plan.get("kind") != PLAN_KIND:
        raise NativeLratPlanError("unsupported launch plan")
    request = plan.get("request")
    if type(request) is not dict:
        raise NativeLratPlanError("launch plan request is missing")
    expected = build_plan(
        request, pins=pins, planner_path=planner_path,
        require_outputs_absent=require_prelaunch,
    )
    if plan != expected:
        raise NativeLratPlanError("launch plan does not match current pinned inputs")
    return dict(plan)


def build_start_receipt(
    plan: Mapping[str, Any],
    observation: Mapping[str, Any],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
) -> dict[str, Any]:
    """Seal a launcher's pre-exec observation without releasing the process."""

    verified = verify_plan(plan, pins=pins, planner_path=planner_path)
    _expect_exact_keys(observation, {
        "schema_version", "kind", "plan_sha256", "leaf_id", "generation",
        "pid", "proc_start_ticks", "cpu", "lease_id", "lease_token_sha256",
        "planned_argv_sha256", "preexec_gate_held", "proof_output_binding",
        "proof_fd", "proof_fd_o_excl_anchor_held",
    }, "pre-exec observation")
    if (
        observation.get("schema_version") != SCHEMA_VERSION
        or observation.get("kind") != PREEXEC_OBSERVATION_KIND
        or observation.get("plan_sha256") != verified["plan_sha256"]
        or observation.get("generation") != 0
        or observation.get("preexec_gate_held") is not True
        or observation.get("proof_fd") != SOLVER_PROOF_FD
        or observation.get("proof_fd_o_excl_anchor_held") is not True
    ):
        raise NativeLratPlanError("pre-exec observation violates the generation-zero gate")
    leaf_id = _identifier(observation.get("leaf_id"), "observed leaf id")
    matches = [item for item in verified["participants"] if item["leaf_id"] == leaf_id]
    if len(matches) != 1:
        raise NativeLratPlanError("pre-exec observation names an unknown leaf")
    participant = matches[0]
    proof_binding, _ = _bind_file(
        Path(participant["proof_output"]["path"]),
        role="exclusive-native-lrat-output",
        cap=0,
        executable=False,
    )
    if (
        proof_binding["mode"] != participant["proof_output"]["creation_mode"]
        or observation.get("proof_output_binding") != proof_binding
    ):
        raise NativeLratPlanError(
            "pre-exec proof inode is not the exact empty O_EXCL output"
        )
    pid = _positive_int(observation.get("pid"), "observed pid")
    if pid == 1:
        raise NativeLratPlanError("PID 1 cannot be a leaf solver")
    start_ticks = _positive_int(
        observation.get("proc_start_ticks"), "observed process start ticks",
    )
    lease = participant["cpu_lease"]
    if (
        observation.get("cpu") != lease["cpu"]
        or observation.get("lease_id") != lease["lease_id"]
        or observation.get("lease_token_sha256") != lease["lease_token_sha256"]
        or observation.get("planned_argv_sha256")
        != participant["solver_invocation"]["argv_sha256"]
    ):
        raise NativeLratPlanError("pre-exec observation does not match its plan/lease")
    receipt = {
        "schema_version": SCHEMA_VERSION,
        "kind": START_RECEIPT_KIND,
        "plan_sha256": verified["plan_sha256"],
        "barrier_id": verified["all_start_barrier"]["barrier_id"],
        "leaf_id": leaf_id,
        "participant_index": participant["participant_index"],
        "generation": 0,
        "pid": pid,
        "proc_start_ticks": start_ticks,
        "cpu": lease["cpu"],
        "lease_id": lease["lease_id"],
        "lease_token_sha256": lease["lease_token_sha256"],
        "planned_argv_sha256": participant["solver_invocation"]["argv_sha256"],
        "preexec_gate_held": True,
        "proof_fd": SOLVER_PROOF_FD,
        "proof_output_binding": proof_binding,
        "proof_fd_o_excl_anchor_held": True,
        "live_identity_recheck_required_before_release": True,
        "releases_process": False,
    }
    return seal(receipt, "start_receipt_sha256")


def _verify_start_receipt_against_plan(
    plan: Mapping[str, Any], receipt: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate a receipt structurally against an already verified plan.

    This pure validator intentionally does not read production ``/proc``.  The
    external launcher is required to repeat that live check immediately before
    releasing its pre-exec gate.
    """

    if not selfhash_valid(receipt, "start_receipt_sha256"):
        raise NativeLratPlanError("start receipt seal is invalid")
    if receipt.get("kind") != START_RECEIPT_KIND or receipt.get("schema_version") != 1:
        raise NativeLratPlanError("unsupported start receipt")
    if receipt.get("plan_sha256") != plan.get("plan_sha256"):
        raise NativeLratPlanError("start receipt belongs to another plan")
    matches = [
        item for item in plan.get("participants", [])
        if item.get("leaf_id") == receipt.get("leaf_id")
    ]
    if len(matches) != 1:
        raise NativeLratPlanError("start receipt names an unknown leaf")
    participant = matches[0]
    lease = participant["cpu_lease"]
    current_proof, _ = _bind_file(
        Path(participant["proof_output"]["path"]),
        role="exclusive-native-lrat-output",
        cap=0,
        executable=False,
    )
    if current_proof["mode"] != participant["proof_output"]["creation_mode"]:
        raise NativeLratPlanError("exclusive proof output mode changed before barrier")
    expected = {
        "schema_version": SCHEMA_VERSION,
        "kind": START_RECEIPT_KIND,
        "plan_sha256": plan["plan_sha256"],
        "barrier_id": plan["all_start_barrier"]["barrier_id"],
        "leaf_id": participant["leaf_id"],
        "participant_index": participant["participant_index"],
        "generation": 0,
        "pid": receipt.get("pid"),
        "proc_start_ticks": receipt.get("proc_start_ticks"),
        "cpu": lease["cpu"],
        "lease_id": lease["lease_id"],
        "lease_token_sha256": lease["lease_token_sha256"],
        "planned_argv_sha256": participant["solver_invocation"]["argv_sha256"],
        "preexec_gate_held": True,
        "proof_fd": SOLVER_PROOF_FD,
        "proof_output_binding": current_proof,
        "proof_fd_o_excl_anchor_held": True,
        "live_identity_recheck_required_before_release": True,
        "releases_process": False,
    }
    _positive_int(expected["pid"], "receipt pid")
    if expected["pid"] == 1:
        raise NativeLratPlanError("PID 1 cannot be a leaf solver")
    _positive_int(expected["proc_start_ticks"], "receipt start ticks")
    if receipt != seal(expected, "start_receipt_sha256"):
        raise NativeLratPlanError("start receipt fields do not match the plan")
    return dict(receipt)


def verify_start_receipt(
    plan: Mapping[str, Any],
    receipt: Mapping[str, Any],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
) -> dict[str, Any]:
    """Revalidate all static bindings before accepting a start receipt."""

    verified = verify_plan(
        plan, pins=pins, planner_path=planner_path,
    )
    return _verify_start_receipt_against_plan(verified, receipt)


def build_barrier_receipt(
    plan: Mapping[str, Any], receipts: Sequence[Mapping[str, Any]],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
) -> dict[str, Any]:
    """Seal all start receipts; this does not release any pre-exec gate."""

    verified = verify_plan(
        plan, pins=pins, planner_path=planner_path,
    )
    expected_members = verified.get("all_start_barrier", {}).get("membership")
    if type(expected_members) is not list:
        raise NativeLratPlanError("plan barrier membership is malformed")
    valid = [
        _verify_start_receipt_against_plan(verified, receipt) for receipt in receipts
    ]
    if len(valid) != len(expected_members):
        raise NativeLratPlanError("all-start barrier is incomplete")
    by_leaf = {item["leaf_id"]: item for item in valid}
    if len(by_leaf) != len(valid) or sorted(by_leaf) != sorted(expected_members):
        raise NativeLratPlanError("all-start barrier membership mismatch")
    process_identities = {(item["pid"], item["proc_start_ticks"]) for item in valid}
    if len(process_identities) != len(valid):
        raise NativeLratPlanError("start receipts reuse a process identity")
    ordered = [by_leaf[leaf] for leaf in expected_members]
    barrier = {
        "schema_version": SCHEMA_VERSION,
        "kind": BARRIER_KIND,
        "plan_sha256": verified["plan_sha256"],
        "barrier_id": verified["all_start_barrier"]["barrier_id"],
        "generation": 0,
        "membership": list(expected_members),
        "receipt_sha256s": [item["start_receipt_sha256"] for item in ordered],
        "pid_start_identities": [
            {"leaf_id": item["leaf_id"], "pid": item["pid"],
             "proc_start_ticks": item["proc_start_ticks"], "cpu": item["cpu"]}
            for item in ordered
        ],
        "all_start_receipts_complete": True,
        "releases_processes": False,
        "external_launcher_may_release_only_after_live_identity_cpu_and_lease_recheck": True,
        "rapid_exit_during_recheck_action": "ABORT_GROUP_NO_AUTORETRY",
    }
    return seal(barrier, "barrier_sha256")


def verify_barrier_receipt(
    plan: Mapping[str, Any], receipts: Sequence[Mapping[str, Any]],
    barrier: Mapping[str, Any],
    *,
    pins: ToolchainPins = DEFAULT_PINS,
    planner_path: Path = Path(__file__).resolve(),
) -> dict[str, Any]:
    if not selfhash_valid(barrier, "barrier_sha256"):
        raise NativeLratPlanError("barrier seal is invalid")
    expected = build_barrier_receipt(
        plan, receipts, pins=pins, planner_path=planner_path,
    )
    if barrier != expected:
        raise NativeLratPlanError("barrier does not match its start receipts")
    return dict(barrier)


def _atomic_publish_new(path: Path, payload: bytes) -> None:
    target = Path(path)
    if not target.is_absolute():
        raise NativeLratPlanError("output path must be absolute")
    parent = target.parent.resolve(strict=True)
    if parent / target.name != target:
        raise NativeLratPlanError("output path must be canonical")
    _bind_directory(parent, "record-output-parent")
    temporary = parent / f".{target.name}.tmp.{os.getpid()}.{uuid.uuid4().hex}"
    descriptor = -1
    try:
        descriptor = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise NativeLratPlanError("short record write")
            view = view[written:]
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        try:
            os.link(temporary, target, follow_symlinks=False)
        except FileExistsError as exc:
            raise NativeLratPlanError(f"refusing to replace existing record: {target}") from exc
        directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def publish_record(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_publish_new(path, canonical_bytes(value) + b"\n")


def _load_json(path: Path, role: str) -> dict[str, Any]:
    _binding, value = _read_json_file(path, role)
    return value


def _emit_or_publish(value: Mapping[str, Any], output: Path | None, dry_run: bool) -> None:
    if dry_run:
        sys.stdout.buffer.write(canonical_bytes(value) + b"\n")
        return
    if output is None:
        raise NativeLratPlanError("--output is required unless --dry-run is used")
    publish_record(output.resolve(strict=False), value)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    create = sub.add_parser("create-plan", help="build, but never execute, a native-LRAT plan")
    create.add_argument("--spec", type=Path, required=True)
    create.add_argument("--output", type=Path)
    create.add_argument("--dry-run", action="store_true")
    validate = sub.add_parser("validate-plan", help="replay every static plan binding")
    validate.add_argument("--plan", type=Path, required=True)
    validate.add_argument("--prelaunch", action="store_true")
    start = sub.add_parser("record-start", help="seal one externally observed pre-exec identity")
    start.add_argument("--plan", type=Path, required=True)
    start.add_argument("--observation", type=Path, required=True)
    start.add_argument("--output", type=Path)
    start.add_argument("--dry-run", action="store_true")
    barrier = sub.add_parser("seal-barrier", help="seal a complete set of start receipts")
    barrier.add_argument("--plan", type=Path, required=True)
    barrier.add_argument("--start-receipt", type=Path, action="append", required=True)
    barrier.add_argument("--output", type=Path)
    barrier.add_argument("--dry-run", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "create-plan":
            spec = _load_json(args.spec.resolve(strict=True), "native-lrat-launch-spec")
            result = build_plan(spec)
            _emit_or_publish(result, args.output, args.dry_run)
        elif args.command == "validate-plan":
            plan = _load_json(args.plan.resolve(strict=True), "native-lrat-launch-plan")
            result = verify_plan(plan, require_prelaunch=args.prelaunch)
            sys.stdout.write(
                f"PASS {result['plan_sha256']} participants={len(result['participants'])}\n"
            )
        elif args.command == "record-start":
            plan = _load_json(args.plan.resolve(strict=True), "native-lrat-launch-plan")
            observation = _load_json(
                args.observation.resolve(strict=True), "native-lrat-preexec-observation",
            )
            result = build_start_receipt(plan, observation)
            _emit_or_publish(result, args.output, args.dry_run)
        elif args.command == "seal-barrier":
            plan = _load_json(args.plan.resolve(strict=True), "native-lrat-launch-plan")
            receipts = [
                _load_json(path.resolve(strict=True), "native-lrat-start-receipt")
                for path in args.start_receipt
            ]
            result = build_barrier_receipt(plan, receipts)
            _emit_or_publish(result, args.output, args.dry_run)
        else:  # pragma: no cover - argparse owns this branch
            raise NativeLratPlanError("unknown command")
    except (NativeLratPlanError, OSError, RuntimeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
