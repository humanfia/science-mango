#!/usr/bin/env python3
"""Trusted tool-free structured answer-blind solver controller.

Unlike the legacy agent launcher, this controller never starts a model CLI or
gives a model a shell, filesystem, process, or host-IPC capability.  It sends
one canonical problem-only projection to an invocation-scoped model broker,
accepts one strict JSON submission, validates and scans all artifact bytes,
then atomically publishes the candidate, Lean source, and blueprint.

The provider client is deliberately injectable for unit tests.  Production
calls use the root controller's HTTP client and the broker's fixed public
dummy credential; the real provider credential remains in the broker worker.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import http.client
import importlib.util
import json
import os
import re
import pwd
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Mapping, NoReturn, Sequence
from urllib.parse import urlsplit


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
REQUEST_PROFILE = "tool_free_structured_solver_v1"
PUBLIC_DUMMY_TOKEN = "answer-blind-public-dummy-token"
SHA256 = re.compile(r"^[0-9a-f]{64}$")
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
SAFE_DECLARATION = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
MODELS: Mapping[str, tuple[str, str]] = {
    "gpt": ("openai", "gpt-5.6-sol"),
    "kimi-k3": ("moonshot", "kimi-k3"),
}
MAX_ARTIFACT_BYTES = 8 * 1024 * 1024
MAX_PROVIDER_RESPONSE_BYTES = 64 * 1024 * 1024
CODEX_STALE_ARG0_WARNING = (
    "WARNING: failed to clean up stale arg0 temp dirs: "
    "Directory not empty (os error 39)"
)
CODEX_DISABLED_HOST_CONFIRMATION = (
    "Code Mode is unavailable because code-mode host is disabled. "
    "Code mode will fail closed; enable `features.code_mode_host` and install "
    "`codex-code-mode-host`."
)
CODEX_TOOL_FREE_CONFIG = (
    "features.shell_tool=false", "features.unified_exec=false",
    "features.code_mode.enabled=false", "features.code_mode_host=false",
    "features.shell_snapshot=false",
    "features.view_image=false", 'web_search="disabled"',
    "features.plugins=false", "features.apps=false",
    "features.browser_use=false", "features.in_app_browser=false",
    "features.multi_agent=false", "features.skill_search=false",
    "features.skill_mcp_dependency_install=false",
    "features.computer_use=false", "features.image_generation=false",
)

LOGIN_PROXY_RECEIPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id", "target_id",
    "attempt", "model_id", "adapter", "proxy_binary_sha256", "codex_binary",
    "codex_version", "command_argv", "caller_body_sha256",
    "pre_registered_request", "upstream_origin", "upstream_status",
    "upstream_raw_sse", "normalized_response", "caller_header_names",
    "forwarded_header_names", "completed_event_count", "codex_exit_code",
    "codex_jsonl", "codex_stderr", "codex_last_message", "tool_events",
}

SUBMISSION_FIELDS = {
    "raw_result", "reported_result",
    "candidate_domain_derivation", "lean_declarations",
    "lean_source", "blueprint",
}
ATTEMPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "target_id", "attempt", "previous_attempt_sha256",
    "adapter", "adapter_provenance", "request_profile", "tools_enabled", "store", "problem_projection_sha256",
    "prior_diagnostics_sha256", "request", "response", "submission",
    "constructed_candidate_sha256", "staged_artifacts", "status",
    "diagnostics", "artifacts", "attempt_chain_sha256",
}
TARGET_FIELDS = {
    "id", "source_report", "adapter", "problem_projection_sha256",
    "prepared_blueprint", "attempts", "accepted_attempt",
    "final_artifacts", "target_chain_sha256",
}
RECEIPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "adapter", "request_profile", "tools_enabled", "store",
    "scope_ids", "bundle", "controller_binary_sha256", "transport",
    "targets", "source_first_precommit_sha256", "all_targets_finalized", "request_count",
    "request_response_chain_sha256",
}
SOURCE_FIRST_PRECOMMIT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "controller_binary_sha256", "input_inventory",
    "review_projection_sha256", "adapter_provenance", "adapter", "transport",
    "request", "response", "model_submission", "normalized_response_sha256",
    "request_response_chain_sha256", "status", "finalized_before_solver",
}

_PROHIBITED_LEAN = re.compile(
    r"\b(?:sorry|admit|axiom|constant|native_decide|sorryAx|unsafe|opaque)\b|"
    r"@\[(?:implemented_by|extern|csimp)\b"
)
_PROHIBITED_COMMAND = re.compile(
    r"(?m)@\[|^\s*attribute\b|"
    r"^\s*(?:local\s+)?(?:instance|notation|infix[lr]?|prefix|postfix)\b|"
    r"\b(?:syntax(?:_cat)?|macro(?:_rules)?|elab(?:_rules)?|"
    r"command_elab|term_elab|tactic|CommandElab|TermElab|Tactic|"
    r"Lean\.Elab|IO(?:\.|\b)|System(?:\.|\b)|process|spawn|"
    r"initialize|builtin_initialize|foreign|run_cmd|run_tac|run_term_elab|"
    r"include_str|include_bytes)\b|^\s*scoped\b|"
    r"^\s*#(?:eval|reduce|check|print|synth|guard|compile|lint)\b"
)
_IMPORT = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$")
_IMPORT_TOKEN = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_TRUSTED_IMPORT_ROOTS = {"Aesop", "Batteries", "Mathlib", "PhysLean", "IChO2026Chem"}


class StructuredSolverError(RuntimeError):
    pass


class ProviderInvocationError(StructuredSolverError):
    def __init__(self, message: str, *, receipt: Mapping[str, str]) -> None:
        super().__init__(message)
        self.receipt = dict(receipt)


def _fail(message: str) -> NoReturn:
    raise StructuredSolverError(message)


def _canonical(value: Any) -> bytes:
    return (
        json.dumps(
            value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _pretty(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def _sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _file_sha(path: Path) -> str:
    return _sha(path.read_bytes())


def _root_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        _fail(f"{label} must be a plain directory")
    root = path.resolve(strict=True)
    metadata = root.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable")
    return root


def _root_file(path: Path, *, label: str, private: bool = False) -> Path:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a plain file: {path}")
    result = path.resolve(strict=True)
    metadata = result.stat()
    forbidden = 0o077 if private else 0o022
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & forbidden:
        _fail(f"{label} ownership/mode is not trusted: {result}")
    return result


def _safe_relative(raw: object, *, label: str) -> str:
    value = str(raw)
    path = PurePosixPath(value)
    if (
        not value or "\\" in value or "\0" in value or path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        _fail(f"{label} is not a normalized project-relative path")
    return value


def _load_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StructuredSolverError(f"invalid {label}: {path}") from exc
    if not isinstance(value, dict):
        _fail(f"{label} must contain an object")
    return value


def _strict_object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            _fail(f"JSON object repeats key: {key}")
        value[key] = item
    return value


def _strict_json(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            payload.decode("utf-8", errors="strict"),
            object_pairs_hook=_strict_object_pairs,
            parse_constant=lambda item: _fail(f"{label} contains {item}"),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StructuredSolverError(f"{label} is not strict UTF-8 JSON") from exc
    if not isinstance(value, dict):
        _fail(f"{label} root must be an object")
    return value


def _codex_version_from_output(payload: bytes) -> str:
    """Parse the pinned CLI version while tolerating its one known warning."""

    try:
        lines = [line for line in payload.decode("utf-8", errors="strict").splitlines() if line]
    except UnicodeDecodeError as exc:
        raise StructuredSolverError("trusted Codex binary version probe is not UTF-8") from exc
    versions = [
        line for line in lines
        if re.fullmatch(r"codex-cli [0-9][A-Za-z0-9.+_-]*", line)
    ]
    warnings = [line for line in lines if line == CODEX_STALE_ARG0_WARNING]
    if (
        len(versions) != 1
        or len(warnings) > 1
        or len(lines) != len(versions) + len(warnings)
    ):
        _fail("trusted Codex binary version probe emitted unexpected output")
    return versions[0]


def _atomic_root_file(path: Path, payload: bytes, *, mode: int = 0o400) -> None:
    if path.exists() or path.is_symlink() or path.parent.is_symlink():
        _fail(f"controller artifact must be new: {path}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail(f"short controller write: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, mode)


def _strip_lean_comments_and_strings(source: str) -> str:
    chars = list(source)
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while index < len(chars):
        current = chars[index]
        following = chars[index + 1] if index + 1 < len(chars) else ""
        if line_comment:
            if current == "\n":
                line_comment = False
            else:
                chars[index] = " "
            index += 1
        elif block_depth:
            if current == "/" and following == "-":
                chars[index] = chars[index + 1] = " "
                block_depth += 1
                index += 2
            elif current == "-" and following == "/":
                chars[index] = chars[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if current != "\n":
                    chars[index] = " "
                index += 1
        elif in_string:
            if current != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
        elif current == "-" and following == "-":
            chars[index] = chars[index + 1] = " "
            line_comment = True
            index += 2
        elif current == "/" and following == "-":
            chars[index] = chars[index + 1] = " "
            block_depth = 1
            index += 2
        elif current == '"':
            chars[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    if block_depth or in_string:
        _fail("Lean source contains an unterminated comment/string")
    return "".join(chars)


def _validate_lean_source(source: object) -> bytes:
    if not isinstance(source, str) or not source.strip():
        _fail("lean_source must be a nonempty UTF-8 string")
    payload = source.encode("utf-8")
    if len(payload) > MAX_ARTIFACT_BYTES or b"\0" in payload:
        _fail("lean_source exceeds bounds or contains NUL")
    active = _strip_lean_comments_and_strings(source)
    prohibited = _PROHIBITED_LEAN.search(active) or _PROHIBITED_COMMAND.search(active)
    if prohibited:
        _fail(f"Lean source contains prohibited construction: {prohibited.group(0)!r}")
    imports: list[str] = []
    for match in _IMPORT.finditer(active):
        imports.extend(match.group(1).split())
    if not imports or any(
        not _IMPORT_TOKEN.fullmatch(module)
        or module.split(".", 1)[0] not in _TRUSTED_IMPORT_ROOTS
        for module in imports
    ):
        _fail("Lean source imports a non-sealed module or has no trusted import")
    return payload


def _construct_candidate(
    submission: Mapping[str, Any], *, target_id: str, blind_hash: str,
    source_entry: Mapping[str, Any],
) -> dict[str, Any]:
    """Build every provenance/policy/hash field outside the model boundary."""

    if set(submission) != SUBMISSION_FIELDS:
        _fail("structured submission fields differ from the strict schema")
    declarations = submission.get("lean_declarations")
    if (
        not isinstance(declarations, list) or len(declarations) != 2
        or any(
            not isinstance(item, str) or SAFE_DECLARATION.fullmatch(item) is None
            or "." not in item
            for item in declarations
        )
        or len(set(declarations)) != 2
    ):
        _fail("lean_declarations must contain two unique qualified names")
    raw = submission.get("raw_result")
    reported = submission.get("reported_result")
    derivation = submission.get("candidate_domain_derivation")
    if not isinstance(raw, Mapping) or not isinstance(reported, Mapping):
        _fail("raw_result and reported_result must be objects")
    if not isinstance(derivation, Mapping) or not derivation:
        _fail("candidate_domain_derivation must be a nonempty object")
    reporting_policy = source_entry.get("reporting_policy")
    measurement_policy = source_entry.get("measurement_policy")
    domain_policy = source_entry.get("candidate_domain_policy")
    if not all(isinstance(item, Mapping) and item for item in (
        reporting_policy, measurement_policy, domain_policy,
    )):
        _fail("problem projection lacks controller-owned policy fields")
    requested = source_entry.get("requested_outputs")
    if not isinstance(requested, list) or not requested:
        _fail("problem projection lacks requested outputs")
    if len(requested) > 1:
        result_kind = "symbolic"
    elif reported.get("value") is None:
        result_kind = "underdetermined"
    else:
        requested_kind = requested[0].get("kind") if isinstance(requested[0], Mapping) else None
        if requested_kind == "numeric":
            result_kind = "numeric"
        elif requested_kind == "classification":
            result_kind = "classification"
        else:
            result_kind = "symbolic"
    raw_copy = {key: value for key, value in raw.items() if value is not None}
    reported_copy = {key: value for key, value in reported.items() if value is not None}
    if reported.get("value") is None:
        reported_copy["value"] = None
    reported_copy["precision"] = reporting_policy.get("final_precision")
    reported_copy["rounding_rule"] = reporting_policy.get("tie_rule")
    candidate: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "phase": "solve",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "id": target_id,
        "blind_record_sha256": blind_hash,
        "result_kind": result_kind,
        "raw_result": raw_copy,
        "reported_result": reported_copy,
        "reporting_rule_source": dict(reporting_policy),
        "tolerance_provenance": {
            "measurement_policy": dict(measurement_policy),
            "derivation": {
                "kind": "controller_policy_binding",
                "source": "problem_projection.measurement_policy",
            },
        },
        "candidate_domain_provenance": {
            "candidate_domain_policy": dict(domain_policy),
            "derivation": dict(derivation),
        },
        "lean_declarations": list(declarations),
        "lean_result_contracts": [],
    }
    try:
        from archon.commands.loop.review_source_contract import (
            blind_result_payload_sha256,
            expected_nonnumeric_result_types,
            expected_numeric_result_types,
            lean_result_type_sha256,
        )

        expected = (
            expected_numeric_result_types(candidate)
            if candidate["result_kind"] == "numeric"
            else expected_nonnumeric_result_types(candidate)
        )
    except ImportError as exc:
        if os.environ.get("ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR") != "1":
            raise StructuredSolverError(
                "trusted result-contract constructor is unavailable"
            ) from exc
        expected = {"raw_result": "True", "reported_result": "True"}
        blind_result_payload_sha256 = lambda value, role: _sha(  # type: ignore[assignment]
            _canonical({"candidate": value, "role": role})
        )
        lean_result_type_sha256 = lambda value: _sha(  # type: ignore[assignment]
            str(value).encode("utf-8")
        )
    if expected is None:
        _fail("semantic submission cannot produce trusted Lean result contracts")
    candidate["lean_result_contracts"] = [
        {
            "role": role,
            "declaration": declaration,
            "expected_type": expected[role],
            "expected_type_sha256": lean_result_type_sha256(expected[role]),
            "result_payload_sha256": blind_result_payload_sha256(candidate, role),
        }
        for role, declaration in zip(
            ("raw_result", "reported_result"), declarations, strict=True,
        )
    ]
    return candidate


def _validate_submission_shape(submission: object) -> dict[str, Any]:
    """Validate the provider-owned envelope before publishing its locator.

    A response whose JSON text is malformed at this layer is still retained as
    a rejected provider response, but it is not mislabeled as a transport
    failure and no invalid ``submission`` locator is emitted.
    """

    if not isinstance(submission, dict) or set(submission) != SUBMISSION_FIELDS:
        _fail("structured submission fields differ from the strict schema")
    for field in ("raw_result", "reported_result", "candidate_domain_derivation"):
        if not isinstance(submission.get(field), Mapping):
            _fail(f"structured submission.{field} must be an object")
    declarations = submission.get("lean_declarations")
    if (
        not isinstance(declarations, list)
        or len(declarations) != 2
        or len(set(declarations)) != 2
        or any(
            not isinstance(item, str)
            or SAFE_DECLARATION.fullmatch(item) is None
            or "." not in item
            for item in declarations
        )
    ):
        _fail("structured submission lean_declarations are invalid")
    for field in ("lean_source", "blueprint"):
        value = submission.get(field)
        if (
            not isinstance(value, str) or not value.strip() or "\0" in value
            or len(value.encode("utf-8")) > MAX_ARTIFACT_BYTES
        ):
            _fail(f"structured submission.{field} is invalid or oversized")
    return submission


def _validate_candidate(
    candidate: object, *, target_id: str, blind_hash: str,
    source_entry: Mapping[str, Any],
) -> bytes:
    if not isinstance(candidate, dict):
        _fail("constructed candidate must be an object")
    required = {
        "schema_version", "protocol", "phase", "evaluation_mode",
        "official_answer_seen", "id", "blind_record_sha256", "result_kind",
        "raw_result", "reported_result", "reporting_rule_source",
        "tolerance_provenance", "candidate_domain_provenance",
        "lean_declarations", "lean_result_contracts",
    }
    if set(candidate) != required:
        _fail("candidate fields differ from the answer-blind contract")
    if (
        candidate.get("schema_version") != 1
        or candidate.get("protocol") != PROTOCOL
        or candidate.get("phase") != "solve"
        or candidate.get("evaluation_mode") != "answer_blind"
        or candidate.get("official_answer_seen") is not False
        or candidate.get("id") != target_id
        or candidate.get("blind_record_sha256") != blind_hash
    ):
        _fail("candidate provenance differs from the target projection")
    declarations = candidate.get("lean_declarations")
    if (
        not isinstance(declarations, list) or not declarations
        or any(not isinstance(item, str) or not SAFE_DECLARATION.fullmatch(item) for item in declarations)
        or len(declarations) != len(set(declarations))
    ):
        _fail("candidate Lean declarations are invalid")
    payload = _canonical(candidate)
    if len(payload) > MAX_ARTIFACT_BYTES:
        _fail("candidate exceeds byte limit")
    # Use the same trusted semantic/result-contract validators that freeze and
    # the final verifier use.  This prevents a shallow outer-schema check from
    # admitting malformed tolerance provenance or result payload contracts.
    if os.environ.get("ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR") == "1":
        return payload
    try:
        from archon.commands import blind_evaluation as blind

        blind._validate_candidate(
            candidate, expected_id=target_id, expected_blind_hash=blind_hash
        )
        blind._validate_candidate_source_policies(
            candidate, source_entry=source_entry, record_id=target_id
        )
    except ImportError:
        raise StructuredSolverError(
            "trusted answer-blind candidate validator is unavailable"
        )
    except Exception as exc:
        if exc.__class__.__name__ != "BlindEvaluationError":
            raise
        raise StructuredSolverError(f"candidate semantic validation failed: {exc}") from exc
    return payload


def _validate_blueprint(value: object) -> bytes:
    if not isinstance(value, str) or not value.strip():
        _fail("blueprint must be a nonempty string")
    payload = value.encode("utf-8")
    if len(payload) > MAX_ARTIFACT_BYTES or b"\0" in payload:
        _fail("blueprint exceeds bounds or contains NUL")
    if re.search(r"(?i)\b(?:sorry|autoformaliz(?:e|ation))\b", value):
        _fail("blueprint contains obsolete sorry/autoformalization boilerplate")
    return payload


def _validated_prepared_blueprint(
    *, payload: bytes, target_relative: str,
    source_report_relative: str,
) -> str:
    if len(payload) > MAX_ARTIFACT_BYTES:
        _fail("prepared problem-only blueprint exceeds byte limit")
    try:
        base = payload.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise StructuredSolverError("prepared blueprint is not UTF-8") from exc
    begin = "% --- Archon physics formalization source begin ---"
    end = "% --- Archon physics formalization source end ---"
    formalization = "\\paragraph{Formalization target.}"
    required = (
        begin, end, f"% archon:covers {target_relative}",
        f"% archon:source-report {source_report_relative}",
        "\\paragraph{Problem source.}", formalization,
    )
    stripped = base.strip()
    if (
        base.count(begin) != 1 or base.count(end) != 1
        or not stripped.startswith(begin) or not stripped.endswith(end)
        or any(base.count(marker) != 1 for marker in required)
        or "\\paragraph{Recorded answer/context.}" in base
    ):
        _fail("prepared blueprint is not the canonical problem-only source block")
    proof_begin = "% --- Answer-blind structured proof begin ---"
    proof_end = "% --- Answer-blind structured proof end ---"
    if proof_begin in base or proof_end in base:
        _fail("prepared blueprint already contains a structured proof block")
    # Drop the old autoformalize/sorry target theorem entirely.  The prepared
    # locator retains its original bytes; the pure composition rule keeps only
    # the problem-side prefix and restores the trusted end marker.
    problem_only = stripped[:stripped.index(formalization)].rstrip()
    return problem_only + "\n" + end


def _compose_blueprint(
    *, generated: object, prepared_payload: bytes | None,
    target_relative: str, source_report_relative: str,
) -> bytes:
    generated_payload = _validate_blueprint(generated)
    if prepared_payload is None:
        return generated_payload
    stripped = _validated_prepared_blueprint(
        payload=prepared_payload, target_relative=target_relative,
        source_report_relative=source_report_relative,
    )
    proof_begin = "% --- Answer-blind structured proof begin ---"
    proof_end = "% --- Answer-blind structured proof end ---"
    combined = (
        stripped.encode("utf-8") + b"\n\n" + proof_begin.encode("ascii")
        + b"\n" + generated_payload.rstrip() + b"\n" + proof_end.encode("ascii") + b"\n"
    )
    if len(combined) > MAX_ARTIFACT_BYTES:
        _fail("composed blueprint exceeds byte limit")
    # Keep this composition function self-validating so the freeze controller
    # can replay it from the archived prepared bytes and the accepted minimal
    # submission without relying on a later, mutable workspace read.
    return _validate_blueprint(combined.decode("utf-8", errors="strict"))


def _bundle_rows(bundle_path: Path) -> tuple[bytes, dict[str, dict[str, Any]]]:
    payload = _root_file(bundle_path, label="blind bundle").read_bytes()
    rows: dict[str, dict[str, Any]] = {}
    for line_number, line in enumerate(payload.splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise StructuredSolverError(f"invalid blind bundle line {line_number}") from exc
        if not isinstance(row, dict):
            _fail(f"blind bundle line {line_number} is not an object")
        target_id = row.get("id")
        if not isinstance(target_id, str) or SAFE_ID.fullmatch(target_id) is None:
            _fail(f"blind bundle line {line_number} has invalid id")
        if target_id in rows:
            _fail(f"blind bundle has duplicate id {target_id}")
        if row.get("official_answer_seen") is not False:
            _fail(f"blind bundle row {target_id} is not answer-blind")
        rows[target_id] = row
    if not rows:
        _fail("blind bundle is empty")
    return payload, rows


def _source_reports(
    workspace: Path, *, rows: Mapping[str, Mapping[str, Any]], scope_ids: Sequence[str],
) -> dict[str, tuple[Path, dict[str, Any], bytes]]:
    root = workspace / "reports"
    if root.is_symlink() or not root.is_dir():
        _fail("structured workspace has no plain source-report directory")
    result: dict[str, tuple[Path, dict[str, Any], bytes]] = {}
    for path in sorted(root.rglob("*.source.json")):
        if path.is_symlink() or not path.is_file():
            _fail(f"structured source report is unsafe: {path}")
        payload = path.read_bytes()
        report = _strict_json(payload, label="source report")
        entry = report.get("entry")
        target_id = entry.get("id") if isinstance(entry, Mapping) else None
        if target_id not in scope_ids:
            continue
        if target_id in result:
            _fail(f"duplicate structured source report: {target_id}")
        row = rows[target_id]
        for field in (
            "id", "current_question", "shared_context", "previous_parts", "images",
            "problem_assets", "requested_outputs", "reporting_policy",
            "measurement_policy", "candidate_domain_policy",
        ):
            if entry.get(field) != row.get(field):
                _fail(f"source report {target_id} differs from blind bundle field {field}")
        if report.get("blind_record_sha256") != _sha(_canonical(row)):
            _fail(f"source report {target_id} blind hash differs from bundle")
        _safe_relative(report.get("output_lean"), label="source report output_lean")
        result[target_id] = (path.resolve(), report, payload)
    if sorted(result) != sorted(scope_ids):
        _fail("source-report set differs from structured scope")
    return result


def _problem_projection(row: Mapping[str, Any]) -> dict[str, Any]:
    fields = (
        "schema_version", "protocol", "evaluation_mode", "official_answer_seen",
        "id", "current_question", "shared_context", "previous_parts", "images",
        "problem_assets", "requested_outputs", "reporting_policy",
        "measurement_policy", "candidate_domain_policy",
    )
    projection = {key: row.get(key) for key in fields}
    projection["phase"] = "structured_solve"
    # This is a content-address, not an answer.  Supplying it prevents the
    # model from guessing a controller-only binding that every candidate must
    # carry exactly, while still deriving it solely from visible problem data.
    projection["blind_record_sha256"] = _sha(_canonical(row))
    if (
        projection["evaluation_mode"] != "answer_blind"
        or projection["official_answer_seen"] is not False
        or not isinstance(projection["requested_outputs"], list)
        or not projection["requested_outputs"]
    ):
        _fail("problem projection lacks answer-blind requested-output authority")
    return projection


def _image_parts(
    *, row: Mapping[str, Any], asset_root: Path,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    gpt: list[dict[str, Any]] = []
    kimi: list[dict[str, Any]] = []
    for asset in row.get("problem_assets", []):
        if not isinstance(asset, Mapping) or asset.get("kind") != "problem_page":
            continue
        relative = _safe_relative(asset.get("path"), label="problem image")
        if len(PurePosixPath(relative).parts) != 1:
            _fail("problem image path must be a bundle basename")
        path = _root_file(asset_root / relative, label="problem image")
        payload = path.read_bytes()
        if _sha(payload) != asset.get("sha256"):
            _fail(f"problem image hash drift: {relative}")
        mime = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".webp": "image/webp"}.get(path.suffix.lower())
        if mime is None:
            _fail(f"unsupported problem image type: {relative}")
        encoded = base64.b64encode(payload).decode("ascii")
        gpt.append({"type": "input_image", "image_url": f"data:{mime};base64,{encoded}"})
        kimi.append({"type": "image", "source": {"type": "base64", "media_type": mime, "data": encoded}})
    return gpt, kimi


def _result_spec_schema(output: Mapping[str, Any]) -> dict[str, Any]:
    kind = str(output.get("kind") or "")
    underdetermined = {
        "type": "object",
        "properties": {
            "kind": {"const": kind}, "status": {"const": "underdetermined"},
            "reason": {"type": "string", "minLength": 1},
            "remaining_constraints": {
                "type": "array", "minItems": 1,
                "items": {"type": "string", "minLength": 1},
            },
        },
        "required": ["kind", "status", "reason", "remaining_constraints"],
        "additionalProperties": False,
    }
    numeric_text = {"type": "string", "pattern": r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?(?:/[1-9]\d*)?$"}
    common = {
        "kind": {"const": kind}, "status": {"const": "derived"},
    }
    if kind == "numeric":
        derived = {
            "type": "object",
            "properties": {
                **common,
                "raw_expression": {"type": "string", "minLength": 1},
                "raw_value": numeric_text,
                "certified_interval": {
                    "type": "object",
                    "properties": {"lower": numeric_text, "upper": numeric_text},
                    "required": ["lower", "upper"], "additionalProperties": False,
                },
                "reported_value": numeric_text, "reporting_quantum": numeric_text,
                "tie_rule": {"type": "string", "minLength": 1},
            },
            "required": [
                "kind", "status", "raw_expression", "raw_value",
                "certified_interval", "reported_value", "reporting_quantum", "tie_rule",
            ],
            "additionalProperties": False,
        }
    elif kind == "integer":
        derived = {
            "type": "object",
            "properties": {
                **common, "value": {"type": "string", "pattern": r"^-?\d+$"},
                "proposition": {"type": "string", "minLength": 1},
                "constraints": {"type": "array", "minItems": 1, "items": {"type": "string", "minLength": 1}},
            },
            "required": ["kind", "status", "value", "proposition", "constraints"],
            "additionalProperties": False,
        }
    elif kind in {"formula", "classification"}:
        derived = {
            "type": "object",
            "properties": {
                **common, "normalized_result": {"type": "string", "minLength": 1},
                "proposition": {"type": "string", "minLength": 1},
                "constraints": {"type": "array", "minItems": 1, "items": {"type": "string", "minLength": 1}},
            },
            "required": ["kind", "status", "normalized_result", "proposition", "constraints"],
            "additionalProperties": False,
        }
    elif kind == "finite_set":
        derived = {
            "type": "object",
            "properties": {
                **common,
                "normalized_members": {"type": "array", "minItems": 1, "items": {"type": "string", "minLength": 1}},
                "proposition": {"type": "string", "minLength": 1},
                "constraints": {"type": "array", "minItems": 1, "items": {"type": "string", "minLength": 1}},
            },
            "required": ["kind", "status", "normalized_members", "proposition", "constraints"],
            "additionalProperties": False,
        }
    else:
        _fail(f"requested output has unsupported kind {kind!r}")
    return {"anyOf": [derived, underdetermined]}


def submission_json_schema(
    projection: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Strict model-owned semantic fields; provenance is controller-owned."""

    requested = projection.get("requested_outputs") if projection is not None else None
    multi = isinstance(requested, list) and len(requested) > 1
    numeric = (
        isinstance(requested, list) and len(requested) == 1
        and isinstance(requested[0], Mapping) and requested[0].get("kind") == "numeric"
    )
    if multi:
        raw_value: dict[str, Any] = {
            "type": "object",
            "properties": {
                str(output["id"]): _result_spec_schema(output)
                for output in requested if isinstance(output, Mapping)
            },
            "required": [str(output["id"]) for output in requested if isinstance(output, Mapping)],
            "additionalProperties": False,
        }
        reported_value: dict[str, Any] = {
            "type": "object",
            "properties": {
                str(output["id"]): {
                    "type": "object",
                    "properties": {
                        "status": {"enum": ["derived", "underdetermined"]},
                        "value": {"type": ["string", "integer", "null"]},
                    },
                    "required": ["status", "value"], "additionalProperties": False,
                }
                for output in requested if isinstance(output, Mapping)
            },
            "required": [str(output["id"]) for output in requested if isinstance(output, Mapping)],
            "additionalProperties": False,
        }
    else:
        numeric_text = {"type": ["string", "null"]}
        raw_value = numeric_text if numeric else {"type": ["string", "integer", "null"]}
        reported_value = numeric_text if numeric else {"type": ["string", "integer", "null"]}
    return {
        "type": "object",
        "properties": {
            "raw_result": {
                "type": "object",
                "properties": {
                    "expression": {"type": "string", "minLength": 1},
                    "lean_expression": {"type": "string", "minLength": 1},
                    "derivation_spec": {"type": ["string", "null"]},
                    "certified_interval": {
                        "anyOf": [
                            {"type": "null"},
                            {
                                "type": "object",
                                "properties": {
                                    "lower": {"type": "string"},
                                    "upper": {"type": "string"},
                                },
                                "required": ["lower", "upper"],
                                "additionalProperties": False,
                            },
                        ],
                    },
                    "value": raw_value,
                    "unit": {"type": ["string", "null"]},
                },
                "required": [
                    "expression", "lean_expression", "derivation_spec",
                    "certified_interval", "value", "unit",
                ],
                "additionalProperties": False,
            },
            "reported_result": {
                "type": "object",
                "properties": {
                    "value": reported_value,
                    "text": {"type": ["string", "null"]},
                    "lean_expression": {"type": "string", "minLength": 1},
                    "unit": {"type": ["string", "null"]},
                },
                "required": ["value", "text", "lean_expression", "unit"],
                "additionalProperties": False,
            },
            "candidate_domain_derivation": {
                "type": "object",
                "properties": {
                    "kind": {"type": "string", "minLength": 1},
                    "evidence": {
                        "type": "array", "minItems": 1,
                        "items": {"type": "string", "minLength": 1},
                    },
                    "depends_on": {
                        "type": "array", "items": {"type": "string"},
                    },
                },
                "required": ["kind", "evidence", "depends_on"],
                "additionalProperties": False,
            },
            "lean_declarations": {
                "type": "array", "minItems": 2, "maxItems": 2,
                "items": {"type": "string", "pattern": SAFE_DECLARATION.pattern},
            },
            "lean_source": {"type": "string", "maxLength": MAX_ARTIFACT_BYTES},
            "blueprint": {"type": "string", "maxLength": MAX_ARTIFACT_BYTES},
        },
        "required": sorted(SUBMISSION_FIELDS),
        "additionalProperties": False,
    }


def _prompt(
    *, projection: Mapping[str, Any], prior_diagnostics: Sequence[Mapping[str, Any]],
) -> str:
    return (
        "Produce a formalization from only the supplied problem projection. "
        "Do not retrieve or infer any official answer. Do not emit markdown. "
        "Return exactly the JSON submission schema. The Lean source must use only "
        "sealed imports and may not use metaprogramming, IO, unsafe declarations, "
        "axioms, sorry/admit, native_decide, run_cmd, or generated imports. "
        "Return only semantic result fields. Provenance, policy, and result-contract "
        "hashes are constructed by the trusted controller.\n"
        f"problem_projection={json.dumps(projection, ensure_ascii=False, sort_keys=True, separators=(',', ':'))}\n"
        f"prior_trusted_diagnostics={json.dumps(list(prior_diagnostics), ensure_ascii=False, sort_keys=True, separators=(',', ':'))}"
    )


def build_provider_request(
    *, variant: str, model: str, projection: Mapping[str, Any],
    gpt_images: Sequence[Mapping[str, Any]], kimi_images: Sequence[Mapping[str, Any]],
    prior_diagnostics: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    prompt = _prompt(projection=projection, prior_diagnostics=prior_diagnostics)
    if variant == "gpt":
        return {
            "model": model, "store": False, "tools": [],
            "tool_choice": "none", "stream": True,
            "reasoning": {"effort": "max", "summary": "auto"},
            "input": [{"role": "user", "content": [{"type": "input_text", "text": prompt}, *gpt_images]}],
            "text": {"format": {"type": "json_schema", "name": "answer_blind_submission", "strict": True, "schema": submission_json_schema(projection)}},
        }
    if variant == "kimi-k3":
        return {
            "model": model, "tools": [], "max_tokens": 131072,
            # The pinned Anthropic-compatible endpoint exposes no separate
            # reasoning-effort knob for this model.  Model id + maximum output
            # budget are therefore the complete supported inference controls.
            "messages": [{"role": "user", "content": [{"type": "text", "text": prompt}, *kimi_images]}],
        }
    _fail(f"unsupported variant: {variant}")


@dataclass(frozen=True)
class ProviderReply:
    raw_response: bytes
    submission: dict[str, Any]
    adapter: str = "structured_broker_http_v1"
    provenance: Mapping[str, Any] | None = None


ProviderCall = Callable[[str, Mapping[str, Any]], ProviderReply]
ProviderFactory = Callable[
    [str, int, Mapping[str, Any], Sequence[Path]], ProviderCall
]
Validator = Callable[[Mapping[str, bytes]], list[dict[str, Any]]]


class CleanLeanValidator:
    """Credential-free low-UID source-only Lean compilation for feedback."""

    def __init__(
        self, *, workspace: Path, target_relative: str, runtime_lake: Path,
        dependency_root: Path, verifier_user: str, scratch_root: Path,
        timeout_s: int = 600,
    ) -> None:
        self.workspace = workspace
        self.target_relative = _safe_relative(target_relative, label="validator target")
        self.runtime_lake = _root_file(runtime_lake, label="trusted Lake executable")
        self.runtime_lean = _root_file(
            self.runtime_lake.with_name("lean"), label="trusted Lean executable",
        )
        self.dependency_root = _root_directory(
            dependency_root, label="trusted Lean dependency tree"
        )
        dependency_paths: list[Path] = []
        for package in sorted(self.dependency_root.iterdir()):
            candidate = package / ".lake/build/lib/lean"
            if candidate.is_dir() and not candidate.is_symlink():
                dependency_paths.append(candidate.resolve(strict=True))
        if not dependency_paths:
            _fail("trusted dependency tree exposes no compiled Lean libraries")
        self.dependency_lean_paths = tuple(dependency_paths)
        identity = pwd.getpwnam(verifier_user)
        if identity.pw_uid == 0 or identity.pw_gid == 0:
            _fail("clean verifier must use a non-root identity")
        self.uid, self.gid = identity.pw_uid, identity.pw_gid
        self.scratch_root = _root_directory(scratch_root, label="verifier scratch root")
        self.timeout_s = timeout_s

    def _drop(self) -> None:
        os.setgroups([])
        os.setgid(self.gid)
        os.setuid(self.uid)

    def __call__(self, payloads: Mapping[str, bytes]) -> list[dict[str, Any]]:
        temporary = Path(
            tempfile.mkdtemp(prefix="structured-lean-", dir=self.scratch_root)
        )
        os.chmod(temporary, 0o755)
        try:
            project = temporary / "project"
            project.mkdir(mode=0o755)
            for relative in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "IChO2026Chem.lean"):
                source = self.workspace / relative
                if source.is_symlink() or not source.is_file():
                    continue
                target = project / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                os.chown(target, 0, 0)
                os.chmod(target, 0o444)
            chemistry = self.workspace / "IChO2026Chem"
            if chemistry.is_dir() and not chemistry.is_symlink():
                for source in sorted(chemistry.rglob("*.lean")):
                    if source.is_symlink() or not source.is_file():
                        _fail("sealed chemistry source tree contains unsafe entry")
                    target = project / source.relative_to(self.workspace)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, target)
                    os.chown(target, 0, 0)
                    os.chmod(target, 0o444)
            target = project.joinpath(*PurePosixPath(self.target_relative).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            candidate = _strict_json(payloads["candidate"], label="validator candidate")
            checks: list[str] = []
            for contract in candidate.get("lean_result_contracts", []):
                if not isinstance(contract, Mapping):
                    _fail("validator candidate has invalid result contract")
                declaration = str(contract.get("declaration") or "")
                expected_type = str(contract.get("expected_type") or "")
                if SAFE_DECLARATION.fullmatch(declaration) is None or not expected_type:
                    _fail("validator candidate has unsafe result contract")
                checks.append(f"#check ({declaration} : {expected_type})")
            target.write_bytes(
                payloads["lean"] + b"\n\n" + "\n".join(checks).encode("utf-8") + b"\n"
            )
            os.chown(target, 0, 0)
            os.chmod(target, 0o444)
            lake = project / ".lake"
            lake.mkdir(mode=0o755)
            packages = lake / "packages"
            packages.symlink_to(self.dependency_root, target_is_directory=True)
            for relative in (".lake/build", ".lake/config"):
                writable = project / relative
                writable.mkdir(parents=True, exist_ok=True)
                os.chown(writable, self.uid, self.gid)
                os.chmod(writable, 0o700)
            private = temporary / "private"
            private.mkdir(mode=0o700)
            os.chown(private, self.uid, self.gid)
            environment = {
                "HOME": str(private), "TMPDIR": str(private),
                "TMP": str(private), "TEMP": str(private),
                "PATH": str(self.runtime_lake.parent),
                "LEAN_PATH": os.pathsep.join([
                    str(project / ".lake/build/lib/lean"),
                    *(str(path) for path in self.dependency_lean_paths),
                ]),
                "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "TZ": "UTC",
            }
            # Compile the sealed support sources directly with Lean.  Invoking
            # `lake build` here would inspect package Git metadata and might
            # attempt dependency mutation/network access.  LEAN_PATH contains
            # only the sealed dependency oleans and this fresh build root.
            build_root = project / ".lake/build/lib/lean"
            support_sources = [
                project / "IChO2026Chem/Core.lean",
                project / "IChO2026Chem/Reporting.lean",
                project / "IChO2026Chem.lean",
            ]
            completed: subprocess.CompletedProcess[bytes] | None = None
            for support_source in support_sources:
                if not support_source.is_file():
                    _fail(f"sealed support source is missing: {support_source.name}")
                support_relative = support_source.relative_to(project).with_suffix(".olean")
                support_output = build_root / support_relative
                support_output.parent.mkdir(parents=True, exist_ok=True)
                os.chown(support_output.parent, self.uid, self.gid)
                os.chmod(support_output.parent, 0o700)
                completed = subprocess.run(
                    [str(self.runtime_lean), "-o", str(support_output), str(support_source)],
                    cwd=project, env=environment, stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    timeout=self.timeout_s, check=False, preexec_fn=self._drop,
                )
                if completed.returncode != 0:
                    break
            if completed is None or completed.returncode == 0:
                completed = subprocess.run(
                    [str(self.runtime_lean), str(target)],
                    cwd=project, env=environment, stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    timeout=self.timeout_s, check=False, preexec_fn=self._drop,
                )
            if completed.returncode == 0:
                return []
            text = completed.stdout.decode("utf-8", errors="replace")[-65536:]
            rows: list[dict[str, Any]] = []
            for line in text.splitlines()[-100:]:
                if not line.strip():
                    continue
                match = re.search(r":(\d+):(\d+):\s*(?:error:)?\s*(.*)", line)
                row: dict[str, Any] = {
                    "kind": "lean_compile",
                    "message": (match.group(3) if match else line).strip()[:8192],
                }
                if match:
                    row.update(line=int(match.group(1)), column=int(match.group(2)))
                rows.append(row)
            return rows or [{"kind": "lean_compile", "message": "Lean compilation failed"}]
        except subprocess.TimeoutExpired:
            return [{"kind": "lean_compile", "message": "Lean compilation timed out"}]
        finally:
            shutil.rmtree(temporary)


def _extract_gpt_submission(document: Mapping[str, Any]) -> dict[str, Any]:
    output = document.get("output")
    if not isinstance(output, list):
        _fail("GPT response output must be a list")
    messages: list[Mapping[str, Any]] = []
    for item in output:
        if not isinstance(item, Mapping):
            _fail("GPT response output items must be objects")
        item_type = item.get("type")
        if item_type == "message":
            if item.get("role") not in (None, "assistant"):
                _fail("GPT response message must have the assistant role")
            messages.append(item)
        elif isinstance(item_type, str) and any(
            token in item_type.lower()
            for token in ("tool", "function", "refusal")
        ):
            _fail("GPT response contains a tool, function, or refusal output")
    if len(messages) != 1:
        _fail("GPT response must contain exactly one assistant message")
    content = messages[0].get("content")
    if not isinstance(content, list) or not content:
        _fail("GPT response assistant message must contain output text")
    segments: list[str] = []
    for block in content:
        if (
            not isinstance(block, Mapping)
            or block.get("type") != "output_text"
            or not isinstance(block.get("text"), str)
        ):
            _fail("GPT response assistant message contains non-text content")
        segments.append(block["text"])
    return _strict_json(
        "".join(segments).encode("utf-8"), label="GPT assistant message text",
    )


def _bounded_gpt_response_structure(document: object) -> dict[str, Any]:
    """Describe a response envelope without copying any generated text."""

    output = document.get("output") if isinstance(document, Mapping) else None
    rows: list[dict[str, Any]] = []
    if isinstance(output, list):
        for item in output[:32]:
            if not isinstance(item, Mapping):
                rows.append({
                    "type": "<non-object>", "role": None,
                    "content_is_list": False, "content_item_count": 0,
                    "content_types": [], "omitted_content_items": 0,
                })
                continue
            content = item.get("content")
            content_types: list[str] = []
            if isinstance(content, list):
                for block in content[:32]:
                    kind = block.get("type") if isinstance(block, Mapping) else None
                    content_types.append(
                        kind[:64] if isinstance(kind, str) else "<non-object-or-type>"
                    )
            item_type = item.get("type")
            role = item.get("role")
            rows.append({
                "type": item_type[:64] if isinstance(item_type, str) else "<non-string>",
                "role": role[:64] if isinstance(role, str) else None,
                "content_is_list": isinstance(content, list),
                "content_item_count": len(content) if isinstance(content, list) else 0,
                "content_types": content_types,
                "omitted_content_items": max(0, len(content) - 32) if isinstance(content, list) else 0,
            })
    return {
        "document_is_object": isinstance(document, Mapping),
        "output_is_list": isinstance(output, list),
        "output_item_count": len(output) if isinstance(output, list) else 0,
        "items": rows,
        "omitted_output_items": max(0, len(output) - 32) if isinstance(output, list) else 0,
    }


def _extract_kimi_submission(document: Mapping[str, Any]) -> dict[str, Any]:
    texts = [
        item.get("text") for item in document.get("content", [])
        if isinstance(item, Mapping) and item.get("type") == "text" and isinstance(item.get("text"), str)
    ]
    if len(texts) != 1:
        _fail("Kimi response must contain exactly one text block")
    return _strict_json(texts[0].encode("utf-8"), label="Kimi text block")


def http_provider_call(url: str, request: Mapping[str, Any]) -> ProviderReply:
    parsed = urlsplit(url)
    if parsed.scheme != "http" or parsed.hostname != "127.0.0.1" or not parsed.port:
        _fail("structured solver broker must be an explicit IPv4 loopback URL")
    payload = _canonical(request).rstrip(b"\n")
    api_root = parsed.path.rstrip("/") or "/v1"
    endpoint = api_root + ("/responses" if "input" in request else "/messages")
    connection = http.client.HTTPConnection("127.0.0.1", parsed.port, timeout=900)
    connection.request(
        "POST", endpoint, body=payload,
        headers={"Authorization": f"Bearer {PUBLIC_DUMMY_TOKEN}", "Content-Type": "application/json", "Accept": "application/json"},
    )
    response = connection.getresponse()
    raw = response.read(MAX_PROVIDER_RESPONSE_BYTES + 1)
    connection.close()
    if response.status != 200 or len(raw) > MAX_PROVIDER_RESPONSE_BYTES:
        _fail(f"structured model broker request failed with HTTP {response.status}")
    document = _strict_json(raw, label="provider response")
    submission = _extract_gpt_submission(document) if "input" in request else _extract_kimi_submission(document)
    return ProviderReply(
        raw, submission, "structured_broker_http_v1",
        {
            "endpoint": endpoint, "request_sha256": _sha(payload),
            "raw_response_sha256": _sha(raw),
            "reasoning_control": (
                {"effort": "max", "summary": "auto"}
                if "input" in request else
                {
                    "provider_field_supported": False,
                    "model_id": request.get("model"),
                    "max_tokens": request.get("max_tokens"),
                }
            ),
        },
    )


def _load_login_proxy_module() -> Any:
    path = Path(__file__).with_name("run_answer_blind_chatgpt_login_proxy.py")
    name = "_answer_blind_chatgpt_login_proxy"
    existing = sys.modules.get(name)
    if existing is not None:
        return existing
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        _fail("trusted ChatGPT login proxy module is unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _load_model_broker_module() -> Any:
    path = Path(__file__).with_name("run_answer_blind_model_broker.py")
    name = "_answer_blind_model_broker"
    existing = sys.modules.get(name)
    if existing is not None:
        return existing
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        _fail("trusted structured model broker module is unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _seal_existing_root_file(path: Path, *, label: str) -> bytes:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} was not produced as a plain file")
    payload = path.read_bytes()
    os.chown(path, 0, 0)
    os.chmod(path, 0o400)
    return payload


def _codex_transport_message(payload: bytes) -> tuple[dict[str, Any], int]:
    messages: list[dict[str, Any]] = []
    events = 0
    tool_events = 0
    thread_started = False
    turn_started = False
    disabled_host_confirmations = 0
    for line in payload.splitlines():
        if not line.strip():
            continue
        event = _strict_json(line, label="Codex transport JSONL event")
        events += 1
        event_type = event.get("type")
        item = event.get("item")
        item_type = item.get("type") if isinstance(item, Mapping) else None
        if event_type == "thread.started":
            if thread_started or turn_started:
                _fail("Codex transport thread.started is duplicated or misplaced")
            thread_started = True
        elif event_type == "turn.started":
            if not thread_started or turn_started or disabled_host_confirmations != 1:
                _fail("Codex transport turn.started precedes its disabled-host confirmation")
            turn_started = True
        is_disabled_host_confirmation = (
            event_type == "item.completed"
            and isinstance(item, Mapping)
            and set(event) == {"type", "item"}
            and set(item) == {"id", "type", "message"}
            and isinstance(item.get("id"), str)
            and 0 < len(item["id"]) <= 128
            and item_type == "error"
            and item.get("message") == CODEX_DISABLED_HOST_CONFIRMATION
        )
        if is_disabled_host_confirmation:
            if not thread_started or turn_started or disabled_host_confirmations:
                _fail("Codex disabled-host confirmation is duplicated or misplaced")
            disabled_host_confirmations += 1
            continue
        if (
            (isinstance(event_type, str) and "error" in event_type.lower())
            or (isinstance(item_type, str) and "error" in item_type.lower())
            or event.get("error") not in (None, "", [], {})
        ):
            _fail("Codex transport emitted an error event")
        if isinstance(item_type, str) and any(
            token in item_type.lower()
            for token in ("tool", "function", "command", "web", "file_change", "mcp")
        ):
            tool_events += 1
        if event.get("type") == "item.completed" and item_type == "agent_message":
            if not turn_started:
                _fail("Codex transport message precedes turn.started")
            text = item.get("text")
            if isinstance(text, str) and text.strip():
                messages.append(_strict_json(text.encode("utf-8"), label="Codex transport message"))
    if (
        tool_events or len(messages) != 1 or not thread_started
        or not turn_started or disabled_host_confirmations != 1
    ):
        _fail("Codex transport emitted a tool event or not exactly one message")
    return messages[0], events


class ChatGPTLoginProxyAdapter:
    """Use Codex only to lend login headers to a controller-owned request."""

    def __init__(
        self, *, codex_binary: Path, codex_home: Path, controller: Path,
        target_id: str, attempt: int, run_id: str,
        runner: Callable[..., subprocess.CompletedProcess[bytes]] = subprocess.run,
        proxy_factory: Callable[..., Any] | None = None,
        timeout_s: int = 1800,
    ) -> None:
        self.binary = _root_file(codex_binary, label="trusted Codex binary")
        self.home = _root_directory(codex_home, label="trusted Codex login home")
        _root_file(self.home / "auth.json", label="Codex login material", private=True)
        self.controller = controller
        self.target_id = target_id
        self.attempt = attempt
        self.run_id = run_id
        self.runner = runner
        self.proxy_factory = proxy_factory
        self.timeout_s = timeout_s

    def __call__(self, _unused_url: str, request: Mapping[str, Any]) -> ProviderReply:
        if request.get("model") != MODELS["gpt"][1]:
            _fail("ChatGPT login proxy adapter received the wrong model")
        registered = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-request.json"
        if _root_file(registered, label="pre-registered GPT request", private=True).read_bytes() != _canonical(request):
            _fail("pre-registered GPT request differs from controller request")
        proxy_module = _load_login_proxy_module()
        factory = self.proxy_factory or proxy_module.OneShotLoginProxy
        proxy = factory(registered_request=registered, model=MODELS["gpt"][1])
        schema_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-schema.json"
        _atomic_root_file(schema_path, _pretty(request["text"]["format"]["schema"]))
        output_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-last-message.json"
        scratch = Path(tempfile.mkdtemp(prefix="answer-blind-codex-", dir=self.controller.parent))
        os.chown(scratch, 0, 0)
        os.chmod(scratch, 0o700)
        argv = [
            str(self.binary), "--strict-config", "exec", "--json", "--skip-git-repo-check",
            "--ignore-user-config", "--ignore-rules", "--ephemeral",
            "-m", MODELS["gpt"][1], "-s", "read-only",
            "--output-schema", str(schema_path), "-o", str(output_path),
            "-C", str(scratch),
            "-c", 'model_provider="answer_blind_login"',
            "-c", 'model_providers.answer_blind_login.name="Answer Blind Login"',
            "-c", f'model_providers.answer_blind_login.base_url="{proxy.base_url}/v1"',
            "-c", 'model_providers.answer_blind_login.wire_api="responses"',
            "-c", "model_providers.answer_blind_login.requires_openai_auth=true",
            *(item for setting in CODEX_TOOL_FREE_CONFIG for item in ("-c", setting)),
            "TRANSPORT_ONLY_REGISTERED_REQUEST",
        ]
        environment = {
            "HOME": str(scratch), "TMPDIR": str(scratch), "TMP": str(scratch),
            "TEMP": str(scratch), "CODEX_HOME": str(self.home),
            "PATH": str(self.binary.parent), "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8", "TZ": "UTC",
        }
        version_run = self.runner(
            [str(self.binary), "--version"], cwd=scratch, env=environment,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=30, check=False,
        )
        try:
            version = _codex_version_from_output(version_run.stdout)
        except StructuredSolverError:
            shutil.rmtree(scratch)
            raise
        if version_run.returncode != 0:
            shutil.rmtree(scratch)
            _fail("trusted Codex binary version probe failed")
        proxy.start()
        completed: subprocess.CompletedProcess[bytes] | None = None
        try:
            try:
                completed = self.runner(
                    argv, cwd=scratch, env=environment, stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    timeout=self.timeout_s, check=False,
                )
                exchange = proxy.wait(timeout=30)
            except BaseException as exc:
                stdout_locator = None
                stderr_locator = None
                if completed is not None:
                    stdout_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-codex.jsonl"
                    stderr_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-codex.stderr"
                    _atomic_root_file(stdout_path, completed.stdout)
                    _atomic_root_file(stderr_path, completed.stderr)
                    stdout_locator = {
                        "path": str(stdout_path), "sha256": _file_sha(stdout_path),
                    }
                    stderr_locator = {
                        "path": str(stderr_path), "sha256": _file_sha(stderr_path),
                    }
                evidence = getattr(proxy, "failure_evidence", None)
                raw_locator = None
                headers_locator = None
                structure = None
                if evidence is not None:
                    raw_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-upstream.sse"
                    headers_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-response-headers.json"
                    _atomic_root_file(raw_path, evidence.upstream_raw_response)
                    _atomic_root_file(headers_path, _pretty({
                        "header_names": list(evidence.response_header_names),
                        "upstream_status": evidence.upstream_status,
                    }))
                    raw_locator = {
                        "path": str(raw_path), "sha256": _file_sha(raw_path),
                    }
                    headers_locator = {
                        "path": str(headers_path), "sha256": _file_sha(headers_path),
                    }
                    structure = dict(evidence.response_structure)
                failure_locator = _transport_failure_locator(
                    controller=self.controller, variant="gpt",
                    target_id=self.target_id, attempt=self.attempt,
                    adapter="chatgpt_login_proxy_v1", request_path=registered,
                    request_sha256=_file_sha(registered),
                    diagnostic_stdout=stdout_locator,
                    diagnostic_stderr=stderr_locator,
                    upstream_raw_sse=raw_locator,
                    response_headers=headers_locator,
                    response_structure=structure,
                )
                raise ProviderInvocationError(
                    "ChatGPT login proxy transport failed",
                    receipt=failure_locator,
                ) from exc
        finally:
            proxy.close()
            shutil.rmtree(scratch)
        raw_sse_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-upstream.sse"
        normalized_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-normalized-response.json"
        jsonl_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-codex.jsonl"
        stderr_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-codex.stderr"
        # Seal every upstream and local transport channel before interpreting
        # any byte.  In particular, malformed envelopes remain auditable.
        _atomic_root_file(raw_sse_path, exchange.upstream_raw_sse)
        _atomic_root_file(normalized_path, exchange.normalized_response)
        _atomic_root_file(jsonl_path, completed.stdout)
        _atomic_root_file(stderr_path, completed.stderr)

        raw_sse_locator = {
            "path": str(raw_sse_path), "sha256": _file_sha(raw_sse_path),
        }
        normalized_locator = {
            "path": str(normalized_path), "sha256": _file_sha(normalized_path),
        }
        stdout_locator = {
            "path": str(jsonl_path), "sha256": _file_sha(jsonl_path),
        }
        stderr_locator = {
            "path": str(stderr_path), "sha256": _file_sha(stderr_path),
        }

        try:
            normalized = _strict_json(
                exchange.normalized_response, label="normalized GPT response",
            )
        except StructuredSolverError as exc:
            structure = _bounded_gpt_response_structure(None)
            failure_receipt = _transport_failure_locator(
                controller=self.controller, variant="gpt",
                target_id=self.target_id, attempt=self.attempt,
                adapter="chatgpt_login_proxy_v1", request_path=registered,
                request_sha256=_file_sha(registered),
                diagnostic_stdout=stdout_locator,
                diagnostic_stderr=stderr_locator,
                upstream_raw_sse=raw_sse_locator,
                normalized_response=normalized_locator,
                response_structure=structure,
            )
            raise ProviderInvocationError(
                "normalized GPT response failed strict JSON validation",
                receipt=failure_receipt,
            ) from exc
        structure = _bounded_gpt_response_structure(normalized)

        def fail_bound(message: str, cause: BaseException | None = None) -> NoReturn:
            failure_receipt = _transport_failure_locator(
                controller=self.controller, variant="gpt",
                target_id=self.target_id, attempt=self.attempt,
                adapter="chatgpt_login_proxy_v1", request_path=registered,
                request_sha256=_file_sha(registered),
                diagnostic_stdout=stdout_locator,
                diagnostic_stderr=stderr_locator,
                upstream_raw_sse=raw_sse_locator,
                normalized_response=normalized_locator,
                response_structure=structure,
            )
            error = ProviderInvocationError(message, receipt=failure_receipt)
            if cause is None:
                raise error
            raise error from cause

        if completed.returncode != 0:
            fail_bound(f"Codex login transport exited {completed.returncode}")
        try:
            transport_message, event_count = _codex_transport_message(completed.stdout)
        except StructuredSolverError as exc:
            fail_bound(
                "Codex transport stdout failed strict JSONL validation", exc,
            )
        try:
            last_payload = _seal_existing_root_file(
                output_path, label="Codex last message",
            )
            last_message = _strict_json(last_payload, label="Codex last message")
            submission = _extract_gpt_submission(normalized)
        except StructuredSolverError as exc:
            fail_bound("GPT response extraction failed", exc)
        if transport_message != submission or last_message != submission:
            fail_bound("Codex transport output differs from normalized upstream response")
        receipt = {
            "schema_version": 1, "protocol": PROTOCOL,
            "phase": "chatgpt_login_proxy_exchange", "variant": "gpt",
            "run_id": self.run_id, "target_id": self.target_id,
            "attempt": self.attempt, "model_id": MODELS["gpt"][1],
            "adapter": "chatgpt_login_proxy_v1",
            "proxy_binary_sha256": _file_sha(Path(proxy_module.__file__).resolve()),
            "codex_binary": {"path": str(self.binary), "sha256": _file_sha(self.binary)},
            "codex_version": version, "command_argv": argv,
            "caller_body_sha256": exchange.caller_body_sha256,
            "pre_registered_request": {"path": str(registered), "sha256": exchange.forwarded_request_sha256},
            "upstream_origin": "https://chatgpt.com",
            "upstream_status": exchange.upstream_status,
            "upstream_raw_sse": {"path": str(raw_sse_path), "sha256": _file_sha(raw_sse_path)},
            "normalized_response": {"path": str(normalized_path), "sha256": _file_sha(normalized_path)},
            "caller_header_names": list(exchange.caller_header_names),
            "forwarded_header_names": list(exchange.forwarded_header_names),
            "completed_event_count": exchange.completed_event_count,
            "codex_exit_code": completed.returncode,
            "codex_jsonl": {"path": str(jsonl_path), "sha256": _file_sha(jsonl_path)},
            "codex_stderr": {"path": str(stderr_path), "sha256": _file_sha(stderr_path)},
            "codex_last_message": {"path": str(output_path), "sha256": _file_sha(output_path)},
            "tool_events": 0,
        }
        if set(receipt) != LOGIN_PROXY_RECEIPT_FIELDS:
            _fail("internal ChatGPT login proxy receipt schema drift")
        receipt_path = self.controller / f"gpt-{self.target_id}-attempt-{self.attempt}-login-proxy-receipt.json"
        _atomic_root_file(receipt_path, _pretty(receipt))
        return ProviderReply(
            exchange.normalized_response, submission, "chatgpt_login_proxy_v1",
            {
                "proxy_receipt": {"path": str(receipt_path), "sha256": _file_sha(receipt_path)},
                "normalized_response_sha256": _sha(exchange.normalized_response),
                "upstream_raw_sse_sha256": _sha(exchange.upstream_raw_sse),
                "event_count": event_count,
            },
        )


def _artifact_paths(
    workspace: Path, *, report: Mapping[str, Any], target_id: str,
) -> dict[str, Path]:
    target = _safe_relative(report.get("output_lean"), label="Lean target")
    if not target.endswith(".lean"):
        _fail("Lean target must use .lean")
    parts = PurePosixPath(target).with_suffix("").parts
    return {
        "candidate": workspace / "blind_candidates" / f"{target_id}.json",
        "lean": workspace.joinpath(*PurePosixPath(target).parts),
        "blueprint": workspace / "blueprint/src/chapters" / ("_".join(parts) + ".tex"),
    }


def _publish_artifacts(
    paths: Mapping[str, Path], payloads: Mapping[str, bytes],
    *, prepared_blueprint_sha256: str | None,
) -> None:
    for name, path in paths.items():
        if name == "blueprint" and prepared_blueprint_sha256 is not None:
            if (
                path.is_symlink() or not path.is_file()
                or _file_sha(path) != prepared_blueprint_sha256
            ):
                _fail("prepared blueprint drifted before atomic publication")
            continue
        if path.exists() or path.is_symlink():
            _fail(f"structured artifact must be new: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.parent.is_symlink():
            _fail(f"structured artifact parent is a symlink: {path.parent}")
    created: list[Path] = []
    try:
        for name in ("candidate", "lean", "blueprint"):
            path = paths[name]
            destination = path
            if name == "blueprint" and prepared_blueprint_sha256 is not None:
                destination = path.with_name(f".{path.name}.structured-{os.getpid()}.tmp")
            descriptor = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                view = memoryview(payloads[name])
                while view:
                    written = os.write(descriptor, view)
                    if written <= 0:
                        _fail(f"short structured artifact write: {destination}")
                    view = view[written:]
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            os.chown(destination, 0, 0)
            os.chmod(destination, 0o400)
            if destination != path:
                if _file_sha(path) != prepared_blueprint_sha256:
                    destination.unlink(missing_ok=True)
                    _fail("prepared blueprint drifted during atomic publication")
                os.replace(destination, path)
            else:
                created.append(path)
    except BaseException:
        for path in created:
            path.unlink(missing_ok=True)
        for name, path in paths.items():
            if name == "blueprint" and prepared_blueprint_sha256 is not None:
                path.with_name(
                    f".{path.name}.structured-{os.getpid()}.tmp"
                ).unlink(missing_ok=True)
        raise


def _normalize_diagnostics(value: object) -> list[dict[str, Any]]:
    if not isinstance(value, list) or len(value) > 200:
        _fail("validator diagnostics must be a bounded list")
    normalized: list[dict[str, Any]] = []
    for index, item in enumerate(value):
        if not isinstance(item, Mapping):
            _fail(f"validator diagnostic {index} must be an object")
        allowed = {"kind", "message", "line", "column"}
        if set(item) - allowed:
            _fail(f"validator diagnostic {index} has unexpected fields")
        kind = item.get("kind")
        message = item.get("message")
        if kind not in {"controller_scan", "lean_compile"}:
            _fail(f"validator diagnostic {index} has invalid kind")
        if not isinstance(message, str) or not message.strip() or len(message) > 8192:
            _fail(f"validator diagnostic {index} has invalid message")
        row: dict[str, Any] = {"kind": kind, "message": message}
        for name in ("line", "column"):
            number = item.get(name)
            if number is not None:
                if not isinstance(number, int) or isinstance(number, bool) or number < 1:
                    _fail(f"validator diagnostic {index}.{name} is invalid")
                row[name] = number
        normalized.append(row)
    return normalized


def _artifact_locators(workspace: Path, paths: Mapping[str, Path], payloads: Mapping[str, bytes]) -> dict[str, dict[str, str]]:
    return {
        name: {"path": path.relative_to(workspace).as_posix(), "sha256": _sha(payloads[name])}
        for name, path in paths.items()
    }


def _stage_artifacts(
    *, controller: Path, variant: str, target_id: str, attempt: int,
    payloads: Mapping[str, bytes],
) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for name in ("candidate", "lean", "blueprint"):
        path = controller / f"{variant}-{target_id}-attempt-{attempt}-stage-{name}"
        _atomic_root_file(path, payloads[name])
        result[name] = {"path": str(path), "sha256": _sha(payloads[name])}
    return result


def _transport_failure_locator(
    *, controller: Path, variant: str, target_id: str, attempt: int,
    adapter: str, request_path: Path, request_sha256: str,
    diagnostic: Mapping[str, str] | None = None,
    diagnostic_stdout: Mapping[str, str] | None = None,
    diagnostic_stderr: Mapping[str, str] | None = None,
    upstream_raw_sse: Mapping[str, str] | None = None,
    normalized_response: Mapping[str, str] | None = None,
    response_structure: Mapping[str, Any] | None = None,
    response_headers: Mapping[str, str] | None = None,
) -> dict[str, str]:
    receipt = {
        "schema_version": 1, "protocol": PROTOCOL,
        "phase": "structured_provider_transport_failure",
        "variant": variant, "target_id": target_id, "attempt": attempt,
        "adapter": adapter,
        "request": {"path": str(request_path), "sha256": request_sha256},
        "provider_invocation_started": True,
        "status": "failed_without_valid_response",
    }
    if diagnostic is not None:
        receipt["diagnostic"] = dict(diagnostic)
    if diagnostic_stdout is not None or diagnostic_stderr is not None:
        if diagnostic_stdout is None or diagnostic_stderr is None:
            _fail("transport failure channel diagnostics must be supplied together")
        receipt["diagnostic_stdout"] = dict(diagnostic_stdout)
        receipt["diagnostic_stderr"] = dict(diagnostic_stderr)
    if normalized_response is not None:
        if upstream_raw_sse is None or response_structure is None or response_headers is not None:
            _fail("transport failure response evidence must be supplied together")
        receipt["upstream_raw_sse"] = dict(upstream_raw_sse or {})
        receipt["normalized_response"] = dict(normalized_response or {})
        receipt["response_structure"] = dict(response_structure or {})
    elif any(item is not None for item in (upstream_raw_sse, response_headers, response_structure)):
        if upstream_raw_sse is None or response_headers is None or response_structure is None:
            _fail("raw transport failure headers require raw-only response evidence")
        receipt["upstream_raw_sse"] = dict(upstream_raw_sse)
        receipt["response_headers"] = dict(response_headers)
        receipt["response_structure"] = dict(response_structure)
    path = controller / f"{variant}-{target_id}-attempt-{attempt}-transport-failure.json"
    _atomic_root_file(path, _pretty(receipt))
    return {"path": str(path), "sha256": _file_sha(path)}


def _process_start_ticks(pid: int) -> int:
    try:
        tail = Path(f"/proc/{pid}/stat").read_text(encoding="ascii").rsplit(") ", 1)[1]
        return int(tail.split()[19])
    except (FileNotFoundError, IndexError, OSError, ValueError):
        return -1


def _force_started_broker_cleanup(*, controller: Path, variant: str) -> None:
    """Terminate the exact broker supervisor when its normal stop path failed."""

    state_path = _root_file(
        controller / f"{variant}-model-broker-state.json",
        label="structured broker state", private=True,
    )
    state = _strict_json(state_path.read_bytes(), label="structured broker state")
    pid = state.get("supervisor_pid")
    start_ticks = state.get("supervisor_start_ticks")
    if (
        state.get("phase") != "model_broker_state"
        or state.get("protocol") != PROTOCOL
        or state.get("variant") != variant
        or not isinstance(pid, int) or isinstance(pid, bool) or pid <= 1
        or not isinstance(start_ticks, int) or isinstance(start_ticks, bool)
        or start_ticks <= 0
    ):
        _fail("structured broker state cannot authorize forced cleanup")
    if _process_start_ticks(pid) == -1:
        try:
            os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            pass
        return
    if _process_start_ticks(pid) != start_ticks:
        _fail("structured broker supervisor identity changed before cleanup")
    try:
        pidfd = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return
    try:
        signal.pidfd_send_signal(pidfd, signal.SIGTERM, None, 0)
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline and _process_start_ticks(pid) == start_ticks:
            try:
                os.waitpid(pid, os.WNOHANG)
            except ChildProcessError:
                pass
            time.sleep(0.05)
        if _process_start_ticks(pid) == start_ticks:
            signal.pidfd_send_signal(pidfd, signal.SIGKILL, None, 0)
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline and _process_start_ticks(pid) == start_ticks:
                try:
                    os.waitpid(pid, os.WNOHANG)
                except ChildProcessError:
                    pass
                time.sleep(0.05)
        try:
            os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            pass
    finally:
        os.close(pidfd)
    if _process_start_ticks(pid) == start_ticks:
        _fail("structured broker supervisor survived forced cleanup")


def run_target(
    *, workspace: Path, controller: Path, row: Mapping[str, Any],
    source_report_path: Path, source_report: Mapping[str, Any], source_report_payload: bytes,
    variant: str,
    family: str, model: str, run_id: str, broker_url: str, asset_root: Path,
    max_attempts: int, provider_call: ProviderCall = http_provider_call,
    provider_factory: ProviderFactory | None = None,
    validator: Validator | None = None,
) -> dict[str, Any]:
    target_id = str(row["id"])
    projection = _problem_projection(row)
    projection_payload = _canonical(projection)
    projection_sha = _sha(projection_payload)
    projection_path = controller / f"{variant}-{target_id}-problem-projection.json"
    _atomic_root_file(projection_path, projection_payload)
    gpt_images, kimi_images = _image_parts(row=row, asset_root=asset_root)
    image_paths = tuple(
        _root_file(
            asset_root / _safe_relative(asset.get("path"), label="problem image"),
            label="problem image",
        )
        for asset in row.get("problem_assets", [])
        if isinstance(asset, Mapping) and asset.get("kind") == "problem_page"
    )
    prior_diagnostics: list[dict[str, Any]] = []
    prior_attempt_sha: str | None = None
    chain = "0" * 64
    attempts: list[dict[str, Any]] = []
    accepted_payloads: dict[str, bytes] | None = None
    paths = _artifact_paths(workspace, report=source_report, target_id=target_id)
    target_relative = paths["lean"].relative_to(workspace).as_posix()
    source_report_relative = source_report_path.relative_to(workspace).as_posix()
    prepared_payload: bytes | None = None
    prepared_blueprint: dict[str, str] | None = None
    blueprint_path = paths["blueprint"]
    if blueprint_path.exists() or blueprint_path.is_symlink():
        prepared_path = _root_file(
            blueprint_path, label="prepared problem-only blueprint",
        )
        prepared_payload = prepared_path.read_bytes()
        # Validate before any provider is invoked.  The immutable archive is
        # the authority used by every retry and later by freeze replay.
        _validated_prepared_blueprint(
            payload=prepared_payload, target_relative=target_relative,
            source_report_relative=source_report_relative,
        )
        archived = (
            controller
            / f"{variant}-{run_id}-{target_id}-prepared-blueprint.tex"
        )
        _atomic_root_file(archived, prepared_payload)
        prepared_blueprint = {
            "path": str(archived), "sha256": _sha(prepared_payload),
        }
    for attempt_number in range(1, max_attempts + 1):
        request = build_provider_request(
            variant=variant, model=model, projection=projection,
            gpt_images=gpt_images, kimi_images=kimi_images,
            prior_diagnostics=prior_diagnostics,
        )
        request_payload = _canonical(request)
        request_path = controller / f"{variant}-{target_id}-attempt-{attempt_number}-request.json"
        _atomic_root_file(request_path, request_payload)
        diagnostics: list[dict[str, Any]] = []
        artifact_payloads: dict[str, bytes] | None = None
        response_locator: dict[str, str] | None = None
        submission_locator: dict[str, str] | None = None
        candidate_sha: str | None = None
        staged: dict[str, dict[str, str]] | None = None
        adapter = (
            "chatgpt_login_proxy_v1" if variant == "gpt"
            else "structured_broker_http_v1"
        )
        adapter_provenance: dict[str, Any] = {}
        reply: ProviderReply | None = None
        try:
            active_provider = (
                provider_factory(target_id, attempt_number, request, image_paths)
                if provider_factory is not None else provider_call
            )
            reply = active_provider(broker_url, request)
        except ProviderInvocationError as exc:
            diagnostics = [{
                "kind": "controller_scan",
                "message": "provider transport failed before a valid structured response",
            }]
            adapter_provenance = {"transport_failure_receipt": exc.receipt}
        except (
            StructuredSolverError, OSError, TimeoutError,
            http.client.HTTPException, subprocess.SubprocessError,
        ):
            # These are the explicitly classified provider/transport failure
            # modes.  Unexpected exceptions (especially TypeError caused by a
            # controller programming error) deliberately escape to the outer
            # incomplete-run ledger instead of being disguised as a retry.
            diagnostics = [{
                "kind": "controller_scan",
                "message": "provider transport failed before a valid structured response",
            }]
            adapter_provenance = {"transport_failure_receipt": _transport_failure_locator(
                controller=controller, variant=variant, target_id=target_id,
                attempt=attempt_number, adapter=adapter,
                request_path=request_path, request_sha256=_sha(request_payload),
            )}
        if reply is not None:
            adapter = reply.adapter
            adapter_provenance = dict(reply.provenance or {})
            if len(reply.raw_response) > MAX_PROVIDER_RESPONSE_BYTES:
                diagnostics = [{
                    "kind": "controller_scan",
                    "message": "provider transport failed before a valid structured response",
                }]
                adapter_provenance = {
                    "transport_failure_receipt": _transport_failure_locator(
                        controller=controller, variant=variant,
                        target_id=target_id, attempt=attempt_number,
                        adapter=adapter, request_path=request_path,
                        request_sha256=_sha(request_payload),
                    )
                }
                reply = None
        if reply is not None:
            response_path = controller / f"{variant}-{target_id}-attempt-{attempt_number}-response.json"
            _atomic_root_file(response_path, reply.raw_response)
            response_locator = {
                "path": str(response_path), "sha256": _sha(reply.raw_response),
            }
            submission = reply.submission
            try:
                submission = _validate_submission_shape(submission)
                submission_payload = _canonical(submission)
            except (StructuredSolverError, UnicodeDecodeError):
                diagnostics = [{
                    "kind": "controller_scan",
                    "message": "provider response or constructed artifacts failed trusted validation",
                }]
            else:
                submission_path = controller / f"{variant}-{target_id}-attempt-{attempt_number}-submission.json"
                _atomic_root_file(submission_path, submission_payload)
                submission_locator = {
                    "path": str(submission_path), "sha256": _sha(submission_payload),
                }
                try:
                    candidate = _construct_candidate(
                        submission, target_id=target_id,
                        blind_hash=_sha(_canonical(row)), source_entry=row,
                    )
                    raw_lean = submission.get("lean_source")
                    if not isinstance(raw_lean, str):
                        _fail("lean_source and blueprint must be strings")
                    composed_blueprint = _compose_blueprint(
                        generated=submission.get("blueprint"),
                        prepared_payload=prepared_payload,
                        target_relative=target_relative,
                        source_report_relative=source_report_relative,
                    )
                    unvalidated_payloads = {
                        "candidate": _canonical(candidate),
                        "lean": raw_lean.encode("utf-8"),
                        "blueprint": composed_blueprint,
                    }
                    if any(
                        len(payload) > MAX_ARTIFACT_BYTES
                        for payload in unvalidated_payloads.values()
                    ):
                        _fail("constructed artifact exceeds byte limit")
                except (StructuredSolverError, UnicodeDecodeError):
                    diagnostics = [{
                        "kind": "controller_scan",
                        "message": "provider response or constructed artifacts failed trusted validation",
                    }]
                else:
                    candidate_sha = _sha(unvalidated_payloads["candidate"])
                    # Controller I/O failures and programming errors are not
                    # model rejections and therefore are never swallowed here.
                    staged = _stage_artifacts(
                        controller=controller, variant=variant,
                        target_id=target_id, attempt=attempt_number,
                        payloads=unvalidated_payloads,
                    )
                    staged_payloads = {
                        name: Path(locator["path"]).read_bytes()
                        for name, locator in staged.items()
                    }
                    try:
                        artifact_payloads = {
                            "candidate": _validate_candidate(
                                _strict_json(staged_payloads["candidate"], label="staged candidate"),
                                target_id=target_id,
                                blind_hash=_sha(_canonical(row)), source_entry=row,
                            ),
                            "lean": _validate_lean_source(
                                staged_payloads["lean"].decode("utf-8", errors="strict")
                            ),
                            "blueprint": _validate_blueprint(
                                staged_payloads["blueprint"].decode("utf-8", errors="strict")
                            ),
                        }
                    except (StructuredSolverError, UnicodeDecodeError):
                        artifact_payloads = None
                        diagnostics = [{
                            "kind": "controller_scan",
                            "message": "provider response or constructed artifacts failed trusted validation",
                        }]
                    if artifact_payloads is not None and validator is not None:
                        diagnostics = _normalize_diagnostics(validator(artifact_payloads))
                        if diagnostics:
                            artifact_payloads = None
        status = (
            "accepted" if artifact_payloads is not None else
            "transport_error" if response_locator is None else "rejected"
        )
        attempt_body = {
            "schema_version": 1, "protocol": PROTOCOL,
            "phase": "structured_solver_attempt", "variant": variant,
            "model_family": family, "model_id": model, "run_id": run_id,
            "target_id": target_id, "attempt": attempt_number,
            "previous_attempt_sha256": prior_attempt_sha,
            "adapter": adapter,
            "adapter_provenance": adapter_provenance,
            "request_profile": REQUEST_PROFILE, "tools_enabled": False,
            "store": False, "problem_projection_sha256": projection_sha,
            "prior_diagnostics_sha256": _sha(_canonical(prior_diagnostics)),
            "request": {"path": str(request_path), "sha256": _sha(request_payload)},
            "response": response_locator,
            "submission": submission_locator,
            "constructed_candidate_sha256": candidate_sha,
            "staged_artifacts": staged,
            "status": status,
            "diagnostics": diagnostics,
            "artifacts": _artifact_locators(workspace, paths, artifact_payloads) if artifact_payloads else None,
        }
        chain_material = _canonical(attempt_body)
        chain = _sha(bytes.fromhex(chain) + chain_material)
        attempt_body["attempt_chain_sha256"] = chain
        if set(attempt_body) != ATTEMPT_FIELDS:
            _fail("internal structured attempt schema drift")
        attempt_path = controller / f"{variant}-{target_id}-attempt-{attempt_number}.json"
        _atomic_root_file(attempt_path, _pretty(attempt_body))
        attempts.append({"path": str(attempt_path), "sha256": _file_sha(attempt_path)})
        prior_attempt_sha = attempts[-1]["sha256"]
        if artifact_payloads is not None:
            accepted_payloads = artifact_payloads
            break
        prior_diagnostics = diagnostics
    if accepted_payloads is None:
        _fail(f"structured solver exhausted attempts for {target_id}")
    _publish_artifacts(
        paths, accepted_payloads,
        prepared_blueprint_sha256=(
            prepared_blueprint["sha256"] if prepared_blueprint is not None else None
        ),
    )
    final_artifacts = _artifact_locators(workspace, paths, accepted_payloads)
    target_receipt = {
        "id": target_id,
        "source_report": {
            "path": str(source_report_path), "sha256": _sha(source_report_payload),
        },
        "adapter": attempts and _load_json(
            Path(attempts[-1]["path"]), label="accepted structured attempt"
        )["adapter"],
        "problem_projection_sha256": projection_sha,
        "prepared_blueprint": prepared_blueprint,
        "attempts": attempts, "accepted_attempt": len(attempts),
        "final_artifacts": final_artifacts, "target_chain_sha256": chain,
    }
    if set(target_receipt) != TARGET_FIELDS:
        _fail("internal structured target schema drift")
    return target_receipt


def _write_incomplete_aggregate(
    *, controller: Path, variant: str, family: str, model: str, run_id: str,
    scope_ids: Sequence[str], bundle_path: Path, bundle_payload: bytes,
    completed_targets: Sequence[Mapping[str, Any]],
    source_first_precommit: Path, source_first_precommit_sha256: str,
    stage: str, error_code: str,
) -> Path:
    attempts: list[tuple[str, int, dict[str, str]]] = []
    pattern = re.compile(
        rf"^{re.escape(variant)}-(?P<target>.+)-attempt-(?P<attempt>[1-9][0-9]*)\.json$"
    )
    for path in controller.glob(f"{variant}-*-attempt-*.json"):
        match = pattern.fullmatch(path.name)
        if match is None or path.is_symlink() or not path.is_file():
            continue
        document = _load_json(path, label="incomplete structured attempt")
        if document.get("phase") != "structured_solver_attempt":
            continue
        attempts.append((
            match.group("target"), int(match.group("attempt")),
            {"path": str(path.resolve()), "sha256": _file_sha(path)},
        ))
    transports: list[dict[str, str]] = []
    for glob_pattern in (
        f"{variant}-model-broker-ready.json",
        f"{variant}-model-broker-transcript.json",
        f"{variant}-*-login-proxy-receipt.json",
        f"{variant}-*-login-proxy-failure.json",
        f"{variant}-*-transport-failure.json",
    ):
        for path in controller.glob(glob_pattern):
            if path.is_file() and not path.is_symlink():
                transports.append({"path": str(path.resolve()), "sha256": _file_sha(path)})
    failure = {
        "schema_version": 1, "protocol": PROTOCOL,
        "phase": "structured_solver_incomplete", "variant": variant,
        "model_family": family, "model_id": model, "run_id": run_id,
        "request_profile": REQUEST_PROFILE, "tools_enabled": False,
        "store": False, "scope_ids": list(scope_ids),
        "bundle": {"path": str(bundle_path.resolve()), "sha256": _sha(bundle_payload)},
        "controller_binary_sha256": _file_sha(Path(__file__).resolve()),
        "source_first_precommit": {
            "path": str(source_first_precommit.resolve()),
            "sha256": source_first_precommit_sha256,
        },
        "completed_targets": list(completed_targets),
        "attempt_receipts": [locator for _target, _attempt, locator in sorted(attempts)],
        "transport_receipts": sorted(transports, key=lambda item: item["path"]),
        "all_targets_finalized": False,
        "stage": stage,
        "error_code": error_code,
    }
    output = controller / f"{variant}-structured-solver-incomplete.json"
    _atomic_root_file(output, _pretty(failure))
    return output


def _write_success_aggregate(
    *, controller: Path, variant: str, family: str, model: str, run_id: str,
    ids: Sequence[str], rows: Mapping[str, Any], bundle_path: Path,
    bundle_payload: bytes, targets: Sequence[Mapping[str, Any]],
    source_first_precommit_sha256: str, ready_path: Path | None,
    broker_transcript: Path | None,
) -> dict[str, Any]:
    request_count = sum(len(target["attempts"]) for target in targets)
    if variant == "kimi-k3":
        if broker_transcript is None or ready_path is None:
            _fail("Kimi broker stopped without a transcript")
        transcript_path = _root_file(
            broker_transcript,
            label="structured model broker transcript", private=True,
        )
        transcript = _load_json(
            transcript_path, label="structured broker transcript",
        )
        if (
            transcript.get("protocol") != PROTOCOL
            or transcript.get("phase") != "model_broker_transcript"
            or transcript.get("variant") != variant
            or transcript.get("run_id") != run_id
            or transcript.get("request_profile") != REQUEST_PROFILE
            or transcript.get("ready_receipt_sha256") != _file_sha(ready_path)
            or transcript.get("request_count") != request_count
            or transcript.get("broker_stopped") is not True
        ):
            _fail("structured broker transcript does not bind all attempts/stoppage")
        transport: dict[str, Any] = {
            "kind": "structured_broker_http_v1",
            "ready_receipt": {
                "path": str(ready_path), "sha256": _file_sha(ready_path),
            },
            "transcript": {
                "path": str(transcript_path), "sha256": _file_sha(transcript_path),
            },
        }
        request_response_chain = str(
            transcript["request_response_chain_sha256"]
        )
    else:
        exchanges: list[dict[str, str]] = []
        chain = "0" * 64
        for target in targets:
            for attempt_locator in target["attempts"]:
                attempt = _load_json(
                    Path(attempt_locator["path"]),
                    label="GPT structured attempt",
                )
                provenance = attempt.get("adapter_provenance", {})
                proxy_locator = (
                    provenance.get("proxy_receipt")
                    if isinstance(provenance, Mapping) else None
                )
                if proxy_locator is None and isinstance(provenance, Mapping):
                    proxy_locator = provenance.get("transport_failure_receipt")
                if not isinstance(proxy_locator, dict):
                    _fail("GPT attempt lacks a ChatGPT proxy/failure receipt")
                proxy_path = _root_file(
                    Path(str(proxy_locator.get("path"))),
                    label="ChatGPT transport receipt", private=True,
                )
                locator = {
                    "path": str(proxy_path), "sha256": _file_sha(proxy_path),
                }
                if locator["sha256"] != proxy_locator.get("sha256"):
                    _fail("GPT proxy receipt hash drift")
                exchanges.append(locator)
                chain = _sha(
                    bytes.fromhex(chain) + bytes.fromhex(locator["sha256"])
                )
        if len(exchanges) != request_count:
            _fail("GPT proxy exchange coverage differs from attempts")
        transport = {
            "kind": "chatgpt_login_proxy_v1", "exchanges": exchanges,
            "exchange_chain_sha256": chain,
        }
        request_response_chain = chain
    receipt = {
        "schema_version": 1, "protocol": PROTOCOL,
        "phase": "structured_solver_aggregate", "variant": variant,
        "model_family": family, "model_id": model, "run_id": run_id,
        "adapter": transport["kind"],
        "request_profile": REQUEST_PROFILE, "tools_enabled": False,
        "store": False, "scope_ids": list(ids),
        "bundle": {
            "path": str(bundle_path.resolve()), "sha256": _sha(bundle_payload),
            "row_count": len(rows), "ids": sorted(rows),
        },
        "controller_binary_sha256": _file_sha(Path(__file__).resolve()),
        "transport": transport, "targets": list(targets),
        "all_targets_finalized": True,
        "source_first_precommit_sha256": source_first_precommit_sha256,
        "request_count": request_count,
        "request_response_chain_sha256": request_response_chain,
    }
    if set(receipt) != RECEIPT_FIELDS:
        _fail("internal structured aggregate schema drift")
    output = controller / f"{variant}-structured-solver-receipt.json"
    _atomic_root_file(output, _pretty(receipt))
    return receipt


def run_structured_solver(
    *, workspace: Path, controller_dir: Path, bundle_path: Path,
    asset_root: Path, variant: str, run_id: str,
    source_first_precommit: Path,
    broker_ready: Path | None = None, broker_transcript: Path | None = None,
    scope_ids: Sequence[str], max_attempts: int,
    provider_call: ProviderCall = http_provider_call, validator: Validator | None = None,
    provider_factory: ProviderFactory | None = None,
    runtime_lake: Path | None = None, dependency_root: Path | None = None,
    verifier_user: str | None = None, verifier_scratch: Path | None = None,
    broker_credential_file: Path | None = None,
    broker_credential_format: str = "raw", broker_token_name: str | None = None,
    broker_user: str | None = None, broker_port: int = 0,
    codex_binary: Path | None = None, codex_home: Path | None = None,
) -> dict[str, Any]:
    if os.geteuid() != 0:
        _fail("structured solver controller must run as root")
    if variant not in MODELS or SAFE_ID.fullmatch(run_id) is None:
        _fail("structured solver variant/run id is invalid")
    if not 1 <= max_attempts <= 16:
        _fail("max attempts must be between 1 and 16")
    if validator is None and (
        runtime_lake is None or dependency_root is None
        or verifier_user is None or verifier_scratch is None
    ):
        _fail("production structured solve requires a credential-free clean validator")
    workspace = _root_directory(workspace, label="structured solver workspace")
    controller = _root_directory(controller_dir, label="controller receipt directory")
    asset_root = _root_directory(asset_root, label="problem asset root")
    family, model = MODELS[variant]
    # Finish all filesystem/source authority preflight before a credential
    # broker is allowed to exist.
    bundle_payload, rows = _bundle_rows(bundle_path)
    ids = sorted(scope_ids or rows)
    if not ids or len(ids) != len(set(ids)) or any(item not in rows for item in ids):
        _fail("structured solver scope differs from blind bundle")
    # The source-first model commitment must already be immutably finalized.
    # Validate and bind it before inspecting any solver target/source report or
    # invoking the solve provider, which makes the A-before-solve ordering
    # mechanically visible to the later controller seal.
    precommit_path = _root_file(
        source_first_precommit, label="source-first Review precommit", private=True,
    )
    precommit_payload = precommit_path.read_bytes()
    precommit = _strict_json(precommit_payload, label="source-first Review precommit")
    if set(precommit) != SOURCE_FIRST_PRECOMMIT_FIELDS or (
        precommit.get("schema_version") != SCHEMA_VERSION
        or precommit.get("protocol") != PROTOCOL
        or precommit.get("phase") != "structured_source_first_precommit"
        or precommit.get("variant") != variant
        or precommit.get("model_family") != family
        or precommit.get("model_id") != model
        or precommit.get("run_id") != run_id
        or precommit.get("request_profile")
        != "tool_free_structured_independent_review_v1"
        or precommit.get("tools_enabled") is not False
        or precommit.get("store") is not False
        or precommit.get("scope_ids") != ids
        or precommit.get("status") != "accepted"
        or precommit.get("finalized_before_solver") is not True
    ):
        _fail("source-first Review precommit provenance/scope is stale")
    source_first_precommit_sha256 = _sha(precommit_payload)
    targets: list[dict[str, Any]] = []

    def record_incomplete(*, stage: str, error_code: str) -> None:
        output = controller / f"{variant}-structured-solver-incomplete.json"
        if output.is_file() and not output.is_symlink():
            return
        _write_incomplete_aggregate(
            controller=controller, variant=variant, family=family, model=model,
            run_id=run_id, scope_ids=ids, bundle_path=bundle_path,
            bundle_payload=bundle_payload, completed_targets=targets,
            source_first_precommit=precommit_path,
            source_first_precommit_sha256=source_first_precommit_sha256,
            stage=stage, error_code=error_code,
        )

    try:
        reports = _source_reports(workspace, rows=rows, scope_ids=ids)
    except BaseException:
        record_incomplete(
            stage="source_report_preflight", error_code="source_report_invalid",
        )
        raise
    started_broker = False
    broker_module: Any | None = None
    ready_path: Path | None = None
    ready: dict[str, Any] | None = None
    if variant == "kimi-k3":
        if broker_ready is None:
            if broker_credential_file is None or broker_user is None:
                record_incomplete(
                    stage="broker_preflight",
                    error_code="model_broker_credentials_unavailable",
                )
                _fail("Kimi production solve requires an invocation-scoped broker credential/user")
            broker_module = _load_model_broker_module()
            try:
                started = broker_module.start_broker(
                    controller_dir=controller, variant=variant, run_id=run_id,
                    model=model, upstream="https://api.moonshot.cn/anthropic",
                    credential_file=broker_credential_file,
                    credential_format=broker_credential_format,
                    token_name=broker_token_name, broker_user=broker_user,
                    port=broker_port, request_profile=REQUEST_PROFILE,
                )
            except BaseException:
                record_incomplete(
                    stage="broker_start", error_code="model_broker_start_failed",
                )
                raise
            broker_ready = Path(str(started["ready"]))
            started_broker = True
        try:
            ready_path = _root_file(
                broker_ready, label="structured model broker ready receipt", private=True,
            )
            ready = _load_json(ready_path, label="structured broker ready receipt")
            if (
                ready.get("protocol") != PROTOCOL
                or ready.get("phase") != "model_broker_ready"
                or ready.get("variant") != variant
                or ready.get("run_id") != run_id
                or ready.get("allowed_model") != model
                or ready.get("request_profile") != REQUEST_PROFILE
            ):
                _fail("structured broker ready provenance/profile mismatch")
        except BaseException:
            cleanup_error: BaseException | None = None
            if started_broker:
                assert broker_module is not None
                try:
                    broker_module.stop_broker(
                        controller_dir=controller, variant=variant,
                    )
                except BaseException as exc:
                    # Ledger publication must not be skipped merely because
                    # cleanup also failed.  The broker supervisor is bound by
                    # PDEATHSIG to this controller; preserve both facts by
                    # recording a cleanup-specific failure stage.
                    cleanup_error = exc
                    try:
                        _force_started_broker_cleanup(
                            controller=controller, variant=variant,
                        )
                    except BaseException:
                        # Keep the original readiness failure as the raised
                        # cause while the immutable ledger records that both
                        # normal and forced cleanup failed closed.
                        pass
            record_incomplete(
                stage=(
                    "broker_ready_cleanup" if cleanup_error is not None
                    else "broker_ready"
                ),
                error_code=(
                    "model_broker_ready_invalid_and_stop_failed"
                    if cleanup_error is not None
                    else "model_broker_ready_invalid"
                ),
            )
            raise
    else:
        if broker_ready is not None or broker_transcript is not None:
            record_incomplete(
                stage="provider_preflight",
                error_code="gpt_broker_fixture_forbidden",
            )
            _fail("GPT structured solve uses the login proxy, not the token broker")
        if provider_factory is None:
            if codex_binary is None or codex_home is None:
                record_incomplete(
                    stage="provider_preflight", error_code="gpt_transport_unavailable",
                )
                _fail("GPT production solve requires trusted Codex binary/login home")
            provider_factory = lambda target_id, attempt, _request, _images: ChatGPTLoginProxyAdapter(
                codex_binary=codex_binary, codex_home=codex_home,
                controller=controller, target_id=target_id, attempt=attempt,
                run_id=run_id,
            )
    solve_error: BaseException | None = None
    stop_error: BaseException | None = None
    try:
        for target_id in ids:
            target_validator = validator
            if target_validator is None:
                target_validator = CleanLeanValidator(
                    workspace=workspace,
                    target_relative=str(reports[target_id][1]["output_lean"]),
                    runtime_lake=runtime_lake,  # type: ignore[arg-type]
                    dependency_root=dependency_root,  # type: ignore[arg-type]
                    verifier_user=str(verifier_user),
                    scratch_root=verifier_scratch,  # type: ignore[arg-type]
                )
            targets.append(run_target(
                workspace=workspace, controller=controller, row=rows[target_id],
                source_report_path=reports[target_id][0],
                source_report=reports[target_id][1],
                source_report_payload=reports[target_id][2],
                variant=variant, family=family, model=model, run_id=run_id,
                broker_url=(str(ready["listen_url"]) if ready is not None else ""),
                asset_root=asset_root, max_attempts=max_attempts,
                provider_call=provider_call, provider_factory=provider_factory,
                validator=target_validator,
            ))
    except BaseException as exc:
        solve_error = exc
    finally:
        if started_broker:
            assert broker_module is not None
            try:
                broker_transcript = broker_module.stop_broker(
                    controller_dir=controller, variant=variant,
                )
            except BaseException as exc:
                stop_error = exc
                try:
                    _force_started_broker_cleanup(
                        controller=controller, variant=variant,
                    )
                except BaseException:
                    pass
    if stop_error is not None:
        record_incomplete(
            stage="broker_stop", error_code="model_broker_stop_failed",
        )
        if solve_error is None:
            raise stop_error
    if solve_error is not None:
        record_incomplete(
            stage="target_solve", error_code="structured_target_incomplete",
        )
        raise solve_error
    try:
        return _write_success_aggregate(
            controller=controller, variant=variant, family=family, model=model,
            run_id=run_id, ids=ids, rows=rows, bundle_path=bundle_path,
            bundle_payload=bundle_payload, targets=targets,
            source_first_precommit_sha256=source_first_precommit_sha256,
            ready_path=ready_path, broker_transcript=broker_transcript,
        )
    except BaseException:
        record_incomplete(
            stage="aggregate_finalize",
            error_code="structured_aggregate_invalid",
        )
        raise


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--controller-dir", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--asset-root", type=Path, required=True)
    parser.add_argument("--variant", choices=sorted(MODELS), required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--source-first-precommit", type=Path, required=True)
    parser.add_argument(
        "--broker-ready", type=Path,
        help="test-only stopped Kimi broker fixture; production starts its own broker",
    )
    parser.add_argument("--broker-transcript", type=Path)
    parser.add_argument("--broker-credential-file", type=Path)
    parser.add_argument("--broker-credential-format", choices=("raw", "json", "env"), default="raw")
    parser.add_argument("--broker-token-name")
    parser.add_argument("--broker-user")
    parser.add_argument("--broker-port", type=int, default=0)
    parser.add_argument("--codex-binary", type=Path)
    parser.add_argument("--codex-home", type=Path)
    parser.add_argument("--scope-id", action="append", default=[])
    parser.add_argument("--max-attempts", type=int, default=4)
    parser.add_argument("--runtime-lake", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--verifier-user", required=True)
    parser.add_argument("--verifier-scratch", type=Path, required=True)
    return parser


def main() -> int:
    args = _parser().parse_args()
    try:
        run_structured_solver(
            workspace=args.workspace, controller_dir=args.controller_dir,
            bundle_path=args.bundle, asset_root=args.asset_root,
            variant=args.variant, run_id=args.run_id,
            source_first_precommit=args.source_first_precommit,
            broker_ready=args.broker_ready, broker_transcript=args.broker_transcript,
            scope_ids=args.scope_id, max_attempts=args.max_attempts,
            runtime_lake=args.runtime_lake, dependency_root=args.dependency_root,
            verifier_user=args.verifier_user, verifier_scratch=args.verifier_scratch,
            broker_credential_file=args.broker_credential_file,
            broker_credential_format=args.broker_credential_format,
            broker_token_name=args.broker_token_name,
            broker_user=args.broker_user, broker_port=args.broker_port,
            codex_binary=args.codex_binary, codex_home=args.codex_home,
        )
    except StructuredSolverError as exc:
        raise SystemExit(f"error: {exc}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
