"""Answer-blind result freezing and post-freeze grading.

The two phases in this module intentionally have separate entry points and
data flows:

* :func:`freeze_blind_evaluation` can only see problem-side source reports,
  solver candidates, Lean artifacts, and the two Review gates.  It has no
  grader-key argument or lookup path.
* :func:`grade_blind_evaluation` first verifies every frozen byte hash.  Only
  after that succeeds does it open the external grader JSONL.  Grading is
  read-only with respect to the project, candidates, gates, and manifest.

This separation is part of the evaluation protocol, rather than merely a CLI
convention.  Keep grader-aware code out of the freeze call graph.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import secrets
import shutil
import stat
import subprocess
import tempfile
import base64
import unicodedata
from collections import Counter
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, NoReturn, Sequence
from urllib.parse import urlparse

import typer

from archon.commands.loop.review_source_contract import (
    blind_result_payload_sha256,
    build_review_source_contract,
    expected_nonnumeric_result_types,
    expected_numeric_result_types,
    is_answer_blind_contract,
    lean_result_type_sha256,
    normalized_review_source_certificate,
    source_contract_provenance,
    validate_blind_result_contracts,
    validate_review_source_certificate,
)
from archon.commands.loop.sorry_count import file_open_sorry_count


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
FREEZE_PHASE = "freeze"
GRADE_PHASE = "post_freeze_grade"

FORMALIZATION_GATE = ".archon/formalization-review-gate.json"
PROOF_GATE = ".archon/proof-review-gate.json"
SEED_MANIFEST = "isolation_manifest.json"
CONFIG_FILE = ".archon/config.json"
MCP_FILE = ".mcp.json"
PROTOCOL_FILE = "ANSWER_BLIND_PROTOCOL.md"
AGENTS_FILE = ".archon/AGENTS.md"
CONTROLLER_PHASE = "freeze_authorization"
VERIFIER_PHASE = "lean_verify"

_CONTROLLER_BINDING_FIELDS = {
    "schema_version",
    "protocol",
    "phase",
    "solver_stopped",
    "seed_manifest_sha256",
    "blind_bundle",
    "freeze_scope",
    "generated_files",
    "dependency_inventory",
    "runtime_inventory",
    "snapshot_inventory",
    "verifier_snapshot",
    "independent_review_receipt",
    "solver",
    "isolation",
    "structured_solver_receipt",
    "source_first_precommit",
    "verifier_receipt",
}
_CONTROLLER_BUNDLE_FIELDS = {"path", "sha256", "row_count", "ids"}
_CONTROLLER_SCOPE_FIELDS = {"kind", "ids"}
_CONTROLLER_GENERATED_FILES = {CONFIG_FILE, MCP_FILE, PROTOCOL_FILE, AGENTS_FILE}
_DEPENDENCY_INVENTORY_FIELDS = {"root", "files", "files_sha256"}
_RUNTIME_INVENTORY_FIELDS = {"root", "files", "files_sha256"}
_SNAPSHOT_INVENTORY_FIELDS = {"files", "files_sha256"}
_VERIFIER_SNAPSHOT_FIELDS = {"root", "files", "files_sha256"}
_SOLVER_FIELDS = {"model_family", "model_id", "run_id"}
_ISOLATION_FIELDS = {"filesystem_answer_blind", "network_answer_blind"}
_EXTERNAL_RECEIPT_FIELDS = {"path", "sha256"}
_LAUNCH_AUTHORIZATION_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id", "workspace",
    "runtime_root", "dependency_root", "system_inventory",
    "system_read_only_paths", "solver_external_read_write_paths",
    "verifier_external_read_write_paths", "reviewer_external_read_write_paths",
    "required_denied_probe_paths", "allowed_model_broker_tcp_port",
}
_SYSTEM_INVENTORY_FIELDS = {"files", "files_sha256"}
_MODEL_BROKER_BINDING_FIELDS = {"ready_receipt", "transcript"}
_MODEL_BROKER_READY_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id",
    "listen_url", "upstream_origin", "allowed_model", "request_profile",
    "public_dummy_key_sha256",
    "broker_uid", "broker_binary_sha256", "started_at",
}
_MODEL_BROKER_TRANSCRIPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id",
    "request_profile", "ready_receipt_sha256", "request_count",
    "request_response_chain_sha256",
    "started_at", "stopped_at", "broker_stopped",
}
_STRUCTURED_REVIEW_PROFILE = "tool_free_structured_independent_review_v1"
_CODEX_DISABLED_HOST_CONFIRMATION = (
    "Code Mode is unavailable because code-mode host is disabled. "
    "Code mode will fail closed; enable `features.code_mode_host` and install "
    "`codex-code-mode-host`."
)
_STRUCTURED_REVIEW_AGGREGATE_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "snapshot_inventory_sha256", "controller_binary_sha256",
    "source_first_attempt", "artifact_review_attempt",
    "source_records_sha256", "source_commitment_sha256",
    "semantic_review_sha256",
    "all_passes_finalized",
}
_STRUCTURED_REVIEW_ATTEMPT_COMMON_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "snapshot_inventory_sha256", "controller_binary_sha256",
    "input_inventory", "review_projection_sha256", "adapter_provenance",
    "adapter", "transport",
    "request", "response", "model_submission", "constructed_semantic_receipt",
    "normalized_response_sha256",
    "request_response_chain_sha256", "status",
}
_STRUCTURED_SOURCE_REVIEW_ATTEMPT_FIELDS = set(
    _STRUCTURED_REVIEW_ATTEMPT_COMMON_FIELDS
) | {"source_first_precommit", "source_records_commitment"}
_STRUCTURED_ARTIFACT_REVIEW_ATTEMPT_FIELDS = {
    *_STRUCTURED_REVIEW_ATTEMPT_COMMON_FIELDS,
    "source_records_commitment", "source_first_attempt_sha256",
}
_STRUCTURED_REVIEW_ADAPTER_FIELDS = {
    "provider_api", "response_extractor", "response_schema_sha256",
}
_STRUCTURED_SOURCE_PRECOMMIT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "request_profile", "tools_enabled", "store",
    "scope_ids", "controller_binary_sha256", "input_inventory",
    "review_projection_sha256", "adapter_provenance", "adapter", "transport",
    "request", "response", "model_submission", "normalized_response_sha256",
    "request_response_chain_sha256", "status", "finalized_before_solver",
}
_SOURCE_FIRST_REVIEW_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "variant", "model_family", "model_id", "run_id",
    "request_profile", "snapshot_inventory_sha256",
    "review_input_inventory_sha256", "review_projection_sha256",
    "source_first_precommit_sha256", "source_records_sha256",
    "scope_ids", "records",
}
_SOURCE_FIRST_RECORDS_COMMITMENT_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "variant", "model_family", "model_id", "run_id",
    "request_profile", "review_input_inventory_sha256",
    "review_projection_sha256", "scope_ids", "records",
}
_SOURCE_FIRST_RECORD_FIELDS = {
    "id", "blind_record_sha256", "source_record_sha256",
    "requested_outputs_sha256", "status", "givens", "derivation_steps",
    "output_commitments",
}
_SOURCE_FIRST_GIVEN_FIELDS = {"id", "source_locator", "fact"}
_SOURCE_FIRST_DERIVATION_FIELDS = {
    "id", "claim", "depends_on", "justification",
}
_SOURCE_FIRST_OUTPUT_FIELDS = {
    "id", "source_requirement", "kind", "unit", "reporting_policy",
    "derivation_step_ids", "result_spec",
}
_SOURCE_FIRST_NUMERIC_SPEC_FIELDS = {
    "kind", "status", "raw_expression", "raw_value", "certified_interval",
    "reported_value", "reporting_quantum", "tie_rule",
}
_SOURCE_FIRST_INTEGER_SPEC_FIELDS = {
    "kind", "status", "value", "proposition", "constraints",
}
_SOURCE_FIRST_SYMBOLIC_SPEC_FIELDS = {
    "kind", "status", "normalized_result", "proposition", "constraints",
}
_SOURCE_FIRST_SET_SPEC_FIELDS = {
    "kind", "status", "normalized_members", "proposition", "constraints",
}
_SOURCE_FIRST_UNDERDETERMINED_SPEC_FIELDS = {
    "kind", "status", "reason", "remaining_constraints",
}
_MULTI_REPORTED_ITEM_FIELDS = {"status", "value"}
_INDEPENDENT_REVIEW_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "variant", "model_family", "model_id", "run_id",
    "request_profile", "snapshot_inventory_sha256",
    "review_input_inventory_sha256", "review_projection_sha256",
    "source_records_sha256",
    "scope_ids", "records",
}
_INDEPENDENT_REVIEW_RECORD_FIELDS = {
    "id", "target", "target_sha256", "candidate_sha256",
    "source_report_sha256", "blueprint_sha256", "source_contract_sha256",
    "requested_outputs_sha256", "source_commitment_record_sha256",
    "source_alignment", "formalization_status",
    "formalization_certificate", "proof_status", "proof_certificate",
}
_SOURCE_ALIGNMENT_FIELDS = {"status", "evidence"}
_SOURCE_COMMITMENT_INPUT = ".source-first-records.json"
_SOURCE_FIRST_RECORD_DIRECTORY = "source_records"
_SOURCE_FIRST_PROJECTION_FIELDS = {
    "schema_version", "protocol", "evaluation_mode", "official_answer_seen",
    "phase", "id", "current_question", "shared_context", "previous_parts",
    "images", "problem_assets", "requested_outputs", "reporting_policy",
    "measurement_policy", "candidate_domain_policy",
}
_INDEPENDENT_FORMAL_CERTIFICATE_REQUIRED_FIELDS = {
    "schema_version", "checks", "bridge_obligations", "source_contract",
    "blind_review_certificate",
}
_INDEPENDENT_FORMAL_CERTIFICATE_OPTIONAL_FIELDS = {
    "official_answer_alignment", "source_inconsistency",
}
_INDEPENDENT_PROOF_CERTIFICATE_FIELDS = {
    "proof_review_schema_version", "proof_review_route", "reason", "evidence",
    "redraft_kind", "source_contract", "blind_review_certificate",
}
_VERIFIER_RECEIPT_FIELDS = {
    "schema_version",
    "protocol",
    "phase",
    "evaluation_mode",
    "verifier_uid",
    "network_answer_blind",
    "runtime_executable",
    "dependency_inventory_sha256",
    "runtime_inventory_sha256",
    "snapshot_inventory_sha256",
    "scope_ids",
    "records",
    "compiled",
    "stdout_sha256",
    "stderr_sha256",
}
_VERIFIER_RUNTIME_FIELDS = {"path", "sha256"}
_VERIFIER_RECORD_FIELDS = {
    "id",
    "target",
    "target_sha256",
    "candidate",
    "candidate_sha256",
    "source_contract_sha256",
    "result_contracts_sha256",
    "checks",
}
_VERIFIER_CHECK_FIELDS = {
    "role",
    "declaration",
    "normalized_type_sha256",
    "result_payload_sha256",
    "axioms",
    "compiled",
}
_VERIFIER_INVOCATION_FIELDS = {
    "schema_version", "protocol", "phase", "verifier_uid", "command_argv",
    "exit_code", "solver_stopped", "descendants_stopped",
    "network_answer_blind", "verifier_receipt", "stdout_log",
    "dependency_inventory_sha256", "runtime_inventory_sha256",
    "snapshot_inventory_sha256", "snapshot_root", "dedicated_uid_quiescence",
}
_FROZEN_MANIFEST_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "frozen_at", "project_binding", "solver",
    "isolation", "controller_binding", "record_count", "records", "artifacts",
}
_FROZEN_CONTROLLER_FIELDS = {
    "controller_seal_sha256", "scope_kind", "scope_ids", "bundle_sha256",
    "bundle_row_count", "seed_manifest_sha256", "snapshot_inventory_sha256",
    "dependency_inventory_sha256", "runtime_inventory_sha256",
    "verifier_snapshot_sha256",
    "source_first_precommit_sha256",
    "structured_solver_receipt_sha256",
    "independent_review_receipt_sha256",
    "verifier_receipt_sha256",
    "lean_verifier_result_sha256",
}
_FROZEN_RECORD_FIELDS = {
    "id", "blind_record_sha256", "candidate", "candidate_artifact",
    "target_artifact", "blueprint_artifact", "source_report_artifact",
    "problem_image_artifacts", "source_contract", "lean_verifier_record",
    "formalization_gate_status", "proof_gate_status",
}
_ARTIFACT_FIELDS = {"kind", "path", "sha256"}
_INVOCATION_RECEIPT_FIELDS = {
    "schema_version", "protocol", "phase", "receipt_type", "variant",
    "model_family", "model_id", "run_id", "invocation", "uid", "gid", "user",
    "command_argv", "started_at", "ended_at", "exit_code", "solver_stopped",
    "descendants_stopped", "isolation", "protected_before", "protected_after",
    "protected_unchanged", "dependency_inventory_sha256",
    "runtime_inventory_sha256", "isolation_probes", "landlock", "stdout_log",
    "dedicated_uid_quiescence", "previous_receipt_sha256", "chain_sha256",
    "launch_authorization_sha256",
    "model_broker",
}
_INVOCATION_AGGREGATE_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "uid", "invocation_count", "receipts",
    "chain_sha256", "all_exit_zero", "all_protected_unchanged", "all_stopped",
    "filesystem_answer_blind", "network_answer_blind", "all_uid_quiescent",
    "dependency_inventory_sha256", "runtime_inventory_sha256",
    "launch_authorization_sha256",
    "model_brokers",
}
_INVOCATION_BROKER_EVIDENCE_FIELDS = {
    "invocation", "ready_receipt_sha256", "transcript_sha256",
}
_STRUCTURED_SOLVER_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "adapter", "request_profile", "tools_enabled", "store",
    "scope_ids", "bundle", "controller_binary_sha256", "transport", "targets",
    "source_first_precommit_sha256", "all_targets_finalized", "request_count",
    "request_response_chain_sha256",
}
_STRUCTURED_SOLVER_BUNDLE_FIELDS = {"path", "sha256", "row_count", "ids"}
_STRUCTURED_TARGET_FIELDS = {
    "id", "source_report", "adapter", "problem_projection_sha256",
    "prepared_blueprint", "attempts", "accepted_attempt",
    "final_artifacts", "target_chain_sha256",
}
_STRUCTURED_ATTEMPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "model_family",
    "model_id", "run_id", "target_id", "attempt", "previous_attempt_sha256",
    "adapter", "adapter_provenance", "request_profile", "tools_enabled", "store", "problem_projection_sha256",
    "prior_diagnostics_sha256", "request", "response", "submission",
    "constructed_candidate_sha256", "staged_artifacts", "status",
    "diagnostics", "artifacts", "attempt_chain_sha256",
}
_STRUCTURED_ARTIFACT_NAMES = {"candidate", "lean", "blueprint"}
_STRUCTURED_ARTIFACT_FIELDS = {"path", "sha256"}
_STRUCTURED_SUBMISSION_FIELDS = {
    "raw_result", "reported_result", "candidate_domain_derivation",
    "lean_declarations", "lean_source", "blueprint",
}
_STRUCTURED_TRANSPORT_KIMI_FIELDS = {"kind", "ready_receipt", "transcript"}
_STRUCTURED_TRANSPORT_GPT_FIELDS = {"kind", "exchanges", "exchange_chain_sha256"}
_STRUCTURED_KIMI_PROVENANCE_FIELDS = {
    "endpoint", "request_sha256", "raw_response_sha256", "reasoning_control",
}
_STRUCTURED_GPT_PROVENANCE_FIELDS = {
    "proxy_receipt", "normalized_response_sha256", "upstream_raw_sse_sha256",
    "event_count",
}
_STRUCTURED_FAILURE_PROVENANCE_FIELDS = {"transport_failure_receipt"}
_LOGIN_PROXY_RECEIPT_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id", "target_id",
    "attempt", "model_id", "adapter", "proxy_binary_sha256", "codex_binary",
    "codex_version", "command_argv", "caller_body_sha256",
    "pre_registered_request", "upstream_origin", "upstream_status",
    "upstream_raw_sse", "normalized_response", "caller_header_names",
    "forwarded_header_names", "completed_event_count", "codex_exit_code",
    "codex_jsonl", "codex_stderr", "codex_last_message", "tool_events",
}
_STRUCTURED_TRANSPORT_FAILURE_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "target_id", "attempt",
    "adapter", "request", "provider_invocation_started", "status",
}
_STRUCTURED_TRANSPORT_FAILURE_DIAGNOSTIC_FIELDS = (
    _STRUCTURED_TRANSPORT_FAILURE_FIELDS | {"diagnostic"}
)
_STRUCTURED_TRANSPORT_FAILURE_CHANNEL_DIAGNOSTIC_FIELDS = (
    _STRUCTURED_TRANSPORT_FAILURE_FIELDS
    | {"diagnostic_stdout", "diagnostic_stderr"}
)
_STRUCTURED_TRANSPORT_FAILURE_GPT_RESPONSE_FIELDS = (
    _STRUCTURED_TRANSPORT_FAILURE_CHANNEL_DIAGNOSTIC_FIELDS
    | {"upstream_raw_sse", "normalized_response", "response_structure"}
)
_STRUCTURED_TRANSPORT_FAILURE_GPT_RAW_FIELDS = (
    _STRUCTURED_TRANSPORT_FAILURE_CHANNEL_DIAGNOSTIC_FIELDS
    | {"upstream_raw_sse", "response_headers", "response_structure"}
)
_STRUCTURED_REQUEST_PROFILE = "tool_free_structured_solver_v1"
_STRUCTURED_DIAGNOSTIC_FIELDS = {"kind", "message", "line", "column"}
_STRUCTURED_DIAGNOSTIC_KINDS = {"controller_scan", "lean_compile"}
_MAX_STRUCTURED_ATTEMPTS = 16
_MAX_PROVIDER_RESPONSE_BYTES = 64 * 1024 * 1024
_LANDLOCK_FIELDS = {
    "abi", "handled_access_fs", "read_only_paths", "read_write_paths",
    "deny_by_default", "no_new_privs", "enforced", "handled_access_net",
    "allowed_bind_tcp_ports", "allowed_connect_tcp_ports",
    "network_deny_by_default",
}
_ISOLATION_PROBE_FIELDS = {"open_read_denied", "errno"}
_PROTECTED_INVENTORY_FIELDS = {"files", "aggregate_sha256"}
_STDOUT_LOG_FIELDS = {"path", "sha256", "size"}
_UID_QUIESCENCE_FIELDS = {
    "mechanism", "uid", "rlimit_nproc", "quiescent_before", "before_pids",
    "prlimit_zero_applied", "pidfd_kill_used", "kill_rounds",
    "quiet_period_ms", "after_pids", "quiescent_after",
}
_FORMAL_REVIEW_CHECKS = {
    "source_faithfulness",
    "derivability",
    "abstraction_sufficiency",
    "uncertainty_propagation",
    "branch_orientation",
    "countermodel_resistance",
}
_FORMAL_REVIEW_NA_CHECKS = {"uncertainty_propagation", "branch_orientation"}
_FORMAL_REVIEW_PASS = {"pass", "passed", "approved", "review-passing", "review_passing"}
_FORMAL_REVIEW_NA = {"not_applicable", "not applicable", "n/a", "na"}
_FORMAL_BRIDGE_PASS = {"covered", "grounded", "encoded", "proved", "pass", "passed"}
# The root umbrella is controller-generated and immutable.  Finalization
# rewrites only the scoped ``IChO2026Problems/All.lean`` before sealing.
_MUTABLE_SEED_PATHS: set[str] = set()
_SOLVER_MUTABLE_PATHS = {
    "IChO2026Problems",
    "blind_candidates",
    "blueprint",
    ".lake/build",
    ".lake/config",
    ".archon/logs",
    ".archon/task_results",
    ".archon/proof-journal",
    ".archon/iter",
    ".archon/tmp",
    ".archon/preflight",
    ".archon/git-dir",
    "IChO2026Problems/All.lean",
    ".archon/PROGRESS.md",
    ".archon/AUTO_NOTES.md",
    ".archon/FORMALIZATION_REVIEW_GATE.md",
    ".archon/PROOF_REVIEW_GATE.md",
    FORMALIZATION_GATE,
    PROOF_GATE,
    ".archon/STRATEGY.md",
    ".archon/PROJECT_STATUS.md",
    ".archon/task_done.md",
    ".archon/task_pending.md",
    ".archon/ARCHON_MEMORY.md",
    ".archon/USER_HINTS.md",
    ".archon/last_lake_build.log",
    ".archon/sync_leanok-state.json",
}
_LANDLOCK_ABI4_RIGHTS = [
    "execute", "write_file", "read_file", "read_dir", "remove_dir",
    "remove_file", "make_char", "make_dir", "make_reg", "make_sock",
    "make_fifo", "make_block", "make_sym", "refer", "truncate",
]

RESULT_KINDS = {"numeric", "symbolic", "classification", "underdetermined"}
GRADE_RESULTS = {
    "exact_match",
    "official_conflict",
    "underdetermined",
    "manual_review",
}
_GRADING_OVERRIDE_FIELDS = {
    "schema_version",
    "official_answer_sha256",
    "reason_code",
    "canonical_answer",
    "accepted_legacy_answers",
}
_MAX_GRADING_OVERRIDE_ALIASES = 8
_MAX_GRADING_OVERRIDE_REASON_CODE_LENGTH = 128

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_SAFE_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
_QUALIFIED_DECLARATION_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
_PROHIBITED_LEAN_RE = re.compile(
    r"\b(?:sorry|admit|axiom|constant|native_decide|sorryAx|unsafe|opaque)\b|"
    r"@\[(?:implemented_by|extern|csimp)\b"
)
_PROHIBITED_LEAN_COMMAND_RE = re.compile(
    r"(?m)@\[|^\s*attribute\b|"
    r"^\s*(?:local\s+)?(?:instance|notation|infix[lr]?|prefix|postfix)\b|"
    r"^\s*open\s+scoped\b|"
    r"\b(?:syntax(?:_cat)?|macro(?:_rules)?|elab(?:_rules)?|"
    r"command_elab|term_elab|tactic|CommandElab|TermElab|Tactic|"
    r"Lean\.Elab|IO(?:\.|\b)|System(?:\.|\b)|process|spawn|"
    r"initialize|builtin_initialize|foreign|run_cmd|run_tac|run_term_elab|"
    r"include_str|include_bytes)\b|^\s*scoped\b|"
    r"^\s*#(?:eval|reduce|check|print|synth|guard|compile|lint)\b"
)
_IMPORT_RE = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$")
_IMPORT_TOKEN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
_TRUSTED_IMPORT_ROOTS = {
    "Aesop",
    "Batteries",
    "Mathlib",
    "PhysLean",
}
_MAX_NUMERIC_TEXT_LENGTH = 256
_MAX_NUMERIC_COEFFICIENT_DIGITS = 192
_MAX_NUMERIC_EXPONENT_ABS = 1000
_MAX_REPORTED_PRECISION_DIGITS = 100
_MAX_JSON_BYTES = 8 * 1024 * 1024
_MAX_CONTROLLER_SEAL_BYTES = 64 * 1024 * 1024
_MAX_ARTIFACT_BYTES = 256 * 1024 * 1024
_MAX_INVENTORY_FILES = 250_000
_MAX_INVENTORY_TOTAL_BYTES = 32 * 1024 * 1024 * 1024
_REQUESTED_OUTPUT_FIELDS = {
    "id", "source_requirement", "kind", "unit", "reporting_policy",
}
_REQUESTED_OUTPUT_KINDS = {
    "numeric", "integer", "formula", "classification", "finite_set",
}
_BOUNDED_DECIMAL_RE = re.compile(
    r"^[+-]?(?P<mantissa>(?:\d+(?:\.\d*)?|\.\d+))"
    r"(?:[eE](?P<exponent>[+-]?\d+))?$"
)
_BOUNDED_RATIONAL_RE = re.compile(r"^(?P<num>-?\d+)/(?P<den>[1-9]\d*)$")
_NUMBER_RE = re.compile(
    r"(?<![A-Za-z0-9_.])"
    r"[+-]?(?:(?:\d+(?:\.\d*)?)|(?:\.\d+))(?:[eE][+-]?\d+)?"
    r"(?![A-Za-z0-9_.])"
)
_SCI_TIMES_TEN_RE = re.compile(
    r"([+-]?(?:(?:\d+(?:\.\d*)?)|(?:\.\d+)))\s*"
    r"(?:[xX*×·])\s*10\s*(?:\^|\*\*)?\s*([+-]?\d+)"
)

_CANDIDATE_FIELDS = {
    "schema_version",
    "protocol",
    "phase",
    "evaluation_mode",
    "official_answer_seen",
    "id",
    "blind_record_sha256",
    "result_kind",
    "raw_result",
    "reported_result",
    "reporting_rule_source",
    "tolerance_provenance",
    "candidate_domain_provenance",
    "lean_declarations",
    "lean_result_contracts",
}
_RAW_RESULT_FIELDS = {
    "expression",
    "lean_expression",
    "derivation_spec",
    "certified_interval",
    "value",
    "unit",
}
_REPORTED_RESULT_FIELDS = {
    "value",
    "text",
    "lean_expression",
    "unit",
    "precision",
    "rounding_rule",
}
_LEAKAGE_KEY_TOKENS = {
    "answer",
    "answers",
    "solution",
    "solutions",
    "marking",
    "rubric",
    "grader",
    "explanation",
    "reasoning",
    "reusable_conclusion",
    "reusable_conclusions",
}


class BlindEvaluationError(RuntimeError):
    """A fail-closed answer-blind protocol violation."""


def _fail(message: str) -> NoReturn:
    raise BlindEvaluationError(message)


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_plain_file_streaming(
    path: Path, *, label: str, max_bytes: int
) -> tuple[str, int]:
    """Hash one regular file without loading an inventory payload into memory."""
    if path.is_symlink():
        _fail(f"{label} must be a regular, non-symlink file: {path}")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    fd: int | None = None
    try:
        fd = os.open(path, flags)
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            _fail(f"{label} must be a regular, non-symlink file: {path}")
        if before.st_size > max_bytes:
            _fail(f"{label} exceeds the {max_bytes}-byte safety limit: {path}")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                _fail(f"{label} exceeds the {max_bytes}-byte safety limit: {path}")
            digest.update(chunk)
        after = os.fstat(fd)
        identity_before = (
            before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
        )
        identity_after = (
            after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
        )
        if total != before.st_size or identity_after != identity_before:
            _fail(f"{label} changed while it was being inventoried: {path}")
        return digest.hexdigest(), total
    except OSError as exc:
        _fail(f"cannot read {label} {path}: {exc}")
    finally:
        if fd is not None:
            os.close(fd)


def _read_plain_bytes(
    path: Path, *, label: str, max_bytes: int = _MAX_ARTIFACT_BYTES
) -> bytes:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a regular, non-symlink file: {path}")
    try:
        size = path.stat(follow_symlinks=False).st_size
        if size > max_bytes:
            _fail(f"{label} exceeds the {max_bytes}-byte safety limit: {path}")
        return path.read_bytes()
    except OSError as exc:
        _fail(f"cannot read {label} {path}: {exc}")


def _read_json(
    path: Path, *, label: str, max_bytes: int = _MAX_JSON_BYTES
) -> tuple[dict[str, Any], bytes]:
    payload = _read_plain_bytes(path, label=label, max_bytes=max_bytes)
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _fail(f"invalid JSON in {label} {path}: {exc}")
    if not isinstance(value, dict):
        _fail(f"{label} must contain one JSON object: {path}")
    return value, payload


def _atomic_write_new(
    path: Path, payload: bytes, *, mode: int | None = None
) -> None:
    """Durably publish one new file without exposing a partial manifest."""
    path = path.resolve()
    if path.exists() or path.is_symlink():
        _fail(f"refusing to overwrite existing output: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            if mode is not None:
                os.fchmod(handle.fileno(), mode)
            os.fsync(handle.fileno())
        try:
            os.replace(tmp, path)
        except OSError as exc:
            _fail(f"could not atomically publish {path}: {exc}")
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = -1
        if directory_fd >= 0:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass


def _project_path(project: Path | str) -> Path:
    path = Path(project).resolve()
    if not path.is_dir():
        _fail(f"project directory does not exist: {path}")
    return path


def _inside_project(path: Path, project: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(project).as_posix()
    except (OSError, ValueError):
        _fail(f"{label} must stay inside the project: {path}")


def _project_path_without_symlinks(path: Path, project: Path, *, label: str) -> Path:
    """Resolve a project path only after rejecting symlink traversal."""
    project = project.resolve()
    lexical = Path(os.path.abspath(path))
    try:
        relative = lexical.relative_to(project)
    except ValueError:
        _fail(f"{label} must stay inside the project: {path}")
    cursor = project
    for part in relative.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            _fail(f"{label} may not traverse a symlink: {cursor}")
    resolved = lexical.resolve()
    _inside_project(resolved, project, label=label)
    return resolved


def _resolve_project_locator(project: Path, raw: object, *, label: str) -> Path:
    if not isinstance(raw, str) or not raw.strip() or "\\" in raw:
        _fail(f"invalid {label} path: {raw!r}")
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        _fail(f"{label} must be a project-relative path: {raw!r}")
    return _project_path_without_symlinks(project / relative, project, label=label)


def _parse_bool_attestation(value: bool | str, *, name: str) -> bool:
    if isinstance(value, bool):
        return value
    token = str(value).strip().lower()
    if token in {"true", "1", "yes"}:
        return True
    if token in {"false", "0", "no"}:
        return False
    _fail(f"{name} must be true or false")


def _require_nonempty_string(value: object, *, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        _fail(f"{field} must be a non-empty string")
    return value.strip()


def _require_sha256(value: object, *, field: str) -> str:
    digest = str(value or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        _fail(f"{field} must be a lowercase SHA-256 digest")
    return digest


def _normalized_key(key: object) -> str:
    snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", str(key).strip())
    return re.sub(r"[^a-z0-9]+", "_", snake.lower()).strip("_")


def _key_tokens(key: object) -> set[str]:
    normalized = _normalized_key(key)
    tokens = {part for part in normalized.split("_") if part}
    tokens.add(normalized)
    return tokens


def _find_leakage_keys(
    value: Any,
    *,
    path: str,
    allow_official_seen: bool = True,
) -> list[str]:
    found: list[str] = []
    blind_metadata_keys = {
        "official_answer_seen",
        "filesystem_answer_blind",
        "network_answer_blind",
    }
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key)
            normalized = _normalized_key(key)
            child_path = f"{path}.{key}"
            if normalized in {"answer_independence", "answer_smuggling"}:
                pass
            elif allow_official_seen and normalized in blind_metadata_keys:
                if normalized == "official_answer_seen" and child is not False:
                    found.append(child_path)
            else:
                tokens = _key_tokens(key)
                if any(
                    token == stem or token == f"{stem}s"
                    for token in tokens
                    for stem in _LEAKAGE_KEY_TOKENS
                ):
                    found.append(child_path)
            found.extend(
                _find_leakage_keys(
                    child,
                    path=child_path,
                    allow_official_seen=allow_official_seen,
                )
            )
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(
                _find_leakage_keys(
                    child,
                    path=f"{path}[{index}]",
                    allow_official_seen=allow_official_seen,
                )
            )
    return found


def _validate_json_value(value: Any, *, field: str) -> None:
    """Require a non-empty, finite JSON provenance value."""
    if value is None or value == "" or value == [] or value == {}:
        _fail(f"{field} must contain explicit provenance")
    if isinstance(value, float) and (value != value or value in {float("inf"), -float("inf")}):
        _fail(f"{field} contains a non-finite number")
    try:
        json.dumps(value, allow_nan=False)
    except (TypeError, ValueError) as exc:
        _fail(f"{field} is not valid finite JSON: {exc}")


def _validate_bounded_numeric_text(
    value: object, *, field: str, allow_rational: bool
) -> None:
    """Reject adversarially large exact numbers before Decimal/Fraction parsing."""
    if not isinstance(value, str) or value != value.strip() or not value:
        _fail(f"{field} must be an exact JSON string")
    if len(value) > _MAX_NUMERIC_TEXT_LENGTH:
        _fail(f"{field} exceeds the bounded numeric text length")
    rational = _BOUNDED_RATIONAL_RE.fullmatch(value) if allow_rational else None
    if rational is not None:
        if max(
            len(rational.group("num").lstrip("-")), len(rational.group("den"))
        ) > _MAX_NUMERIC_COEFFICIENT_DIGITS:
            _fail(f"{field} exceeds the bounded rational coefficient length")
        return
    decimal = _BOUNDED_DECIMAL_RE.fullmatch(value)
    if decimal is None:
        _fail(f"{field} is not a bounded decimal value")
    coefficient_digits = sum(character.isdigit() for character in decimal.group("mantissa"))
    if coefficient_digits > _MAX_NUMERIC_COEFFICIENT_DIGITS:
        _fail(f"{field} exceeds the bounded decimal coefficient length")
    exponent = int(decimal.group("exponent") or "0")
    if abs(exponent) > _MAX_NUMERIC_EXPONENT_ABS:
        _fail(f"{field} exponent exceeds the bounded verifier range")


def _bounded_fraction(value: object, *, field: str) -> Fraction:
    """Parse only text which has already passed the bounded exact-number grammar."""
    _validate_bounded_numeric_text(value, field=field, allow_rational=True)
    assert isinstance(value, str)
    try:
        if "/" in value:
            numerator, denominator = value.split("/", 1)
            result = Fraction(int(numerator), int(denominator))
        else:
            result = Fraction(Decimal(value))
    except (InvalidOperation, ValueError, ZeroDivisionError) as exc:
        _fail(f"{field} is not a valid bounded exact number: {exc}")
    return result


def _validate_candidate(
    candidate: dict[str, Any],
    *,
    expected_id: str,
    expected_blind_hash: str,
) -> dict[str, Any]:
    missing = sorted(_CANDIDATE_FIELDS - set(candidate))
    extra = sorted(set(candidate) - _CANDIDATE_FIELDS)
    if missing or extra:
        pieces = []
        if missing:
            pieces.append("missing " + ", ".join(missing))
        if extra:
            pieces.append("unexpected " + ", ".join(extra))
        _fail(f"candidate {expected_id} has invalid fields: {'; '.join(pieces)}")

    leakage = _find_leakage_keys(candidate, path=f"candidate[{expected_id}]")
    if leakage:
        _fail(
            f"candidate {expected_id} contains solution/grader leakage field(s): "
            + ", ".join(leakage)
        )
    if candidate.get("schema_version") != SCHEMA_VERSION:
        _fail(f"candidate {expected_id} requires schema_version=1")
    if candidate.get("protocol") != PROTOCOL:
        _fail(f"candidate {expected_id} has an unsupported protocol")
    if candidate.get("phase") != "solve":
        _fail(f"candidate {expected_id} requires phase=solve")
    if candidate.get("evaluation_mode") != "answer_blind":
        _fail(f"candidate {expected_id} requires evaluation_mode=answer_blind")
    if candidate.get("official_answer_seen") is not False:
        _fail(f"candidate {expected_id} requires official_answer_seen=false")
    if candidate.get("id") != expected_id:
        _fail(f"candidate id does not match source report: {expected_id}")
    candidate_hash = _require_sha256(
        candidate.get("blind_record_sha256"),
        field=f"candidate {expected_id}.blind_record_sha256",
    )
    if candidate_hash != expected_blind_hash:
        _fail(f"candidate {expected_id} is bound to a different blind record")

    result_kind = str(candidate.get("result_kind") or "").strip().lower()
    if result_kind not in RESULT_KINDS:
        _fail(f"candidate {expected_id} has unsupported result_kind {result_kind!r}")

    raw = candidate.get("raw_result")
    if not isinstance(raw, dict):
        _fail(f"candidate {expected_id}.raw_result must be an object")
    raw_extra = sorted(set(raw) - _RAW_RESULT_FIELDS)
    if raw_extra:
        _fail(
            f"candidate {expected_id}.raw_result has unexpected fields: "
            + ", ".join(raw_extra)
        )
    _require_nonempty_string(
        raw.get("expression"), field=f"candidate {expected_id}.raw_result.expression"
    )
    if result_kind == "numeric":
        interval = raw.get("certified_interval")
        if not isinstance(interval, Mapping) or set(interval) != {"lower", "upper"}:
            _fail(
                f"candidate {expected_id}.raw_result.certified_interval must "
                "contain exactly lower and upper"
            )
        _require_nonempty_string(
            raw.get("derivation_spec"),
            field=f"candidate {expected_id}.raw_result.derivation_spec",
        )
        _validate_bounded_numeric_text(
            raw.get("value"), field=f"candidate {expected_id}.raw_result.value",
            allow_rational=True,
        )
        for bound in ("lower", "upper"):
            _validate_bounded_numeric_text(
                interval.get(bound),
                field=(
                    f"candidate {expected_id}.raw_result.certified_interval.{bound}"
                ),
                allow_rational=True,
            )
        lower = _bounded_fraction(
            interval.get("lower"),
            field=f"candidate {expected_id}.raw_result.certified_interval.lower",
        )
        upper = _bounded_fraction(
            interval.get("upper"),
            field=f"candidate {expected_id}.raw_result.certified_interval.upper",
        )
        if lower >= upper:
            _fail(
                f"candidate {expected_id}.raw_result.certified_interval must be "
                "a non-degenerate independently proved enclosure"
            )
    for key, value in raw.items():
        if key != "expression" and value is not None:
            _validate_json_value(value, field=f"candidate {expected_id}.raw_result.{key}")

    reported = candidate.get("reported_result")
    if not isinstance(reported, dict):
        _fail(f"candidate {expected_id}.reported_result must be an object")
    if "value" not in reported:
        _fail(f"candidate {expected_id}.reported_result.value is required")
    reported_extra = sorted(set(reported) - _REPORTED_RESULT_FIELDS)
    if reported_extra:
        _fail(
            f"candidate {expected_id}.reported_result has unexpected fields: "
            + ", ".join(reported_extra)
        )
    reported_value = reported.get("value")
    if result_kind != "underdetermined" and (
        reported_value is None or reported_value == ""
    ):
        _fail(f"candidate {expected_id}.reported_result.value is empty")
    if reported_value is not None and not isinstance(
        reported_value, (str, int, float, dict)
    ):
        _fail(
            f"candidate {expected_id}.reported_result.value must be a JSON "
            "scalar or structured multi-output object"
        )
    if isinstance(reported_value, bool):
        _fail(f"candidate {expected_id}.reported_result.value may not be boolean")
    for name in ("text", "unit", "rounding_rule"):
        if name in reported and reported[name] is not None and not isinstance(
            reported[name], str
        ):
            _fail(f"candidate {expected_id}.reported_result.{name} must be a string")
    if result_kind == "numeric":
        _validate_bounded_numeric_text(
            reported_value,
            field=f"candidate {expected_id}.reported_result.value",
            allow_rational=False,
        )
        precision = reported.get("precision")
        if isinstance(precision, Mapping):
            digits = precision.get("digits")
            if (
                not isinstance(digits, int)
                or isinstance(digits, bool)
                or not 0 <= digits <= _MAX_REPORTED_PRECISION_DIGITS
            ):
                _fail(
                    f"candidate {expected_id}.reported_result.precision.digits "
                    "is outside the bounded verifier range"
                )
        if _one_decimal(reported_value) is None:
            _fail(f"candidate {expected_id}.reported_result.value is not one numeric value")
    for key, value in reported.items():
        if value is not None:
            _validate_json_value(
                value, field=f"candidate {expected_id}.reported_result.{key}"
            )

    for name in (
        "reporting_rule_source",
        "tolerance_provenance",
        "candidate_domain_provenance",
    ):
        _validate_json_value(candidate.get(name), field=f"candidate {expected_id}.{name}")

    declarations = candidate.get("lean_declarations")
    if not isinstance(declarations, list) or not declarations:
        _fail(f"candidate {expected_id}.lean_declarations must be a non-empty list")
    if any(not isinstance(item, str) or not item.strip() for item in declarations):
        _fail(f"candidate {expected_id}.lean_declarations contains an invalid name")
    if len(set(declarations)) != len(declarations):
        _fail(f"candidate {expected_id}.lean_declarations contains duplicates")
    result_contract_errors = validate_blind_result_contracts(candidate)
    if result_contract_errors:
        _fail(
            f"candidate {expected_id} has invalid Lean result contract(s): "
            + "; ".join(result_contract_errors)
        )
    return candidate


def _validate_candidate_source_policies(
    candidate: Mapping[str, Any],
    *,
    source_entry: Mapping[str, Any],
    record_id: str,
) -> None:
    """Bind solver reporting/tolerance choices to pre-solve source policy."""
    reporting_policy = source_entry.get("reporting_policy")
    if not isinstance(reporting_policy, Mapping) or not reporting_policy:
        _fail(f"source report {record_id} has no predeclared reporting_policy")
    requested_outputs = source_entry.get("requested_outputs")
    if not isinstance(requested_outputs, list) or not requested_outputs:
        _fail(f"source report {record_id} has no predeclared requested_outputs")
    requested_ids: set[str] = set()
    for index, output in enumerate(requested_outputs, start=1):
        if not isinstance(output, Mapping):
            _fail(f"source report {record_id} requested output {index} is invalid")
        _strict_fields(
            output, _REQUESTED_OUTPUT_FIELDS,
            label=f"source report {record_id} requested output {index}",
        )
        output_id = _require_nonempty_string(
            output.get("id"), field=f"source report {record_id} requested output id"
        )
        if output_id in requested_ids:
            _fail(f"source report {record_id} has duplicate requested output id")
        requested_ids.add(output_id)
        kind = output.get("kind")
        if kind not in _REQUESTED_OUTPUT_KINDS:
            _fail(f"source report {record_id} requested output kind is invalid")
        _require_nonempty_string(
            output.get("source_requirement"),
            field=f"source report {record_id} requested output requirement",
        )
        policy = output.get("reporting_policy")
        if not isinstance(policy, Mapping) or not policy:
            _fail(f"source report {record_id} requested output policy is invalid")
        policy_kind = policy.get("kind")
        if kind == "numeric" and policy_kind not in {
            "decimal_places", "significant_figures",
        }:
            _fail(f"source report {record_id} numeric output policy is invalid")
        expected_kind = {
            "integer": "exact_integer",
            "formula": "exact_symbolic",
            "classification": "exact_symbolic",
            "finite_set": "exact_symbolic",
        }.get(str(kind))
        if expected_kind is not None and policy_kind != expected_kind:
            _fail(f"source report {record_id} output policy does not match its kind")
    if len(requested_outputs) > 1 and reporting_policy.get("final_precision") != {
        "kind": "per_requested_output", "source": "requested_outputs"
    }:
        _fail(f"source report {record_id} multi-output policy must be per-output")
    if len(requested_outputs) > 1 and candidate.get("result_kind") != "symbolic":
        _fail(f"candidate {record_id} must use symbolic result_kind for multiple outputs")
    if len(requested_outputs) > 1:
        raw = candidate.get("raw_result")
        reported = candidate.get("reported_result")
        raw_values = raw.get("value") if isinstance(raw, Mapping) else None
        structured = reported.get("value") if isinstance(reported, Mapping) else None
        if (
            not isinstance(raw_values, dict)
            or not isinstance(structured, dict)
            or set(raw_values) != requested_ids
            or set(structured) != requested_ids
        ):
            _fail(
                f"candidate {record_id} multi-output raw/reported values must be "
                "objects with exactly the requested output IDs"
            )
        for output in requested_outputs:
            assert isinstance(output, Mapping)
            output_id = str(output["id"])
            spec = raw_values[output_id]
            if not isinstance(spec, Mapping):
                _fail(f"candidate {record_id}/{output_id} raw spec is invalid")
            _validate_source_first_result_spec(
                spec, output_kind=output.get("kind"), record_id=record_id,
                output_id=output_id,
            )
            item = structured[output_id]
            if not isinstance(item, Mapping):
                _fail(f"candidate {record_id}/{output_id} reported item is invalid")
            _strict_fields(
                item, _MULTI_REPORTED_ITEM_FIELDS,
                label=f"candidate {record_id}/{output_id} reported item",
            )
            if item.get("status") != spec.get("status"):
                _fail(f"candidate {record_id}/{output_id} raw/reported statuses disagree")
            if spec.get("status") == "underdetermined":
                if item.get("value") is not None:
                    _fail(
                        f"candidate {record_id}/{output_id} underdetermined output "
                        "must have value=null"
                    )
                continue
            kind = output.get("kind")
            expected_value: object
            if kind == "numeric":
                expected_value = spec.get("reported_value")
                _validate_bounded_numeric_text(
                    item.get("value"),
                    field=f"candidate {record_id}/{output_id} numeric reported value",
                    allow_rational=False,
                )
            elif kind == "integer":
                expected_value = spec.get("value")
            elif kind in {"formula", "classification"}:
                expected_value = spec.get("normalized_result")
            else:
                expected_value = spec.get("normalized_members")
            if kind == "numeric":
                values_match = _bounded_fraction(
                    item.get("value"),
                    field=f"candidate {record_id}/{output_id} numeric reported value",
                ) == _bounded_fraction(
                    expected_value,
                    field=f"candidate {record_id}/{output_id} raw spec reported value",
                )
            else:
                values_match = item.get("value") == expected_value
            if not values_match:
                _fail(
                    f"candidate {record_id}/{output_id} reported value differs "
                    "from its raw structured spec"
                )
    if len(requested_outputs) == 1 and requested_outputs[0].get("kind") == "numeric":
        if reporting_policy.get("final_precision") != requested_outputs[0].get(
            "reporting_policy"
        ):
            _fail(f"source report {record_id} single numeric policies disagree")
    if candidate.get("reporting_rule_source") != reporting_policy:
        _fail(
            f"candidate {record_id}.reporting_rule_source must exactly equal "
            "the source reporting_policy"
        )
    measurement_policy = source_entry.get("measurement_policy")
    if not isinstance(measurement_policy, Mapping) or not measurement_policy:
        _fail(f"source report {record_id} has no predeclared measurement_policy")
    tolerance = candidate.get("tolerance_provenance")
    if not isinstance(tolerance, Mapping) or tolerance.get(
        "measurement_policy"
    ) != measurement_policy:
        _fail(
            f"candidate {record_id}.tolerance_provenance.measurement_policy must "
            "exactly equal the source measurement_policy"
        )
    domain_policy = source_entry.get("candidate_domain_policy")
    if not isinstance(domain_policy, Mapping) or not domain_policy:
        _fail(f"source report {record_id} has no predeclared candidate_domain_policy")
    domain_provenance = candidate.get("candidate_domain_provenance")
    if (
        not isinstance(domain_provenance, Mapping)
        or set(domain_provenance) != {"candidate_domain_policy", "derivation"}
        or domain_provenance.get("candidate_domain_policy") != domain_policy
        or not isinstance(domain_provenance.get("derivation"), Mapping)
        or not domain_provenance.get("derivation")
    ):
        _fail(
            f"candidate {record_id}.candidate_domain_provenance must bind the "
            "exact source candidate_domain_policy and structured derivation"
        )
    reported = candidate.get("reported_result")
    if not isinstance(reported, Mapping):  # already rejected by schema validation
        _fail(f"candidate {record_id}.reported_result must be an object")
    if reported.get("rounding_rule") != reporting_policy.get("tie_rule"):
        _fail(
            f"candidate {record_id}.reported_result.rounding_rule must equal "
            "source reporting_policy.tie_rule"
        )
    if candidate.get("result_kind") == "numeric" and reported.get(
        "precision"
    ) != reporting_policy.get("final_precision"):
        _fail(
            f"candidate {record_id}.reported_result.precision must exactly equal "
            "source reporting_policy.final_precision"
        )


def _strip_lean_comments_and_strings(source: str) -> str:
    """Blank nested Lean comments and strings while preserving line breaks."""
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
            continue
        if block_depth:
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
            continue
        if in_string:
            if current != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
            continue
        if current == "-" and following == "-":
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
        _fail("Lean target has an unterminated comment or string")
    return "".join(chars)


def _validate_lean_target(
    path: Path,
    *,
    project: Path,
    declarations: Iterable[str],
    raw_expression: str | None = None,
    derivation_spec: str | None = None,
    reported_value: str | None = None,
) -> bytes:
    payload = _read_plain_bytes(path, label="Lean target")
    try:
        source = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(f"Lean target is not UTF-8: {path}: {exc}")
    sorry_count = file_open_sorry_count(path)
    if sorry_count is None:
        _fail(f"could not determine the open-sorry count for {path}")
    if sorry_count != 0:
        _fail(f"Lean target must have zero active sorry/admit placeholders: {path}")
    active = _strip_lean_comments_and_strings(source)
    prohibited = _PROHIBITED_LEAN_RE.search(active)
    if prohibited:
        line = active.count("\n", 0, prohibited.start()) + 1
        _fail(
            f"Lean target contains prohibited construction "
            f"{prohibited.group(0)!r} at {path}:{line}"
        )
    prohibited_command = _PROHIBITED_LEAN_COMMAND_RE.search(active)
    if prohibited_command:
        line = active.count("\n", 0, prohibited_command.start()) + 1
        _fail(
            "Lean target contains a command capable of extending or executing "
            f"the elaborator at {path}:{line}"
        )
    imports: list[str] = []
    for match in _IMPORT_RE.finditer(active):
        for module in match.group(1).split():
            if not _IMPORT_TOKEN_RE.fullmatch(module):
                _fail(f"Lean target has an invalid import token {module!r}: {path}")
            imports.append(module)
    if not imports:
        _fail(f"Lean target must import a controller-sealed library module: {path}")
    seed, _ = _read_json(project / SEED_MANIFEST, label="seed isolation manifest")
    seed_payloads = _validated_hash_map(
        seed.get("payload_files"), label="seed payload_files"
    )
    seeded_modules = {
        ".".join(Path(relative).with_suffix("").parts): (relative, digest)
        for relative, digest in seed_payloads.items()
        if relative.endswith(".lean") and relative not in _MUTABLE_SEED_PATHS
    }
    untrusted_imports: list[str] = []
    for module in imports:
        relative = module.replace(".", "/") + ".lean"
        local = project / relative
        seeded = seeded_modules.get(module)
        if local.exists() or local.is_symlink():
            if seeded is None or local.is_symlink() or not local.is_file():
                untrusted_imports.append(module)
                continue
            _seeded_relative, seeded_hash = seeded
            if _sha256_bytes(
                _read_plain_bytes(local, label=f"seeded import {module}")
            ) != seeded_hash:
                _fail(f"Lean target seeded import hash drift: {module}")
        elif module.split(".", 1)[0] not in _TRUSTED_IMPORT_ROOTS:
            untrusted_imports.append(module)
    if untrusted_imports:
        _fail(
            "Lean target imports solver-controlled/unapproved module(s): "
            + ", ".join(untrusted_imports)
        )
    if raw_expression:
        raw_tail = re.escape(raw_expression.rsplit(".", 1)[-1])
        raw_definition = re.search(
            rf"(?m)^\s*(?:noncomputable\s+)?def\s+(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
            rf"{raw_tail}\b[^\n]*:=\s*(?P<rhs>[^\n]+)$",
            active,
        )
        if raw_definition is None:
            _fail(
                "numeric raw_result.lean_expression must name a local, auditable "
                f"definition in {path}: {raw_expression}"
            )
        rhs = raw_definition.group("rhs")
        if re.search(r"(?<![A-Za-z0-9_'])id(?![A-Za-z0-9_'])", rhs):
            _fail(
                "numeric raw carrier may not disguise a submitted literal with id; "
                f"derive the carrier from named problem data: {raw_expression}"
            )
        if reported_value is not None:
            reported_exact = _bounded_fraction(
                reported_value, field="reported result used by Lean source audit"
            )
            for literal in re.findall(
                r"(?<![A-Za-z0-9_'.])[-+]?(?:\d+(?:\.\d*)?|\.\d+)"
                r"(?:[eE][-+]?\d+)?",
                rhs,
            ):
                try:
                    literal_exact = Fraction(Decimal(literal))
                except (InvalidOperation, ValueError, ZeroDivisionError):
                    continue
                if literal_exact == reported_exact:
                    _fail(
                        "numeric raw carrier directly embeds the submitted reported "
                        f"literal: {raw_expression}"
                    )
        identifiers = {
            token
            for token in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", rhs)
            if token not in {"Real", "Rat", "OfScientific"}
        }
        if not identifiers:
            _fail(
                "numeric raw carrier may not be defined directly as the submitted "
                f"decimal/rational: {raw_expression}"
            )
        if derivation_spec:
            spec_tail = re.escape(derivation_spec.rsplit(".", 1)[-1])
            spec_definition = re.search(
                rf"(?ms)^\s*(?:(?:private|protected|noncomputable)\s+)*"
                rf"(?:def|theorem|lemma)\s+(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
                rf"{spec_tail}\b(?P<body>.*?)(?=^\s*(?:(?:private|protected|"
                rf"noncomputable)\s+)*(?:def|theorem|lemma|namespace|end)\b|\Z)",
                active,
            )
            if spec_definition is None:
                _fail(
                    "numeric raw_result.derivation_spec must name a local auditable "
                    f"declaration in {path}: {derivation_spec}"
                )
            spec_body = spec_definition.group("body")
            raw_tail_text = raw_expression.rsplit(".", 1)[-1]
            if not re.search(rf"\b{re.escape(raw_tail_text)}\b", spec_body):
                _fail(
                    "numeric derivation_spec does not bind the independently derived "
                    f"raw carrier: {derivation_spec}"
                )
            if re.search(
                r":\s*(?:Prop\s*:=\s*)?True\s*:=?\s*"
                r"(?:True\b|by\s*(?:trivial\b|simp\b|exact\s+True\.intro\b))?",
                spec_body,
            ):
                _fail("numeric derivation_spec is a trivial truth certificate")
            qualified_raw = rf"(?:[A-Za-z_][A-Za-z0-9_']*\.)*{re.escape(raw_tail_text)}"
            if re.search(
                rf":\s*{qualified_raw}\s*=\s*{qualified_raw}\s*:=",
                spec_body,
            ):
                _fail("numeric derivation_spec is a reflexive raw-carrier tautology")
    declared = {match.group(1) for match in _DECL_RE.finditer(active)}
    tails = {name.rsplit(".", 1)[-1] for name in declared}
    missing = [
        name
        for name in declarations
        if name not in declared and name.rsplit(".", 1)[-1] not in tails
    ]
    if missing:
        _fail(
            f"candidate references declaration(s) absent from {path}: "
            + ", ".join(missing)
        )
    return payload


def _collect_source_contracts(value: Any) -> list[dict[str, Any]]:
    found: list[dict[str, Any]] = []
    if isinstance(value, Mapping):
        raw = value.get("source_contract")
        if isinstance(raw, Mapping):
            found.append(dict(raw))
        for key, child in value.items():
            if key != "source_contract":
                found.extend(_collect_source_contracts(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(_collect_source_contracts(child))
    return found


def _formal_review_certificate(record: Mapping[str, Any]) -> Mapping[str, Any]:
    """Return the one target-bound formal Review certificate, fail closed."""

    certificate = record.get("certificate")
    if not isinstance(certificate, Mapping):
        _fail("formalization Review gate certificate is missing")
    milestones = certificate.get("milestones")
    if milestones is None:
        return certificate
    if (
        not isinstance(milestones, list)
        or len(milestones) != 1
        or not isinstance(milestones[0], Mapping)
    ):
        _fail(
            "formalization Review batch certificate must contain exactly one "
            "target-bound milestone"
        )
    item = milestones[0]
    for field in ("source_contract", "blind_review_certificate"):
        if certificate.get(field) != item.get(field):
            _fail(
                "formalization Review batch wrapper does not exactly bind its "
                f"milestone {field}"
            )
    return item


def _validate_formal_review_semantics(certificate: Mapping[str, Any]) -> None:
    """Revalidate the formal checks and source-to-Lean bridges at freeze."""

    if certificate.get("schema_version") != 2:
        _fail("formalization Review certificate schema is unsupported")
    checks = certificate.get("checks")
    if not isinstance(checks, Mapping) or set(checks) != _FORMAL_REVIEW_CHECKS:
        _fail("formalization Review certificate has incomplete formal checks")
    for name in sorted(_FORMAL_REVIEW_CHECKS):
        check = checks.get(name)
        if not isinstance(check, Mapping):
            _fail(f"formalization Review check {name} must be an object")
        _strict_fields(check, {"status", "evidence"}, label=f"formal Review check {name}")
        status = str(check.get("status") or "").strip().lower()
        allowed = status in _FORMAL_REVIEW_PASS
        if name in _FORMAL_REVIEW_NA_CHECKS:
            allowed = allowed or status in _FORMAL_REVIEW_NA
        if not allowed:
            _fail(f"formalization Review check {name} is not passing")
        _require_nonempty_string(
            check.get("evidence"), field=f"formalization Review check {name}.evidence"
        )
    bridges = certificate.get("bridge_obligations")
    if not isinstance(bridges, list) or not bridges:
        _fail("formalization Review certificate has no source-to-Lean bridge")
    for index, bridge in enumerate(bridges, start=1):
        if not isinstance(bridge, Mapping):
            _fail(f"formalization Review bridge {index} must be an object")
        _strict_fields(
            bridge,
            {"claim", "carrier", "status", "evidence"},
            label=f"formalization Review bridge {index}",
        )
        for field in ("claim", "carrier", "evidence"):
            _require_nonempty_string(
                bridge.get(field), field=f"formalization Review bridge {index}.{field}"
            )
        if str(bridge.get("status") or "").strip().lower() not in _FORMAL_BRIDGE_PASS:
            _fail(f"formalization Review bridge {index} is not passing")


def _validate_gate_record(
    *,
    gate_name: str,
    record: object,
    expected_status: str,
    expected_provenance: dict[str, Any],
    expected_contract: Mapping[str, Any],
    requested_outputs: object,
) -> None:
    if not isinstance(record, dict):
        _fail(f"{gate_name} has no record for the target")
    if record.get("status") != expected_status:
        _fail(
            f"{gate_name} is not passing/current: expected status "
            f"{expected_status!r}, got {record.get('status')!r}"
        )
    contracts = _collect_source_contracts(
        record.get("certificate") if gate_name == "formalization Review gate" else record
    )
    if not contracts:
        _fail(f"{gate_name} has no hash-bound source_contract provenance")
    for provenance in contracts:
        if provenance != expected_provenance:
            _fail(f"{gate_name} source_contract provenance is stale or mismatched")
    if gate_name == "formalization Review gate":
        certificate = _formal_review_certificate(record)
        _validate_formal_review_semantics(certificate)
        review = certificate.get("blind_review_certificate")
    else:
        if record.get("proof_review_schema_version") != 1:
            _fail("proof Review gate schema is unsupported")
        if record.get("proof_review_route") != "solved":
            _fail("proof Review gate does not persist the solved Review route")
        _require_nonempty_string(record.get("reason"), field="proof Review reason")
        _require_nonempty_string(record.get("evidence"), field="proof Review evidence")
        if record.get("redraft_kind") != "not_applicable":
            _fail("a solved proof Review may not retain a redraft classification")
        review = record.get("blind_review_certificate")
    if not isinstance(review, Mapping):
        _fail(f"{gate_name} lacks the complete normalized blind Review certificate")
    error = validate_review_source_certificate(
        review, expected_contract, passing=True
    )
    if error:
        _fail(f"{gate_name} blind Review certificate is invalid: {error}")
    if not isinstance(requested_outputs, list) or not requested_outputs:
        _fail(f"{gate_name} cannot bind an empty requested-output contract")
    review_outputs = review.get("requested_outputs")
    if not isinstance(review_outputs, list):
        _fail(f"{gate_name} requested-output audit is missing")
    requirements = [
        str(item.get("source_requirement") or "").strip()
        for item in requested_outputs
        if isinstance(item, Mapping)
    ]
    covered_requirements = [
        str(item.get("source_requirement") or "").strip()
        for item in review_outputs
        if isinstance(item, Mapping)
    ]
    if covered_requirements != requirements or len(set(covered_requirements)) != len(
        covered_requirements
    ):
        _fail(f"{gate_name} does not exactly cover every bundle requested output")


def _discover_blind_reports(project: Path) -> list[tuple[Path, dict[str, Any], bytes]]:
    report_root = _project_path_without_symlinks(
        project / "reports", project, label="source report directory"
    )
    if not report_root.is_dir():
        _fail(f"source report directory is missing: {report_root}")
    reports: list[tuple[Path, dict[str, Any], bytes]] = []
    for path in sorted(report_root.rglob("*.source.json")):
        report, payload = _read_json(path, label="source report")
        mode = str(report.get("evaluation_mode") or "visible").strip().lower()
        if mode.replace("-", "_") != "answer_blind":
            _fail(f"non-answer-blind source report is present in sealed run: {path}")
        reports.append((path.resolve(), report, payload))
    if not reports:
        _fail("no answer_blind source reports were found under project/reports")
    return reports


def _artifact(
    *,
    project: Path,
    path: Path,
    kind: str,
    payload: bytes | None = None,
) -> dict[str, str]:
    relative = _inside_project(path, project, label=kind)
    content = payload if payload is not None else _read_plain_bytes(path, label=kind)
    return {"kind": kind, "path": relative, "sha256": _sha256_bytes(content)}


def _load_gate(
    project: Path,
    relative: str,
    *,
    label: str,
) -> tuple[Path, dict[str, Any], bytes]:
    path = _project_path_without_symlinks(
        project / relative, project, label=label
    )
    data, payload = _read_json(path, label=label)
    if data.get("version") != 2 or not isinstance(data.get("targets"), dict):
        _fail(f"{label} has an unsupported or invalid state schema")
    return path.resolve(), data, payload


def _hash_index(index: Mapping[str, str]) -> str:
    """Hash a path-to-content-hash mapping in its canonical sorted form."""
    return _sha256_bytes(_json_bytes(dict(sorted(index.items()))))


def _strict_fields(
    value: Mapping[str, Any], expected: set[str], *, label: str
) -> None:
    missing = sorted(expected - set(value))
    extra = sorted(set(value) - expected)
    if missing or extra:
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        _fail(f"{label} has invalid fields: {'; '.join(details)}")


def _strict_id_list(value: object, *, label: str) -> list[str]:
    if not isinstance(value, list) or not value:
        _fail(f"{label} must be a non-empty sorted ID list")
    ids: list[str] = []
    for raw in value:
        identifier = _require_nonempty_string(raw, field=label)
        if not _SAFE_ID_RE.fullmatch(identifier):
            _fail(f"{label} contains unsafe ID {identifier!r}")
        ids.append(identifier)
    if ids != sorted(ids) or len(ids) != len(set(ids)):
        _fail(f"{label} must be sorted and contain no duplicates")
    return ids


def _outside_project(path: Path, project: Path, *, label: str) -> Path:
    resolved = Path(os.path.abspath(path)).resolve()
    try:
        resolved.relative_to(project)
    except ValueError:
        return resolved
    _fail(f"{label} must be controller-owned and outside the solver project")


def _require_controller_owned_readonly(path: Path, *, label: str) -> None:
    try:
        metadata = path.stat(follow_symlinks=False)
    except OSError as exc:
        _fail(f"cannot stat {label} {path}: {exc}")
    if metadata.st_uid != os.geteuid():
        _fail(f"{label} must be owned by the controller UID: {path}")
    if metadata.st_mode & 0o022:
        _fail(f"{label} may not be group/other writable: {path}")


def _controller_output_path(
    raw: Path | str, *, project: Path, label: str
) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = Path.cwd() / path
    path = _outside_project(path, project, label=label)
    if path.parent.is_symlink() or not path.parent.is_dir():
        _fail(f"{label} parent must be a regular directory: {path.parent}")
    _require_controller_owned_readonly(path.parent, label=f"{label} parent")
    return path


def _load_bound_external_receipt(
    *, project: Path, spec: object, label: str,
    max_bytes: int = _MAX_JSON_BYTES,
) -> tuple[Path, dict[str, Any], bytes]:
    if not isinstance(spec, dict):
        _fail(f"controller seal {label} must be an object")
    _strict_fields(spec, _EXTERNAL_RECEIPT_FIELDS, label=f"controller seal {label}")
    raw_path = spec.get("path")
    if not isinstance(raw_path, str) or not Path(raw_path).is_absolute():
        _fail(f"controller seal {label}.path must be absolute")
    path = _outside_project(Path(raw_path), project, label=label)
    _require_controller_owned_readonly(path, label=label)
    value, payload = _read_json(path, label=label, max_bytes=max_bytes)
    expected = _require_sha256(spec.get("sha256"), field=f"controller seal {label}.sha256")
    if _sha256_bytes(payload) != expected:
        _fail(f"{label} hash does not match controller seal")
    return path, value, payload


def _absolute_path_list(value: object, *, label: str) -> list[Path]:
    if not isinstance(value, list) or len(value) != len(set(map(str, value))):
        _fail(f"{label} must be a duplicate-free absolute path list")
    result: list[Path] = []
    for raw in value:
        if not isinstance(raw, str) or not Path(raw).is_absolute():
            _fail(f"{label} must contain absolute paths")
        path = Path(raw).resolve()
        if str(path) != raw:
            _fail(f"{label} contains a noncanonical path: {raw}")
        result.append(path)
    return result


def _load_launch_authorization(
    *, project: Path, seal: Mapping[str, Any]
) -> tuple[dict[str, Any], str]:
    authorization_path, authorization, payload = _load_bound_external_receipt(
        project=project,
        spec=seal.get("launch_authorization"),
        label="Landlock launch authorization",
    )
    _strict_fields(
        authorization,
        _LAUNCH_AUTHORIZATION_FIELDS,
        label="Landlock launch authorization",
    )
    if (
        authorization.get("schema_version") != 1
        or authorization.get("protocol") != PROTOCOL
        or authorization.get("phase") != "landlock_launch_authorization"
    ):
        _fail("Landlock launch authorization has unsupported metadata")
    solver = seal.get("solver")
    if not isinstance(solver, Mapping):
        _fail("controller seal solver is missing")
    aggregate_spec = seal.get("structured_solver_receipt")
    if not isinstance(aggregate_spec, Mapping):
        _fail("controller seal invocation aggregate is missing")
    _aggregate_path, aggregate, _aggregate_payload = _load_bound_external_receipt(
        project=project, spec=aggregate_spec, label="structured solver receipt"
    )
    if (
        authorization.get("variant") != aggregate.get("variant")
        or authorization.get("run_id") != solver.get("run_id")
        or authorization.get("workspace") != str(project)
    ):
        _fail("Landlock launch authorization run/workspace identity is stale")
    dependency = seal.get("dependency_inventory")
    runtime = seal.get("runtime_inventory")
    if not isinstance(dependency, Mapping) or not isinstance(runtime, Mapping):
        _fail("controller seal inventories are missing")
    if (
        authorization.get("dependency_root") != dependency.get("root")
        or authorization.get("runtime_root") != runtime.get("root")
    ):
        _fail("Landlock launch authorization runtime/dependency roots are stale")
    broker_port = authorization.get("allowed_model_broker_tcp_port")
    if (
        not isinstance(broker_port, int)
        or isinstance(broker_port, bool)
        or not 1 <= broker_port <= 65535
    ):
        _fail("Landlock launch authorization broker TCP port is invalid")
    dependency_root = Path(str(dependency.get("root"))).resolve()
    runtime_root = Path(str(runtime.get("root"))).resolve()
    system = authorization.get("system_inventory")
    if not isinstance(system, Mapping):
        _fail("Landlock launch authorization system_inventory is missing")
    _strict_fields(system, _SYSTEM_INVENTORY_FIELDS, label="system_inventory")
    raw_files = system.get("files")
    if not isinstance(raw_files, dict) or not raw_files:
        _fail("system_inventory.files must be a nonempty absolute hash map")
    system_files: dict[str, str] = {}
    broad = {"/", "/usr", "/lib", "/lib64", "/sys", "/proc", "/etc", "/dev"}
    for raw_path, raw_sha in raw_files.items():
        if not isinstance(raw_path, str) or not Path(raw_path).is_absolute():
            _fail("system_inventory contains a non-absolute path")
        path = Path(raw_path).resolve()
        if raw_path != str(path) or str(path) in broad or not path.is_file():
            _fail(f"system_inventory contains a broad/non-file authority: {raw_path}")
        _require_controller_owned_readonly(path, label="system inventory file")
        expected = _require_sha256(raw_sha, field=f"system_inventory[{raw_path}]")
        if _sha256_bytes(_read_plain_bytes(path, label="system inventory file")) != expected:
            _fail(f"system inventory file drift: {raw_path}")
        system_files[str(path)] = expected
    if system.get("files_sha256") != _hash_index(system_files):
        _fail("system inventory digest is invalid")
    system_readonly = _absolute_path_list(
        authorization.get("system_read_only_paths"),
        label="system_read_only_paths",
    )
    safe_devices = {"/dev/null", "/dev/zero", "/dev/random", "/dev/urandom"}
    readonly_strings = set(map(str, system_readonly))
    expected_safe_devices = {
        str(Path(raw).resolve()) for raw in safe_devices if Path(raw).exists()
    }
    if readonly_strings != set(system_files) | expected_safe_devices:
        _fail(
            "system read-only paths must exactly equal the hashed regular-file "
            "inventory plus the fixed safe device allowlist"
        )
    external_writable: dict[str, list[Path]] = {}
    for field in (
        "solver_external_read_write_paths",
        "verifier_external_read_write_paths",
        "reviewer_external_read_write_paths",
    ):
        external_writable[field] = _absolute_path_list(
            authorization.get(field), label=field
        )
    required_probes = set(_absolute_path_list(
        authorization.get("required_denied_probe_paths"),
        label="required_denied_probe_paths",
    ))
    mandatory = {
        Path("/root"), Path("/tmp"), Path("/var/tmp"), Path("/dev/shm"),
        Path("/proc/1/environ"), authorization_path.parent,
    }
    if not mandatory.issubset(required_probes):
        _fail("launch authorization omits mandatory root/temp/proc/controller probes")
    sibling_candidates = required_probes - mandatory
    if len(sibling_candidates) != 1:
        _fail("launch authorization must bind exactly one sibling workspace probe")
    sibling = next(iter(sibling_candidates))
    if any(
        sibling == protected or sibling.is_relative_to(protected)
        or protected.is_relative_to(sibling)
        for protected in (project, runtime_root, dependency_root, authorization_path.parent)
    ):
        _fail("launch authorization sibling probe overlaps trusted/current-run roots")
    protected_roots = {
        project, runtime_root, dependency_root, authorization_path.parent, sibling,
        Path("/root"), Path("/proc/1/environ"),
        *(Path(path) for path in system_files),
    }
    shared_temp_roots = {Path("/tmp"), Path("/var/tmp"), Path("/dev/shm")}
    all_external = [
        (field, path)
        for field, paths in external_writable.items()
        for path in paths
    ]
    for field, path in all_external:
        if any(
            path == protected or path.is_relative_to(protected)
            or protected.is_relative_to(path)
            for protected in protected_roots
        ):
            _fail(f"{field} overlaps controller/system/sibling protected material")
        if any(shared == path or shared.is_relative_to(path) for shared in shared_temp_roots):
            _fail(f"{field} grants broad shared-temporary authority")
    writable_sets = {
        field: set(paths) for field, paths in external_writable.items()
    }
    for first, second in (
        ("solver_external_read_write_paths", "verifier_external_read_write_paths"),
        ("solver_external_read_write_paths", "reviewer_external_read_write_paths"),
        ("verifier_external_read_write_paths", "reviewer_external_read_write_paths"),
    ):
        if writable_sets[first] & writable_sets[second]:
            _fail("solver, verifier and reviewer writable roots must be disjoint")
    return authorization, _sha256_bytes(payload)


def _load_and_validate_model_broker_binding(
    *, project: Path, binding: object, variant: object, run_id: object,
    model_id: object, runtime: object, minimum_requests: int, label: str,
    request_profile: str = "agent_harness_v1",
    exact_requests: int | None = None,
) -> tuple[dict[str, Any], str, dict[str, Any], str]:
    """Revalidate the root-side model boundary and its content-free ledger."""
    if not isinstance(binding, Mapping):
        _fail(f"{label} must be an object")
    _strict_fields(binding, _MODEL_BROKER_BINDING_FIELDS, label=label)
    ready_path, ready, ready_payload = _load_bound_external_receipt(
        project=project,
        spec=binding.get("ready_receipt"),
        label=f"{label} ready receipt",
    )
    transcript_path, transcript, transcript_payload = _load_bound_external_receipt(
        project=project,
        spec=binding.get("transcript"),
        label=f"{label} transcript",
    )
    for path, label in (
        (ready_path, "model broker ready receipt"),
        (transcript_path, "model broker transcript"),
    ):
        mode = path.stat(follow_symlinks=False).st_mode & 0o777
        if mode != 0o400:
            _fail(f"{label} must be controller-owned mode 0400")
    _strict_fields(ready, _MODEL_BROKER_READY_FIELDS, label="model broker ready receipt")
    _strict_fields(
        transcript,
        _MODEL_BROKER_TRANSCRIPT_FIELDS,
        label="model broker transcript",
    )
    broker_model_id = (
        "kimi-k3"
        if variant == "kimi-k3" and request_profile == "agent_harness_v1"
        else model_id
    )
    if (
        ready.get("schema_version") != SCHEMA_VERSION
        or ready.get("protocol") != PROTOCOL
        or ready.get("phase") != "model_broker_ready"
        or ready.get("variant") != variant
        or ready.get("run_id") != run_id
        or ready.get("allowed_model") != broker_model_id
        or ready.get("request_profile") != request_profile
    ):
        _fail("model broker ready receipt disagrees with the sealed solver run")
    listen = urlparse(str(ready.get("listen_url") or ""))
    if (
        listen.scheme not in {"http", "https"}
        or listen.hostname != "127.0.0.1"
        or listen.username is not None
        or listen.password is not None
        or listen.query
        or listen.fragment
    ):
        _fail("model broker listen_url must be a credential-free loopback URL")
    if variant == "kimi-k3":
        expected_path = (
            "" if request_profile == "agent_harness_v1" else "/v1"
        )
        if listen.path.rstrip("/") != expected_path:
            _fail(
                "Kimi model broker listen_url path disagrees with its request profile"
            )
    upstream = urlparse(str(ready.get("upstream_origin") or ""))
    if (
        upstream.scheme != "https"
        or not upstream.hostname
        or upstream.username is not None
        or upstream.password is not None
        or upstream.query
        or upstream.fragment
        or upstream.path not in {"", "/"}
    ):
        _fail("model broker upstream_origin must be a credential-free HTTPS origin")
    expected_origin = (
        "https://chatgpt.com"
        if variant == "gpt"
        else "https://api.moonshot.cn"
    )
    if ready.get("upstream_origin") != expected_origin:
        _fail("model broker upstream origin is not the pinned release endpoint")
    expected_dummy = _sha256_bytes(b"answer-blind-public-dummy-token")
    if ready.get("public_dummy_key_sha256") != expected_dummy:
        _fail("model broker ready receipt does not bind the public dummy credential")
    broker_uid = ready.get("broker_uid")
    if not isinstance(broker_uid, int) or isinstance(broker_uid, bool) or broker_uid == 0:
        _fail("model broker must run under a dedicated non-root UID")
    broker_binary_sha = _require_sha256(
        ready.get("broker_binary_sha256"), field="model broker broker_binary_sha256"
    )
    runtime_files = runtime.get("files") if isinstance(runtime, Mapping) else None
    if not isinstance(runtime_files, Mapping) or broker_binary_sha not in set(
        runtime_files.values()
    ):
        _fail("model broker binary is absent from the sealed runtime inventory")
    _require_nonempty_string(ready.get("started_at"), field="model broker started_at")

    ready_sha = _sha256_bytes(ready_payload)
    if (
        transcript.get("schema_version") != SCHEMA_VERSION
        or transcript.get("protocol") != PROTOCOL
        or transcript.get("phase") != "model_broker_transcript"
        or transcript.get("variant") != variant
        or transcript.get("run_id") != run_id
        or transcript.get("request_profile") != request_profile
        or transcript.get("ready_receipt_sha256") != ready_sha
        or transcript.get("broker_stopped") is not True
    ):
        _fail("model broker transcript disagrees with the stopped sealed run")
    request_count = transcript.get("request_count")
    if (
        not isinstance(request_count, int)
        or isinstance(request_count, bool)
        or request_count < minimum_requests
        or (exact_requests is not None and request_count != exact_requests)
    ):
        _fail(f"{label} transcript has too few brokered requests")
    _require_sha256(
        transcript.get("request_response_chain_sha256"),
        field="model broker request_response_chain_sha256",
    )
    _require_nonempty_string(
        transcript.get("started_at"), field="model broker transcript started_at"
    )
    _require_nonempty_string(
        transcript.get("stopped_at"), field="model broker transcript stopped_at"
    )
    return ready, ready_sha, transcript, _sha256_bytes(transcript_payload)


def _load_model_broker_binding(
    *, project: Path, seal: Mapping[str, Any]
) -> tuple[dict[str, Any], str, dict[str, Any], str]:
    aggregate_spec = seal.get("structured_solver_receipt")
    solver = seal.get("solver")
    if not isinstance(aggregate_spec, Mapping) or not isinstance(solver, Mapping):
        _fail("controller seal solver/invocation identity is missing")
    _aggregate_path, aggregate, _aggregate_payload = _load_bound_external_receipt(
        project=project, spec=aggregate_spec, label="structured solver receipt"
    )
    scope = seal.get("freeze_scope")
    scope_ids = scope.get("ids") if isinstance(scope, Mapping) else None
    minimum_requests = 3 * len(scope_ids) if isinstance(scope_ids, list) else 1
    return _load_and_validate_model_broker_binding(
        project=project, binding=seal.get("model_broker"),
        variant=aggregate.get("variant"), run_id=solver.get("run_id"),
        model_id=solver.get("model_id"), runtime=seal.get("runtime_inventory"),
        minimum_requests=minimum_requests, request_profile="agent_harness_v1",
        label="finalize Review model_broker",
    )


def _validate_landlock_attestation(
    *,
    landlock: object,
    probes: object,
    project: Path,
    seal: Mapping[str, Any],
    verifier_readonly: bool,
    controller_path: Path,
    review_input_root: Path | None = None,
    allow_model_broker: bool = False,
) -> None:
    if not isinstance(landlock, Mapping):
        _fail("invocation Landlock attestation must be an object")
    _strict_fields(landlock, _LANDLOCK_FIELDS, label="invocation Landlock")
    if (
        not isinstance(landlock.get("abi"), int)
        or isinstance(landlock.get("abi"), bool)
        or landlock["abi"] < 4
        or landlock.get("handled_access_fs") != _LANDLOCK_ABI4_RIGHTS
        or landlock.get("deny_by_default") is not True
        or landlock.get("no_new_privs") is not True
        or landlock.get("enforced") is not True
        or landlock.get("handled_access_net") != ["bind_tcp", "connect_tcp"]
        or landlock.get("allowed_bind_tcp_ports") != []
        or landlock.get("network_deny_by_default") is not True
    ):
        _fail("invocation lacks the exact enforced ABI-4 Landlock policy")

    readonly = _absolute_path_list(
        landlock.get("read_only_paths"), label="invocation Landlock.read_only_paths"
    )
    writable = _absolute_path_list(
        landlock.get("read_write_paths"), label="invocation Landlock.read_write_paths"
    )
    dependency = seal.get("dependency_inventory")
    runtime = seal.get("runtime_inventory")
    assert isinstance(dependency, Mapping) and isinstance(runtime, Mapping)
    dependency_root = Path(str(dependency.get("root"))).resolve()
    runtime_root = Path(str(runtime.get("root"))).resolve()
    authorization, _authorization_sha = _load_launch_authorization(
        project=project, seal=seal
    )
    expected_ports = (
        [authorization.get("allowed_model_broker_tcp_port")]
        if allow_model_broker
        else []
    )
    if landlock.get("allowed_connect_tcp_ports") != expected_ports:
        _fail("Landlock TCP authority differs from the pre-run broker allowlist")
    system_readonly = _absolute_path_list(
        authorization.get("system_read_only_paths"), label="system_read_only_paths"
    )
    confined_source_root = review_input_root or project
    expected_readonly = [
        *system_readonly, runtime_root, dependency_root, confined_source_root
    ]
    # The launcher preserves this authority order. Exact equality also rejects
    # accidental broad additions such as /usr, /lib, /etc or an answer tree.
    if readonly != expected_readonly:
        _fail("Landlock read-only authority differs from the pre-run exact allowlist")

    external_field = (
        "reviewer_external_read_write_paths"
        if review_input_root is not None
        else "verifier_external_read_write_paths"
        if verifier_readonly
        else "solver_external_read_write_paths"
    )
    external_writable = _absolute_path_list(
        authorization.get(external_field), label=external_field
    )
    for external in external_writable:
        try:
            external.relative_to(project)
        except ValueError:
            pass
        else:
            _fail(f"{external_field} may not authorize a path inside the snapshot")
    mutable_in_project = sorted(
        {
            (project / relative).resolve()
            for relative in _SOLVER_MUTABLE_PATHS
        },
        key=str,
    )
    expected_writable = set(external_writable)
    if not verifier_readonly:
        expected_writable.update(mutable_in_project)
    if set(writable) != expected_writable:
        _fail("Landlock writable authority differs from the pre-run exact allowlist")
    protected = [
        project / SEED_MANIFEST,
        *(project / relative for relative in _CONTROLLER_GENERATED_FILES),
        runtime_root,
        dependency_root,
        *( [review_input_root] if review_input_root is not None else [] ),
        controller_path,
    ]
    for write_root in writable:
        if any(
            protected_path == write_root or protected_path.is_relative_to(write_root)
            for protected_path in protected
        ):
            _fail("Landlock writable path covers controller-protected material")
        if verifier_readonly:
            try:
                write_root.relative_to(project)
            except ValueError:
                pass
            else:
                _fail("Lean verifier Landlock policy may not write anywhere in the snapshot")

    if not isinstance(probes, Mapping) or not probes:
        _fail("invocation isolation_probes must be a nonempty object")
    seen_probe_paths: set[Path] = set()
    for raw_path, probe in probes.items():
        if not isinstance(raw_path, str) or not Path(raw_path).is_absolute():
            _fail("invocation isolation probe path must be absolute")
        probe_path = Path(raw_path).resolve()
        seen_probe_paths.add(probe_path)
        if not isinstance(probe, Mapping):
            _fail("invocation isolation probe must be an object")
        _strict_fields(probe, _ISOLATION_PROBE_FIELDS, label="isolation probe")
        if probe.get("open_read_denied") is not True or probe.get("errno") not in {1, 13}:
            _fail("invocation isolation probe did not fail closed with EACCES/EPERM")
    authorized_probes = set(_absolute_path_list(
        authorization.get("required_denied_probe_paths"),
        label="required_denied_probe_paths",
    ))
    dynamic_probes = seen_probe_paths - authorized_probes
    if not authorized_probes.issubset(seen_probe_paths) or len(dynamic_probes) != 1:
        _fail("invocation isolation probes differ from pre-run exact probe authority")
    dynamic_controller_proc = next(iter(dynamic_probes))
    if (
        not re.fullmatch(r"/proc/[1-9][0-9]*/environ", str(dynamic_controller_proc))
        or dynamic_controller_proc == Path("/proc/1/environ")
    ):
        _fail("invocation has an invalid dynamic controller-process probe")
    required_probes = {
        Path("/root"), Path("/var/tmp"), Path("/dev/shm"),
        Path("/proc/1/environ"),
    }
    if not required_probes.issubset(seen_probe_paths) or not any(
        path == Path("/tmp") or path.is_relative_to(Path("/tmp"))
        for path in seen_probe_paths
    ):
        _fail("invocation probes omit root/shared-temp/proc-1 isolation")
    # The one authorized dynamic probe above is the controller process env.
    if not any(
        controller_path == probe or controller_path.is_relative_to(probe)
        for probe in seen_probe_paths
    ):
        _fail("invocation isolation probes do not cover the controller receipt root")


def _validate_dedicated_uid_quiescence(value: object, *, expected_uid: int) -> None:
    if not isinstance(value, Mapping):
        _fail("dedicated_uid_quiescence must be an object")
    _strict_fields(value, _UID_QUIESCENCE_FIELDS, label="dedicated_uid_quiescence")
    if value.get("mechanism") != "dedicated_uid_prlimit_pidfd_v1":
        _fail("dedicated UID quiescence mechanism is unsupported")
    if value.get("uid") != expected_uid:
        _fail("dedicated UID quiescence attests the wrong UID")
    rlimit = value.get("rlimit_nproc")
    if (
        not isinstance(rlimit, int) or isinstance(rlimit, bool)
        or not 1 <= rlimit <= 256
    ):
        _fail("dedicated UID quiescence rlimit_nproc is invalid")
    if (
        value.get("quiescent_before") is not True
        or value.get("before_pids") != []
        or value.get("prlimit_zero_applied") is not True
        or value.get("quiescent_after") is not True
        or value.get("after_pids") != []
    ):
        _fail("dedicated UID was not proven quiescent before and after invocation")
    if not isinstance(value.get("pidfd_kill_used"), bool):
        _fail("dedicated UID quiescence pidfd_kill_used must be boolean")
    kill_rounds = value.get("kill_rounds")
    if not isinstance(kill_rounds, int) or isinstance(kill_rounds, bool) or kill_rounds < 0:
        _fail("dedicated UID quiescence kill_rounds is invalid")
    quiet = value.get("quiet_period_ms")
    if not isinstance(quiet, int) or isinstance(quiet, bool) or quiet < 500:
        _fail("dedicated UID quiescence quiet period is too short")


def _validate_solver_invocation_receipt(
    receipt: Mapping[str, Any], *, seal: Mapping[str, Any], project: Path,
    expected_invocation: int,
    expected_previous_receipt_sha256: str | None,
    expected_previous_chain_sha256: str | None,
) -> tuple[str, str, str]:
    _strict_fields(
        receipt, _INVOCATION_RECEIPT_FIELDS, label="solver invocation receipt"
    )
    if (
        receipt.get("schema_version") != 1
        or receipt.get("protocol") != PROTOCOL
        or receipt.get("phase") != "solver_invocation"
        or receipt.get("receipt_type") != "trusted-controller-one-iteration"
    ):
        _fail("solver invocation receipt has unsupported metadata")
    if receipt.get("exit_code") != 0:
        _fail("solver invocation did not complete successfully")
    if receipt.get("solver_stopped") is not True or receipt.get("descendants_stopped") is not True:
        _fail("solver invocation receipt does not attest a stopped process tree")
    if receipt.get("protected_unchanged") is not True:
        _fail("solver invocation receipt reports protected-file drift")
    previous = receipt.get("previous_receipt_sha256")
    if previous != expected_previous_receipt_sha256:
        _fail("solver invocation receipt hash chain has a stale previous receipt")
    without_chain = dict(receipt)
    claimed_chain = _require_sha256(
        without_chain.pop("chain_sha256"), field="solver invocation chain_sha256"
    )
    core_sha = _sha256_bytes(_json_bytes(without_chain))
    expected_chain = _sha256_bytes(_json_bytes({
        "previous_chain_sha256": expected_previous_chain_sha256,
        "receipt_core_sha256": core_sha,
    }))
    if claimed_chain != expected_chain:
        _fail("solver invocation receipt chain_sha256 is invalid")
    solver = seal.get("solver")
    isolation = seal.get("isolation")
    if not isinstance(solver, dict) or set(solver) != _SOLVER_FIELDS:
        _fail("controller seal solver identity is invalid")
    if not isinstance(isolation, dict) or set(isolation) != _ISOLATION_FIELDS:
        _fail("controller seal isolation metadata is invalid")
    for field in _SOLVER_FIELDS:
        if receipt.get(field) != solver.get(field):
            _fail(f"solver invocation receipt disagrees with controller seal: {field}")
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3[1m]"),
    }.get(receipt.get("variant"))
    if expected_identity != (solver.get("model_family"), solver.get("model_id")):
        _fail("solver invocation receipt has an unapproved variant/model identity")
    if receipt.get("isolation") != isolation:
        _fail("solver invocation receipt isolation disagrees with controller seal")
    if isolation != {
        "filesystem_answer_blind": True,
        "network_answer_blind": False,
    }:
        _fail("controller seal isolation must conservatively record filesystem-only blindness")
    dependency = seal.get("dependency_inventory")
    assert isinstance(dependency, Mapping)
    if receipt.get("dependency_inventory_sha256") != dependency.get("files_sha256"):
        _fail("solver invocation receipt dependency inventory is stale")
    runtime_inventory = seal.get("runtime_inventory")
    if not isinstance(runtime_inventory, Mapping) or (
        receipt.get("runtime_inventory_sha256")
        != runtime_inventory.get("files_sha256")
    ):
        _fail("solver invocation receipt runtime inventory is stale")
    _authorization, authorization_sha = _load_launch_authorization(
        project=project, seal=seal
    )
    if receipt.get("launch_authorization_sha256") != authorization_sha:
        _fail("solver invocation receipt launch authorization is stale")
    ready, broker_receipt_sha, _transcript, transcript_sha = (
        _load_and_validate_model_broker_binding(
            project=project, binding=receipt.get("model_broker"),
            variant=receipt.get("variant"), run_id=receipt.get("run_id"),
            model_id=receipt.get("model_id"), runtime=runtime_inventory,
            minimum_requests=1,
            request_profile="agent_harness_v1",
            label=f"solver invocation {expected_invocation} model_broker",
        )
    )
    parsed_ready = urlparse(str(ready.get("listen_url") or ""))
    if parsed_ready.port != _authorization.get("allowed_model_broker_tcp_port"):
        _fail("solver invocation broker port differs from launch authorization")
    before = receipt.get("protected_before")
    after = receipt.get("protected_after")
    if not isinstance(before, dict) or before != after:
        _fail("solver invocation protected inventories differ")
    _strict_fields(before, _PROTECTED_INVENTORY_FIELDS, label="protected inventory")
    protected_files = _validated_hash_map(
        before.get("files"), label="solver invocation protected files"
    )
    if before.get("aggregate_sha256") != _hash_index(protected_files):
        _fail("solver invocation protected inventory digest is invalid")
    if not isinstance(receipt.get("command_argv"), list) or not receipt["command_argv"]:
        _fail("solver invocation command_argv must be a non-empty list")
    if any(not isinstance(item, str) or not item for item in receipt["command_argv"]):
        _fail("solver invocation command_argv contains an invalid element")
    for field in ("started_at", "ended_at", "user"):
        _require_nonempty_string(receipt.get(field), field=f"solver invocation {field}")
    if receipt.get("invocation") != expected_invocation:
        _fail("solver invocation receipt sequence number is invalid")
    for field in ("uid", "gid"):
        value = receipt.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value == 0:
            _fail(f"solver invocation {field} must identify a non-root account")
    _validate_dedicated_uid_quiescence(
        receipt.get("dedicated_uid_quiescence"), expected_uid=receipt["uid"]
    )
    log = receipt.get("stdout_log")
    if not isinstance(log, dict):
        _fail("solver invocation stdout_log must be an object")
    _strict_fields(log, _STDOUT_LOG_FIELDS, label="solver invocation stdout_log")
    _require_sha256(log.get("sha256"), field="solver invocation stdout_log.sha256")
    if not isinstance(log.get("size"), int) or isinstance(log.get("size"), bool) or log["size"] < 0:
        _fail("solver invocation stdout_log.size is invalid")
    raw_log_path = log.get("path")
    if not isinstance(raw_log_path, str) or not Path(raw_log_path).is_absolute():
        _fail("solver invocation stdout_log.path must be absolute")
    log_path = _outside_project(Path(raw_log_path), project, label="solver stdout log")
    _validate_landlock_attestation(
        landlock=receipt.get("landlock"), probes=receipt.get("isolation_probes"),
        project=project, seal=seal, verifier_readonly=False,
        controller_path=log_path.parent,
        allow_model_broker=True,
    )
    _require_controller_owned_readonly(log_path, label="solver stdout log")
    log_payload = _read_plain_bytes(log_path, label="solver stdout log")
    if len(log_payload) != log["size"] or _sha256_bytes(log_payload) != log["sha256"]:
        _fail("solver invocation stdout log hash/size drift")
    return claimed_chain, broker_receipt_sha, transcript_sha


def _validate_solver_invocation_aggregate(
    aggregate: Mapping[str, Any], *, seal: Mapping[str, Any], project: Path
) -> None:
    _strict_fields(
        aggregate, _INVOCATION_AGGREGATE_FIELDS,
        label="solver invocation aggregate receipt",
    )
    if (
        aggregate.get("schema_version") != 1
        or aggregate.get("protocol") != PROTOCOL
        or aggregate.get("phase") != "solver_invocation_aggregate"
    ):
        _fail("solver invocation aggregate has unsupported metadata")
    solver = seal.get("solver")
    assert isinstance(solver, Mapping)
    for field in _SOLVER_FIELDS:
        if aggregate.get(field) != solver.get(field):
            _fail(f"solver invocation aggregate disagrees with seal: {field}")
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3[1m]"),
    }.get(aggregate.get("variant"))
    if expected_identity != (solver.get("model_family"), solver.get("model_id")):
        _fail("solver invocation aggregate has an unapproved model identity")
    for field in (
        "all_exit_zero", "all_protected_unchanged", "all_stopped",
        "all_uid_quiescent",
    ):
        if aggregate.get(field) is not True:
            _fail(f"solver invocation aggregate requires {field}=true")
    dependency = seal.get("dependency_inventory")
    runtime = seal.get("runtime_inventory")
    if not isinstance(dependency, Mapping) or not isinstance(runtime, Mapping):
        _fail("controller inventories are missing")
    if aggregate.get("dependency_inventory_sha256") != dependency.get("files_sha256"):
        _fail("solver invocation aggregate dependency inventory is stale")
    if aggregate.get("runtime_inventory_sha256") != runtime.get("files_sha256"):
        _fail("solver invocation aggregate runtime inventory is stale")
    _authorization, authorization_sha = _load_launch_authorization(
        project=project, seal=seal
    )
    if aggregate.get("launch_authorization_sha256") != authorization_sha:
        _fail("solver invocation aggregate launch authorization is stale")
    if (
        aggregate.get("filesystem_answer_blind") is not True
        or aggregate.get("network_answer_blind") is not False
    ):
        _fail("solver invocation aggregate isolation is invalid")
    uid = aggregate.get("uid")
    if not isinstance(uid, int) or isinstance(uid, bool) or uid == 0:
        _fail("solver invocation aggregate UID must be non-root")
    specs = aggregate.get("receipts")
    broker_evidence = aggregate.get("model_brokers")
    count = aggregate.get("invocation_count")
    if (
        not isinstance(specs, list) or not specs
        or not isinstance(broker_evidence, list)
        or len(broker_evidence) != len(specs)
        or not isinstance(count, int) or isinstance(count, bool)
        or count != len(specs)
    ):
        _fail("solver invocation aggregate receipt count is invalid")
    previous_receipt_sha: str | None = None
    previous_chain: str | None = None
    seen_broker_pairs: set[tuple[str, str]] = set()
    for index, spec in enumerate(specs, start=1):
        _path, receipt, payload = _load_bound_external_receipt(
            project=project, spec=spec, label=f"solver invocation receipt {index}"
        )
        if receipt.get("uid") != uid:
            _fail("solver invocation aggregate mixes solver UIDs")
        previous_chain, ready_sha, transcript_sha = _validate_solver_invocation_receipt(
            receipt, seal=seal, project=project,
            expected_invocation=index,
            expected_previous_receipt_sha256=previous_receipt_sha,
            expected_previous_chain_sha256=previous_chain,
        )
        evidence = broker_evidence[index - 1]
        if not isinstance(evidence, Mapping):
            _fail("solver invocation aggregate broker evidence must be an object")
        _strict_fields(
            evidence, _INVOCATION_BROKER_EVIDENCE_FIELDS,
            label="solver invocation aggregate broker evidence",
        )
        if (
            evidence.get("invocation") != index
            or evidence.get("ready_receipt_sha256") != ready_sha
            or evidence.get("transcript_sha256") != transcript_sha
        ):
            _fail("solver invocation aggregate broker evidence is stale/out of order")
        pair = (ready_sha, transcript_sha)
        if pair in seen_broker_pairs:
            _fail("solver invocations reuse model-broker lifecycle evidence")
        seen_broker_pairs.add(pair)
        previous_receipt_sha = _sha256_bytes(payload)
    if aggregate.get("chain_sha256") != previous_chain:
        _fail("solver invocation aggregate final chain SHA-256 is stale")


def _strict_json_object(payload: bytes, *, label: str) -> dict[str, Any]:
    """Parse one bounded JSON object while rejecting duplicate keys/NaN."""

    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                _fail(f"{label} repeats JSON key {key!r}")
            result[key] = item
        return result

    try:
        value = json.loads(
            payload.decode("utf-8", errors="strict"),
            object_pairs_hook=pairs_hook,
            parse_constant=lambda token: _fail(f"{label} contains {token}"),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _fail(f"{label} is not strict UTF-8 JSON: {exc}")
    if not isinstance(value, dict):
        _fail(f"{label} must contain one JSON object")
    return value


def _structured_problem_projection(row: Mapping[str, Any]) -> dict[str, Any]:
    fields = (
        "schema_version", "protocol", "evaluation_mode", "official_answer_seen",
        "id", "current_question", "shared_context", "previous_parts", "images",
        "problem_assets", "requested_outputs", "reporting_policy",
        "measurement_policy", "candidate_domain_policy",
    )
    projection = {field: row.get(field) for field in fields}
    projection["phase"] = "structured_solve"
    projection["blind_record_sha256"] = _sha256_bytes(_json_bytes(row))
    if (
        projection.get("schema_version") != SCHEMA_VERSION
        or projection.get("protocol") != PROTOCOL
        or projection.get("evaluation_mode") != "answer_blind"
        or projection.get("official_answer_seen") is not False
        or not isinstance(projection.get("requested_outputs"), list)
        or not projection["requested_outputs"]
    ):
        _fail("structured solver problem projection is not answer-blind")
    return projection


def _structured_result_spec_schema(output: Mapping[str, Any]) -> dict[str, Any]:
    kind = str(output.get("kind") or "")
    text = {"type": "string", "minLength": 1}
    underdetermined = {
        "type": "object",
        "properties": {
            "kind": {"const": kind}, "status": {"const": "underdetermined"},
            "reason": text,
            "remaining_constraints": {"type": "array", "minItems": 1, "items": text},
        },
        "required": ["kind", "status", "reason", "remaining_constraints"],
        "additionalProperties": False,
    }
    numeric_text = {
        "type": "string",
        "pattern": r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?(?:/[1-9]\d*)?$",
    }
    common = {"kind": {"const": kind}, "status": {"const": "derived"}}
    if kind == "numeric":
        derived = {
            "type": "object", "properties": {
                **common, "raw_expression": text, "raw_value": numeric_text,
                "certified_interval": {
                    "type": "object",
                    "properties": {"lower": numeric_text, "upper": numeric_text},
                    "required": ["lower", "upper"], "additionalProperties": False,
                },
                "reported_value": numeric_text, "reporting_quantum": numeric_text,
                "tie_rule": text,
            },
            "required": [
                "kind", "status", "raw_expression", "raw_value",
                "certified_interval", "reported_value", "reporting_quantum", "tie_rule",
            ],
            "additionalProperties": False,
        }
    elif kind == "integer":
        derived = {
            "type": "object", "properties": {
                **common, "value": {"type": "string", "pattern": r"^-?\d+$"},
                "proposition": text,
                "constraints": {"type": "array", "minItems": 1, "items": text},
            },
            "required": ["kind", "status", "value", "proposition", "constraints"],
            "additionalProperties": False,
        }
    elif kind in {"formula", "classification"}:
        derived = {
            "type": "object", "properties": {
                **common, "normalized_result": text, "proposition": text,
                "constraints": {"type": "array", "minItems": 1, "items": text},
            },
            "required": ["kind", "status", "normalized_result", "proposition", "constraints"],
            "additionalProperties": False,
        }
    elif kind == "finite_set":
        derived = {
            "type": "object", "properties": {
                **common,
                "normalized_members": {"type": "array", "minItems": 1, "items": text},
                "proposition": text,
                "constraints": {"type": "array", "minItems": 1, "items": text},
            },
            "required": ["kind", "status", "normalized_members", "proposition", "constraints"],
            "additionalProperties": False,
        }
    else:
        _fail(f"structured requested output has unsupported kind {kind!r}")
    return {"anyOf": [derived, underdetermined]}


def _structured_submission_schema(
    projection: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
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
                str(output["id"]): _structured_result_spec_schema(output)
                for output in requested if isinstance(output, Mapping)
            },
            "required": [str(output["id"]) for output in requested if isinstance(output, Mapping)],
            "additionalProperties": False,
        }
        reported_value: dict[str, Any] = {
            "type": "object",
            "properties": {
                str(output["id"]): {
                    "type": "object", "properties": {
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
                "type": "object", "properties": {
                    "expression": {"type": "string", "minLength": 1},
                    "lean_expression": {"type": "string", "minLength": 1},
                    "derivation_spec": {"type": ["string", "null"]},
                    "certified_interval": {"anyOf": [
                        {"type": "null"},
                        {
                            "type": "object",
                            "properties": {
                                "lower": {"type": "string"}, "upper": {"type": "string"},
                            },
                            "required": ["lower", "upper"], "additionalProperties": False,
                        },
                    ]},
                    "value": raw_value, "unit": {"type": ["string", "null"]},
                },
                "required": [
                    "expression", "lean_expression", "derivation_spec",
                    "certified_interval", "value", "unit",
                ],
                "additionalProperties": False,
            },
            "reported_result": {
                "type": "object", "properties": {
                    "value": reported_value, "text": {"type": ["string", "null"]},
                    "lean_expression": {"type": "string", "minLength": 1},
                    "unit": {"type": ["string", "null"]},
                },
                "required": ["value", "text", "lean_expression", "unit"],
                "additionalProperties": False,
            },
            "candidate_domain_derivation": {
                "type": "object", "properties": {
                    "kind": {"type": "string", "minLength": 1},
                    "evidence": {
                        "type": "array", "minItems": 1,
                        "items": {"type": "string", "minLength": 1},
                    },
                    "depends_on": {"type": "array", "items": {"type": "string"}},
                },
                "required": ["kind", "evidence", "depends_on"],
                "additionalProperties": False,
            },
            "lean_declarations": {
                "type": "array", "minItems": 2, "maxItems": 2,
                "items": {"type": "string", "pattern": _QUALIFIED_DECLARATION_RE.pattern},
            },
            "lean_source": {"type": "string", "maxLength": 8 * 1024 * 1024},
            "blueprint": {"type": "string", "maxLength": 8 * 1024 * 1024},
        },
        "required": sorted(_STRUCTURED_SUBMISSION_FIELDS),
        "additionalProperties": False,
    }


def _structured_prompt(
    *, projection: Mapping[str, Any], diagnostics: Sequence[Mapping[str, Any]],
) -> str:
    return (
        "Produce a formalization from only the supplied problem projection. "
        "Do not retrieve or infer any official answer. Do not emit markdown. "
        "Return exactly the JSON submission schema. The Lean source must use only "
        "sealed imports and may not use metaprogramming, IO, unsafe declarations, "
        "axioms, sorry/admit, native_decide, run_cmd, or generated imports. "
        "Return only semantic result fields. Provenance, policy, and result-contract "
        "hashes are constructed by the trusted controller.\n"
        "problem_projection="
        + json.dumps(
            projection, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        )
        + "\nprior_trusted_diagnostics="
        + json.dumps(
            list(diagnostics), ensure_ascii=False, sort_keys=True,
            separators=(",", ":"),
        )
    )


def _structured_image_parts(
    *, project: Path, row: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    gpt: list[dict[str, Any]] = []
    kimi: list[dict[str, Any]] = []
    assets = row.get("problem_assets")
    if not isinstance(assets, list):
        _fail("structured solver problem_assets must be a list")
    for asset in assets:
        if not isinstance(asset, Mapping) or asset.get("kind") != "problem_page":
            continue
        raw = asset.get("path")
        if not isinstance(raw, str) or Path(raw).name != raw:
            _fail("structured solver image must be a bundle basename")
        path = _resolve_project_locator(
            project, f"icho_2026_source/image/{raw}", label="structured problem image"
        )
        payload = _read_plain_bytes(path, label="structured problem image")
        if _sha256_bytes(payload) != asset.get("sha256"):
            _fail(f"structured problem image hash drift: {raw}")
        mime = {
            ".png": "image/png", ".jpg": "image/jpeg",
            ".jpeg": "image/jpeg", ".webp": "image/webp",
        }.get(path.suffix.lower())
        if mime is None:
            _fail(f"unsupported structured problem image type: {raw}")
        encoded = base64.b64encode(payload).decode("ascii")
        gpt.append({"type": "input_image", "image_url": f"data:{mime};base64,{encoded}"})
        kimi.append({
            "type": "image",
            "source": {"type": "base64", "media_type": mime, "data": encoded},
        })
    return gpt, kimi


def _structured_provider_request(
    *, variant: str, model_id: str, projection: Mapping[str, Any],
    gpt_images: Sequence[Mapping[str, Any]],
    kimi_images: Sequence[Mapping[str, Any]],
    diagnostics: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    prompt = _structured_prompt(projection=projection, diagnostics=diagnostics)
    if variant == "gpt":
        return {
            "model": model_id,
            "store": False,
            "tools": [],
            "tool_choice": "none",
            "stream": True,
            "reasoning": {"effort": "max", "summary": "auto"},
            "input": [{
                "role": "user",
                "content": [{"type": "input_text", "text": prompt}, *gpt_images],
            }],
            "text": {"format": {
                "type": "json_schema", "name": "answer_blind_submission",
                "strict": True, "schema": _structured_submission_schema(projection),
            }},
        }
    if variant == "kimi-k3":
        return {
            "model": model_id,
            "tools": [],
            "max_tokens": 131072,
            "messages": [{
                "role": "user",
                "content": [{"type": "text", "text": prompt}, *kimi_images],
            }],
        }
    _fail(f"unsupported structured solver variant: {variant}")


def _structured_raw_submission_from_response(
    response: Mapping[str, Any], *, variant: str,
) -> dict[str, Any]:
    if variant == "gpt":
        output = response.get("output")
        if not isinstance(output, list):
            _fail("structured GPT response output must be a list")
        messages: list[Mapping[str, Any]] = []
        for item in output:
            if not isinstance(item, Mapping):
                _fail("structured GPT response output items must be objects")
            item_type = item.get("type")
            if item_type == "message":
                if item.get("role") not in (None, "assistant"):
                    _fail("structured GPT response message must be from assistant")
                messages.append(item)
            elif isinstance(item_type, str) and any(
                token in item_type.lower()
                for token in ("tool", "function", "refusal")
            ):
                _fail("structured GPT response contains prohibited output")
        if len(messages) != 1:
            _fail("structured GPT response must contain one assistant message")
        content = messages[0].get("content")
        if not isinstance(content, list) or not content:
            _fail("structured GPT assistant message has no output text")
        texts: list[str] = []
        for block in content:
            if (
                not isinstance(block, Mapping)
                or block.get("type") != "output_text"
                or not isinstance(block.get("text"), str)
            ):
                _fail("structured GPT assistant message contains non-text content")
            texts.append(block["text"])
        joined = "".join(texts)
    else:
        content = response.get("content")
        if not isinstance(content, list):
            _fail("structured provider response content must be a list")
        texts = [
            block["text"]
            for block in content
            if isinstance(block, Mapping)
            and block.get("type") == "text"
            and isinstance(block.get("text"), str)
        ]
        if len(texts) != 1:
            _fail("structured provider response must contain exactly one JSON text block")
        joined = texts[0]
    return _strict_json_object(
        joined.encode("utf-8"), label="structured provider submission text"
    )


def _bounded_structured_gpt_response_structure(document: object) -> dict[str, Any]:
    """Mirror the producer's bounded, text-free envelope diagnostic."""

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


def _structured_submission_from_response(
    response: Mapping[str, Any], *, variant: str,
) -> dict[str, Any]:
    submission = _structured_raw_submission_from_response(response, variant=variant)
    _strict_fields(
        submission, _STRUCTURED_SUBMISSION_FIELDS,
        label="structured provider submission",
    )
    for field in ("raw_result", "reported_result", "candidate_domain_derivation"):
        if not isinstance(submission.get(field), Mapping):
            _fail(f"structured provider submission.{field} must be an object")
    declarations = submission.get("lean_declarations")
    if (
        not isinstance(declarations, list) or len(declarations) != 2
        or len(set(declarations)) != 2
        or any(
            not isinstance(item, str)
            or _QUALIFIED_DECLARATION_RE.fullmatch(item) is None
            for item in declarations
        )
    ):
        _fail("structured provider lean_declarations must be two unique qualified names")
    for field in ("lean_source", "blueprint"):
        value = submission.get(field)
        if not isinstance(value, str) or not value.strip():
            _fail(f"structured provider submission.{field} must be nonempty text")
        if len(value.encode("utf-8")) > 8 * 1024 * 1024 or "\0" in value:
            _fail(f"structured provider submission.{field} exceeds safety bounds")
    return submission


def _construct_structured_candidate(
    submission: Mapping[str, Any], *, target_id: str, blind_hash: str,
    source_entry: Mapping[str, Any],
) -> dict[str, Any]:
    """Deterministically inject all controller-owned candidate bindings."""
    _strict_fields(
        submission, _STRUCTURED_SUBMISSION_FIELDS,
        label="structured provider submission",
    )
    declarations = submission.get("lean_declarations")
    if (
        not isinstance(declarations, list) or len(declarations) != 2
        or len(set(declarations)) != 2
        or any(
            not isinstance(item, str)
            or _QUALIFIED_DECLARATION_RE.fullmatch(item) is None
            for item in declarations
        )
    ):
        _fail("structured lean_declarations are invalid")
    raw = submission.get("raw_result")
    reported = submission.get("reported_result")
    derivation = submission.get("candidate_domain_derivation")
    if not all(isinstance(item, Mapping) for item in (raw, reported, derivation)):
        _fail("structured semantic result objects are missing")
    assert isinstance(raw, Mapping) and isinstance(reported, Mapping)
    assert isinstance(derivation, Mapping)
    if not derivation:
        _fail("structured candidate-domain derivation must be nonempty")
    reporting_policy = source_entry.get("reporting_policy")
    measurement_policy = source_entry.get("measurement_policy")
    domain_policy = source_entry.get("candidate_domain_policy")
    requested = source_entry.get("requested_outputs")
    if (
        not all(isinstance(item, Mapping) and item for item in (
            reporting_policy, measurement_policy, domain_policy,
        ))
        or not isinstance(requested, list) or not requested
    ):
        _fail("structured source projection lacks controller-owned policies")
    if len(requested) > 1:
        result_kind = "symbolic"
    elif reported.get("value") is None:
        result_kind = "underdetermined"
    else:
        requested_kind = requested[0].get("kind") if isinstance(requested[0], Mapping) else None
        result_kind = (
            "numeric" if requested_kind == "numeric" else
            "classification" if requested_kind == "classification" else
            "symbolic"
        )
    raw_copy = {key: value for key, value in raw.items() if value is not None}
    reported_copy = {key: value for key, value in reported.items() if value is not None}
    assert isinstance(reporting_policy, Mapping)
    assert isinstance(measurement_policy, Mapping)
    assert isinstance(domain_policy, Mapping)
    reported_copy["precision"] = reporting_policy.get("final_precision")
    reported_copy["rounding_rule"] = reporting_policy.get("tie_rule")
    candidate: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
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
    if result_kind == "numeric":
        _validate_bounded_numeric_text(
            raw_copy.get("value"),
            field=f"candidate {target_id}.raw_result.value",
            allow_rational=True,
        )
        _validate_bounded_numeric_text(
            reported_copy.get("value"),
            field=f"candidate {target_id}.reported_result.value",
            allow_rational=False,
        )
        interval = raw_copy.get("certified_interval")
        if not isinstance(interval, Mapping) or set(interval) != {"lower", "upper"}:
            _fail(
                f"candidate {target_id}.raw_result.certified_interval must contain "
                "exactly lower and upper"
            )
        lower = _bounded_fraction(
            interval.get("lower"),
            field=f"candidate {target_id}.raw_result.certified_interval.lower",
        )
        upper = _bounded_fraction(
            interval.get("upper"),
            field=f"candidate {target_id}.raw_result.certified_interval.upper",
        )
        if lower >= upper:
            _fail(
                f"candidate {target_id}.raw_result.certified_interval must be "
                "a non-degenerate independently proved enclosure"
            )
    expected = (
        expected_numeric_result_types(candidate)
        if result_kind == "numeric"
        else expected_nonnumeric_result_types(candidate)
    )
    if expected is None:
        _fail("structured semantic result cannot produce Lean result contracts")
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


def _compose_structured_blueprint(
    *, generated: object, prepared_payload: bytes | None,
    target_relative: str, source_report_relative: str,
) -> bytes:
    if not isinstance(generated, str) or not generated.strip():
        _fail("structured blueprint must be nonempty text")
    generated_payload = generated.encode("utf-8")
    if (
        len(generated_payload) > _MAX_ARTIFACT_BYTES or b"\0" in generated_payload
        or re.search(r"(?i)\b(?:sorry|autoformaliz(?:e|ation))\b", generated)
    ):
        _fail("structured blueprint contains prohibited or oversized content")
    if prepared_payload is None:
        return generated_payload
    if len(prepared_payload) > _MAX_ARTIFACT_BYTES:
        _fail("prepared problem-only blueprint exceeds byte limit")
    try:
        base = prepared_payload.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        _fail("prepared blueprint is not UTF-8")
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
        or "% --- Answer-blind structured proof begin ---" in base
        or "% --- Answer-blind structured proof end ---" in base
    ):
        _fail("prepared blueprint is not the canonical problem-only source block")
    problem_only = stripped[:stripped.index(formalization)].rstrip() + "\n" + end
    combined = (
        problem_only.encode("utf-8")
        + b"\n\n% --- Answer-blind structured proof begin ---\n"
        + generated_payload.rstrip()
        + b"\n% --- Answer-blind structured proof end ---\n"
    )
    if len(combined) > _MAX_ARTIFACT_BYTES:
        _fail("composed blueprint exceeds byte limit")
    return combined


def _validate_structured_diagnostics(value: object, *, label: str) -> list[dict[str, Any]]:
    if not isinstance(value, list) or len(value) > 200:
        _fail(f"{label} must be a bounded list")
    normalized: list[dict[str, Any]] = []
    for index, item in enumerate(value):
        if not isinstance(item, Mapping):
            _fail(f"{label}[{index}] must be an object")
        missing = {"kind", "message"} - set(item)
        extra = set(item) - _STRUCTURED_DIAGNOSTIC_FIELDS
        if missing or extra:
            _fail(f"{label}[{index}] has invalid fields")
        if item.get("kind") not in _STRUCTURED_DIAGNOSTIC_KINDS:
            _fail(f"{label}[{index}] has an invalid kind")
        message = item.get("message")
        if not isinstance(message, str) or not message.strip() or len(message) > 8192:
            _fail(f"{label}[{index}] has an invalid message")
        normalized_item: dict[str, Any] = {
            "kind": item["kind"], "message": message,
        }
        for field in ("line", "column"):
            number = item.get(field)
            if number is not None:
                if not isinstance(number, int) or isinstance(number, bool) or number < 1:
                    _fail(f"{label}[{index}].{field} is invalid")
                normalized_item[field] = number
        normalized.append(normalized_item)
    return normalized


def _structured_artifact_map(
    value: object, *, project: Path, label: str,
) -> dict[str, dict[str, str]]:
    if not isinstance(value, Mapping):
        _fail(f"{label} must be an object")
    _strict_fields(value, _STRUCTURED_ARTIFACT_NAMES, label=label)
    result: dict[str, dict[str, str]] = {}
    seen_paths: set[str] = set()
    for name in sorted(_STRUCTURED_ARTIFACT_NAMES):
        item = value.get(name)
        if not isinstance(item, Mapping):
            _fail(f"{label}.{name} must be an object")
        _strict_fields(item, _STRUCTURED_ARTIFACT_FIELDS, label=f"{label}.{name}")
        path = _resolve_project_locator(
            project, item.get("path"), label=f"structured {name} artifact"
        )
        relative = path.relative_to(project).as_posix()
        if relative in seen_paths:
            _fail(f"{label} reuses an artifact path")
        seen_paths.add(relative)
        digest = _require_sha256(item.get("sha256"), field=f"{label}.{name}.sha256")
        result[name] = {"path": relative, "sha256": digest}
    return result


def _load_external_bytes_locator(
    *, project: Path, spec: object, label: str,
    max_bytes: int = _MAX_PROVIDER_RESPONSE_BYTES,
    exact_private_mode: bool = True,
) -> tuple[Path, bytes]:
    if not isinstance(spec, Mapping):
        _fail(f"{label} locator is missing")
    _strict_fields(spec, _EXTERNAL_RECEIPT_FIELDS, label=f"{label} locator")
    raw_path = spec.get("path")
    if not isinstance(raw_path, str) or not Path(raw_path).is_absolute():
        _fail(f"{label} path must be absolute")
    path = _outside_project(Path(raw_path), project, label=label)
    _require_controller_owned_readonly(path, label=label)
    mode = path.stat(follow_symlinks=False).st_mode & 0o777
    if (exact_private_mode and mode != 0o400) or (
        not exact_private_mode and mode & 0o022
    ):
        _fail(f"{label} must be controller-owned mode 0400")
    payload = _read_plain_bytes(path, label=label, max_bytes=max_bytes)
    if _sha256_bytes(payload) != _require_sha256(
        spec.get("sha256"), field=f"{label}.sha256"
    ):
        _fail(f"{label} hash is stale")
    return path, payload


def _validate_structured_failure_diagnostic(
    *, project: Path, failure: Mapping[str, Any], variant: object,
) -> None:
    locator_fields = [
        field for field in ("diagnostic", "diagnostic_stdout", "diagnostic_stderr")
        if field in failure
    ]
    if locator_fields and variant != "gpt":
        _fail("only GPT transport failures may bind a Codex diagnostic")
    for field in locator_fields:
        diagnostic_path, _diagnostic_payload = _load_external_bytes_locator(
            project=project, spec=failure.get(field),
            label=f"structured provider transport failure {field}",
        )
        if diagnostic_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
            _fail("structured provider transport failure diagnostic must be mode 0400")
    normalized_response_fields = (
        "upstream_raw_sse", "normalized_response", "response_structure",
    )
    raw_response_fields = (
        "upstream_raw_sse", "response_headers", "response_structure",
    )
    present_normalized = [
        field for field in normalized_response_fields if field in failure
    ]
    present_raw = [field for field in raw_response_fields if field in failure]
    if "normalized_response" in failure:
        if variant != "gpt" or len(present_normalized) != len(normalized_response_fields):
            _fail("GPT transport failure response evidence must be supplied together")
        _load_external_bytes_locator(
            project=project, spec=failure.get("upstream_raw_sse"),
            label="structured provider transport failure upstream SSE",
        )
        _normalized_path, normalized_payload = _load_external_bytes_locator(
            project=project, spec=failure.get("normalized_response"),
            label="structured provider transport failure normalized response",
        )
        try:
            normalized: object = _strict_json_object(
                normalized_payload, label="failed normalized ChatGPT response",
            )
        except BlindEvaluationError:
            normalized = None
        expected_structure = _bounded_structured_gpt_response_structure(normalized)
        if failure.get("response_structure") != expected_structure:
            _fail("GPT transport failure response structure is stale")
    elif present_raw:
        if variant != "gpt" or len(present_raw) != len(raw_response_fields):
            _fail("raw GPT transport failure evidence must be supplied together")
        _raw_path, raw_payload = _load_external_bytes_locator(
            project=project, spec=failure.get("upstream_raw_sse"),
            label="failed ChatGPT upstream SSE",
        )
        _headers_path, headers = _load_bound_external_receipt(
            project=project, spec=failure.get("response_headers"),
            label="failed ChatGPT response headers",
        )[:2]
        if (
            set(headers) != {"header_names", "upstream_status"}
            or not isinstance(headers.get("header_names"), list)
            or headers["header_names"] != sorted(set(headers["header_names"]))
            or any(not isinstance(item, str) or not item for item in headers["header_names"])
            or not isinstance(headers.get("upstream_status"), int)
            or isinstance(headers.get("upstream_status"), bool)
        ):
            _fail("failed ChatGPT response header metadata is invalid")
        if failure.get("response_structure") != _bounded_chatgpt_sse_structure(raw_payload):
            _fail("failed ChatGPT SSE structure diagnostic is stale")


def _validate_codex_disabled_code_mode_argv(value: object) -> None:
    if (
        not isinstance(value, list) or not value
        or any(not isinstance(item, str) or not item for item in value)
    ):
        _fail("ChatGPT login proxy command_argv is invalid")
    settings: list[str] = []
    for index, item in enumerate(value):
        if item != "-c":
            continue
        if index + 1 >= len(value):
            _fail("ChatGPT login proxy command_argv has an incomplete config")
        settings.append(value[index + 1])
    for key in ("features.code_mode.enabled", "features.code_mode_host"):
        matching = [item for item in settings if item.split("=", 1)[0] == key]
        if matching != [f"{key}=false"]:
            _fail("ChatGPT login proxy did not uniquely disable Code Mode")


def _chatgpt_sse_forbidden(value: object) -> bool:
    if isinstance(value, Mapping):
        kind = value.get("type")
        if isinstance(kind, str) and any(
            token in kind.lower() for token in ("tool", "function", "refusal")
        ):
            return True
        if any(
            value.get(key) not in (None, [], "")
            for key in ("tool_calls", "function_call", "refusal")
        ):
            return True
        return any(_chatgpt_sse_forbidden(child) for child in value.values())
    if isinstance(value, list):
        return any(_chatgpt_sse_forbidden(child) for child in value)
    return False


def _bounded_chatgpt_sse_structure(raw: bytes) -> dict[str, Any]:
    result: dict[str, Any] = {
        "byte_count": len(raw), "utf8": False, "block_count": 0,
        "data_block_count": 0, "done_count": 0, "parsed_event_count": 0,
        "event_types": [], "omitted_event_types": 0,
    }
    try:
        text = raw.decode("utf-8", errors="strict").replace("\r\n", "\n")
    except UnicodeDecodeError:
        return result
    result["utf8"] = True
    event_types: list[str] = []
    blocks = [block for block in text.split("\n\n") if block]
    result["block_count"] = len(blocks)
    for block in blocks:
        data_lines = [
            line[5:].lstrip() for line in block.splitlines()
            if line.startswith("data:")
        ]
        if not data_lines:
            continue
        result["data_block_count"] += 1
        data = "\n".join(data_lines)
        if data == "[DONE]":
            result["done_count"] += 1
            continue
        try:
            event = _strict_json_object(
                data.encode("utf-8"), label="diagnostic ChatGPT SSE event",
            )
        except BlindEvaluationError:
            continue
        result["parsed_event_count"] += 1
        kind = event.get("type")
        if isinstance(kind, str):
            kind = re.sub(r"[^A-Za-z0-9_.:-]", "?", kind)[:32] or "unknown"
        else:
            kind = "unknown"
        if len(event_types) < 64:
            event_types.append(kind)
        else:
            result["omitted_event_types"] += 1
    result["event_types"] = event_types
    return result


def _rebuild_chatgpt_response_from_sse(payload: bytes) -> tuple[dict[str, Any], bytes]:
    """Independently replay the answer-bearing Responses SSE state machine."""

    try:
        text = payload.decode("utf-8", errors="strict").replace("\r\n", "\n")
    except UnicodeDecodeError as exc:
        raise BlindEvaluationError("ChatGPT SSE is not strict UTF-8") from exc
    events: list[dict[str, Any]] = []
    done_seen = False
    for block in text.split("\n\n"):
        lines = block.splitlines()
        if not lines:
            continue
        event_lines = [line[6:].lstrip() for line in lines if line.startswith("event:")]
        data_lines = [line[5:].lstrip() for line in lines if line.startswith("data:")]
        if not data_lines:
            continue
        data = "\n".join(data_lines)
        if data == "[DONE]":
            if done_seen:
                _fail("ChatGPT SSE repeats [DONE]")
            done_seen = True
            continue
        event = _strict_json_object(
            data.encode("utf-8"), label="ChatGPT SSE event",
        )
        if (
            len(event_lines) != 1 or event_lines[0] != event.get("type")
            or len(data_lines) != 1 or lines != [
                f"event: {event_lines[0]}", f"data: {data_lines[0]}",
            ]
        ):
            _fail("ChatGPT SSE event/data framing is not canonical")
        sequence = event.get("sequence_number")
        if (
            not isinstance(sequence, int) or isinstance(sequence, bool)
            or sequence != len(events) or done_seen
        ):
            _fail("ChatGPT SSE sequence is non-contiguous or follows [DONE]")
        events.append(event)
    if not events:
        _fail("ChatGPT SSE has no response events")

    allowed_types = {
        "response.created", "response.in_progress",
        "response.output_item.added", "response.output_item.done",
        "response.reasoning_summary_part.added",
        "response.reasoning_summary_text.delta",
        "response.reasoning_summary_text.done",
        "response.reasoning_summary_part.done",
        "response.content_part.added", "response.output_text.delta",
        "response.output_text.done", "response.content_part.done",
        "response.completed", "keepalive",
    }
    response_id: str | None = None
    created = 0
    in_progress = 0
    completed: list[dict[str, Any]] = []
    added_items: dict[int, tuple[str, str]] = {}
    done_items: dict[int, dict[str, Any]] = {}
    reasoning_summary_parts: dict[int, dict[int, dict[str, Any]]] = {}
    message_index: int | None = None
    message_id: str | None = None
    message_done: dict[str, Any] | None = None
    content_added = False
    text_done: str | None = None
    content_done: dict[str, Any] | None = None
    deltas: list[str] = []
    delta_bytes = 0

    def strict_index(value: object) -> bool:
        return isinstance(value, int) and not isinstance(value, bool) and value >= 0

    def message_coordinates(event: Mapping[str, Any]) -> bool:
        output_index = event.get("output_index")
        content_index = event.get("content_index")
        return (
            strict_index(output_index) and output_index == message_index
            and event.get("item_id") == message_id
            and strict_index(content_index) and content_index == 0
        )

    for position, event in enumerate(events):
        event_type = event.get("type")
        if event_type not in allowed_types or _chatgpt_sse_forbidden(event):
            _fail("ChatGPT SSE contains an unknown or prohibited event")
        if event_type == "keepalive":
            if (
                set(event) != {"type", "sequence_number"}
                or created != 1 or in_progress != 1 or completed
                or not (set(added_items) - set(done_items))
            ):
                _fail("ChatGPT SSE keepalive is malformed or outside active generation")
            continue
        response = event.get("response")
        if (
            event.get("error") not in (None, "", [], {})
            or (isinstance(response, Mapping) and response.get("error") is not None)
        ):
            _fail("ChatGPT SSE contains an error response")
        if event_type in {"response.created", "response.in_progress", "response.completed"}:
            if not isinstance(response, dict) or not isinstance(response.get("id"), str):
                _fail("ChatGPT SSE response lifecycle event is malformed")
            if response_id is None:
                response_id = response["id"]
            elif response["id"] != response_id:
                _fail("ChatGPT SSE response id changed")
        if event_type == "response.created":
            created += 1
            if position != 0 or created != 1 or response.get("status") != "in_progress":
                _fail("ChatGPT SSE response.created is duplicated or misplaced")
            continue
        if event_type == "response.in_progress":
            in_progress += 1
            if position != 1 or in_progress != 1 or response.get("status") != "in_progress":
                _fail("ChatGPT SSE response.in_progress is duplicated or misplaced")
            continue
        if event_type == "response.completed":
            if position != len(events) - 1 or response.get("status") != "completed":
                _fail("ChatGPT SSE response.completed is not terminal")
            completed.append(response)
            continue
        if event_type == "response.output_item.added":
            index = event.get("output_index")
            item = event.get("item")
            if (
                not isinstance(index, int) or isinstance(index, bool) or index < 0
                or index != len(added_items) or index in added_items
                or not isinstance(item, Mapping)
                or not isinstance(item.get("id"), str) or not item["id"]
                or item.get("type") not in {"reasoning", "message"}
            ):
                _fail("ChatGPT SSE output_item.added is malformed")
            added_items[index] = (item["id"], item["type"])
            if item["type"] == "reasoning":
                if item.get("summary") != []:
                    _fail("ChatGPT SSE must add reasoning with an empty summary")
                reasoning_summary_parts[index] = {}
            if item["type"] == "message":
                if (
                    message_id is not None or item.get("role") != "assistant"
                    or item.get("phase") != "final_answer"
                    or item.get("status") != "in_progress" or item.get("content") != []
                ):
                    _fail("ChatGPT SSE must add one empty assistant message")
                message_index, message_id = index, item["id"]
            continue
        if event_type == "response.output_item.done":
            index = event.get("output_index")
            item = event.get("item")
            if (
                not strict_index(index) or index not in added_items or index in done_items
                or not isinstance(item, Mapping)
                or (item.get("id"), item.get("type")) != added_items[index]
            ):
                _fail("ChatGPT SSE output_item.done does not match its added item")
            if item.get("type") == "reasoning":
                parts = reasoning_summary_parts.get(index)
                if parts is None or any(
                    part_state.get("part_done") is None for part_state in parts.values()
                ):
                    _fail("ChatGPT SSE reasoning summary is incomplete")
                rebuilt_summary = [
                    parts[summary_index]["part_done"]
                    for summary_index in range(len(parts))
                ]
                if item.get("summary") != rebuilt_summary:
                    _fail("ChatGPT SSE reasoning item summary differs from its events")
            done_items[index] = dict(item)
            if item.get("type") == "message":
                joined = "".join(deltas)
                content = item.get("content")
                if (
                    index != message_index or item.get("role") != "assistant"
                    or item.get("phase") != "final_answer"
                    or item.get("status") != "completed" or content_done is None
                    or text_done != joined or not isinstance(content, list)
                    or len(content) != 1 or content[0] != content_done
                ):
                    _fail("ChatGPT SSE completed assistant message is inconsistent")
                message_done = dict(item)
            continue
        if event_type == "response.content_part.added":
            part = event.get("part")
            if (
                content_added or not message_coordinates(event)
                or not isinstance(part, Mapping) or part.get("type") != "output_text"
                or part.get("text") != ""
            ):
                _fail("ChatGPT SSE output_text part is malformed")
            content_added = True
            continue
        if event_type == "response.output_text.delta":
            delta = event.get("delta")
            if (
                not content_added or text_done is not None or not message_coordinates(event)
                or not isinstance(delta, str)
            ):
                _fail("ChatGPT SSE output_text delta is malformed or misplaced")
            delta_bytes += len(delta.encode("utf-8"))
            if delta_bytes > _MAX_PROVIDER_RESPONSE_BYTES:
                _fail("ChatGPT SSE output_text exceeds its bound")
            deltas.append(delta)
            continue
        if event_type == "response.output_text.done":
            joined = "".join(deltas)
            if (
                text_done is not None or not message_coordinates(event)
                or event.get("text") != joined
            ):
                _fail("ChatGPT SSE output_text.done differs from its deltas")
            text_done = joined
            continue
        if event_type == "response.content_part.done":
            part = event.get("part")
            if (
                content_done is not None or text_done is None
                or not message_coordinates(event) or not isinstance(part, Mapping)
                or part.get("type") != "output_text" or part.get("text") != text_done
            ):
                _fail("ChatGPT SSE content_part.done differs from output_text.done")
            content_done = dict(part)
            continue
        # Reasoning summaries do not contribute answer text, but their complete
        # lifecycle is replayed and bound to the final reasoning item.
        index = event.get("output_index")
        item_id = event.get("item_id")
        if (
            not strict_index(index) or index not in added_items
            or index in done_items or added_items[index] != (item_id, "reasoning")
        ):
            _fail("ChatGPT SSE reasoning event is detached from its item")
        summary_index = event.get("summary_index")
        if not strict_index(summary_index):
            _fail("ChatGPT SSE reasoning summary index is malformed")
        parts = reasoning_summary_parts[index]
        if event_type == "response.reasoning_summary_part.added":
            part = event.get("part")
            if (
                summary_index != len(parts) or summary_index in parts
                or not isinstance(part, Mapping)
                or part.get("type") != "summary_text" or part.get("text") != ""
            ):
                _fail("ChatGPT SSE reasoning summary part.added is malformed")
            parts[summary_index] = {
                "deltas": [], "text_done": None, "part_done": None,
            }
            continue
        if summary_index not in parts:
            _fail("ChatGPT SSE reasoning summary event precedes part.added")
        part_state = parts[summary_index]
        if event_type == "response.reasoning_summary_text.delta":
            delta = event.get("delta")
            if (
                part_state["text_done"] is not None
                or part_state["part_done"] is not None
                or not isinstance(delta, str)
            ):
                _fail("ChatGPT SSE reasoning summary delta is malformed or misplaced")
            part_state["deltas"].append(delta)
            continue
        if event_type == "response.reasoning_summary_text.done":
            joined = "".join(part_state["deltas"])
            if (
                part_state["text_done"] is not None
                or part_state["part_done"] is not None
                or event.get("text") != joined
            ):
                _fail("ChatGPT SSE reasoning summary text.done differs from its deltas")
            part_state["text_done"] = joined
            continue
        if event_type == "response.reasoning_summary_part.done":
            part = event.get("part")
            if (
                part_state["text_done"] is None or part_state["part_done"] is not None
                or not isinstance(part, Mapping)
                or part.get("type") != "summary_text"
                or part.get("text") != part_state["text_done"]
            ):
                _fail("ChatGPT SSE reasoning summary part.done is inconsistent")
            part_state["part_done"] = dict(part)
            continue
        _fail("ChatGPT SSE reasoning summary event is unsupported")

    if len(completed) != 1:
        _fail("ChatGPT SSE must contain exactly one response.completed")
    response = completed[0]
    existing_output = response.get("output")
    rebuilt_output = [done_items[index] for index in range(len(done_items))]
    if (
        created != 1 or in_progress != 1 or set(added_items) != set(done_items)
        or message_done is None or message_id is None or message_index is None
        or text_done is None or content_done is None
        or not isinstance(existing_output, list)
        or (existing_output != [] and existing_output != rebuilt_output)
        or response.get("incomplete_details") is not None
        or response.get("tools") != [] or response.get("tool_choice") != "none"
        or _chatgpt_sse_forbidden(response)
    ):
        _fail("ChatGPT SSE did not complete one consistent tool-free message")
    rebuilt = dict(response)
    rebuilt["output"] = rebuilt_output
    rebuilt_payload = _json_bytes(rebuilt)
    return rebuilt, rebuilt_payload


def _validate_structured_transport_provenance(
    *, project: Path, runtime: Mapping[str, Any], aggregate: Mapping[str, Any],
    attempt: Mapping[str, Any], request_path: Path, request_payload: bytes,
    response_path: Path | None, response_payload: bytes | None,
    expected_gpt_exchange: Mapping[str, Any] | None,
    expected_submission: Mapping[str, Any] | None = None,
    allow_invalid_submission: bool = False,
) -> None:
    provenance = attempt.get("adapter_provenance")
    if not isinstance(provenance, Mapping):
        _fail("structured solver adapter_provenance must be an object")
    variant = aggregate.get("variant")
    expected_adapter = (
        "chatgpt_login_proxy_v1" if variant == "gpt"
        else "structured_broker_http_v1"
    )
    if attempt.get("adapter") != expected_adapter:
        _fail("structured solver attempt adapter differs from its variant")
    status = attempt.get("status")
    if status == "transport_error":
        _strict_fields(
            provenance, _STRUCTURED_FAILURE_PROVENANCE_FIELDS,
            label="structured transport failure provenance",
        )
        failure_path, failure, _payload = _load_bound_external_receipt(
            project=project, spec=provenance.get("transport_failure_receipt"),
            label="structured provider transport failure",
        )
        if failure_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
            _fail("structured provider transport failure must be mode 0400")
        if frozenset(failure) not in {
            frozenset(_STRUCTURED_TRANSPORT_FAILURE_FIELDS),
            frozenset(_STRUCTURED_TRANSPORT_FAILURE_DIAGNOSTIC_FIELDS),
            frozenset(_STRUCTURED_TRANSPORT_FAILURE_CHANNEL_DIAGNOSTIC_FIELDS),
            frozenset(_STRUCTURED_TRANSPORT_FAILURE_GPT_RESPONSE_FIELDS),
            frozenset(_STRUCTURED_TRANSPORT_FAILURE_GPT_RAW_FIELDS),
        }:
            _fail("structured provider transport failure has unexpected fields")
        if (
            failure.get("schema_version") != SCHEMA_VERSION
            or failure.get("protocol") != PROTOCOL
            or failure.get("phase") != "structured_provider_transport_failure"
            or failure.get("variant") != variant
            or failure.get("target_id") != attempt.get("target_id")
            or failure.get("attempt") != attempt.get("attempt")
            or failure.get("adapter") != expected_adapter
            or failure.get("request") != attempt.get("request")
            or failure.get("provider_invocation_started") is not True
            or failure.get("status") != "failed_without_valid_response"
        ):
            _fail("structured provider transport failure provenance is stale")
        _validate_structured_failure_diagnostic(
            project=project, failure=failure, variant=variant,
        )
        if expected_gpt_exchange is not None and dict(
            provenance["transport_failure_receipt"]
        ) != dict(expected_gpt_exchange):
            _fail("GPT aggregate exchange does not bind its failure receipt")
        return
    if variant == "kimi-k3":
        _strict_fields(
            provenance, _STRUCTURED_KIMI_PROVENANCE_FIELDS,
            label="structured Kimi adapter provenance",
        )
        if response_payload is None or (
            provenance.get("endpoint") != "/v1/messages"
            or provenance.get("request_sha256")
            != _sha256_bytes(request_payload.rstrip(b"\n"))
            or provenance.get("raw_response_sha256") != _sha256_bytes(response_payload)
            or provenance.get("reasoning_control") != {
                "provider_field_supported": False,
                "model_id": aggregate.get("model_id"),
                "max_tokens": 131072,
            }
        ):
            _fail("structured Kimi adapter provenance is stale")
        return
    _strict_fields(
        provenance, _STRUCTURED_GPT_PROVENANCE_FIELDS,
        label="structured GPT adapter provenance",
    )
    proxy_spec = provenance.get("proxy_receipt")
    if expected_gpt_exchange is None or proxy_spec != expected_gpt_exchange:
        _fail("GPT aggregate exchange does not bind its proxy receipt")
    proxy_path, receipt, _receipt_payload = _load_bound_external_receipt(
        project=project, spec=proxy_spec, label="ChatGPT login proxy receipt",
    )
    if proxy_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail("ChatGPT login proxy receipt must be mode 0400")
    _strict_fields(receipt, _LOGIN_PROXY_RECEIPT_FIELDS, label="ChatGPT login proxy receipt")
    if (
        receipt.get("schema_version") != SCHEMA_VERSION
        or receipt.get("protocol") != PROTOCOL
        or receipt.get("phase") != "chatgpt_login_proxy_exchange"
        or receipt.get("variant") != "gpt"
        or receipt.get("run_id") != aggregate.get("run_id")
        or receipt.get("target_id") != attempt.get("target_id")
        or receipt.get("attempt") != attempt.get("attempt")
        or receipt.get("model_id") != aggregate.get("model_id")
        or receipt.get("adapter") != "chatgpt_login_proxy_v1"
        or receipt.get("upstream_origin") != "https://chatgpt.com"
        or receipt.get("upstream_status") != 200
        or receipt.get("codex_exit_code") != 0
        or receipt.get("tool_events") != 0
        or receipt.get("pre_registered_request") != attempt.get("request")
    ):
        _fail("ChatGPT login proxy receipt metadata is stale")
    _validate_codex_disabled_code_mode_argv(receipt.get("command_argv"))
    runtime_files = runtime.get("files")
    if not isinstance(runtime_files, Mapping):
        _fail("sealed runtime inventory is missing")
    runtime_hashes = set(runtime_files.values())
    if _require_sha256(
        receipt.get("proxy_binary_sha256"), field="login proxy binary sha256"
    ) not in runtime_hashes:
        _fail("ChatGPT login proxy binary is absent from runtime inventory")
    _codex_path, _codex_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("codex_binary"), label="Codex binary",
        exact_private_mode=False,
    )
    if _sha256_bytes(_codex_payload) not in runtime_hashes:
        _fail("Codex binary is absent from runtime inventory")
    normalized_path, normalized_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("normalized_response"),
        label="normalized ChatGPT response",
    )
    if (
        response_path is None or response_payload is None
        or normalized_payload != response_payload
        or provenance.get("normalized_response_sha256") != _sha256_bytes(response_payload)
    ):
        _fail("ChatGPT normalized response binding is stale")
    _sse_path, sse_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("upstream_raw_sse"),
        label="ChatGPT upstream SSE",
    )
    if provenance.get("upstream_raw_sse_sha256") != _sha256_bytes(sse_payload):
        _fail("ChatGPT upstream SSE binding is stale")
    _rebuilt_response, rebuilt_payload = _rebuild_chatgpt_response_from_sse(
        sse_payload,
    )
    if rebuilt_payload != normalized_payload:
        _fail("normalized ChatGPT response is not the strict SSE reconstruction")
    _jsonl_path, jsonl_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("codex_jsonl"), label="Codex JSONL",
    )
    _stderr_path, _stderr_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("codex_stderr"), label="Codex stderr",
    )
    _last_path, last_payload = _load_external_bytes_locator(
        project=project, spec=receipt.get("codex_last_message"),
        label="Codex last message",
    )
    messages: list[dict[str, Any]] = []
    events = 0
    thread_started = False
    turn_started = False
    disabled_host_confirmations = 0
    for line in jsonl_payload.splitlines():
        if not line.strip():
            continue
        event = _strict_json_object(line, label="Codex JSONL event")
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
                _fail("Codex transport turn.started precedes disabled-host confirmation")
            turn_started = True
        is_disabled_host_confirmation = (
            event_type == "item.completed"
            and isinstance(item, Mapping)
            and set(event) == {"type", "item"}
            and set(item) == {"id", "type", "message"}
            and isinstance(item.get("id"), str)
            and 0 < len(item["id"]) <= 128
            and item_type == "error"
            and item.get("message") == _CODEX_DISABLED_HOST_CONFIRMATION
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
            _fail("Codex transport emitted a tool event")
        if event.get("type") == "item.completed" and item_type == "agent_message":
            if not turn_started:
                _fail("Codex transport message precedes turn.started")
            text = item.get("text")
            if isinstance(text, str) and text.strip():
                messages.append(_strict_json_object(text.encode(), label="Codex message"))
    normalized = _strict_json_object(normalized_payload, label="normalized ChatGPT response")
    normalized_submission = (
        dict(expected_submission)
        if expected_submission is not None
        else (
            _structured_raw_submission_from_response(normalized, variant="gpt")
            if allow_invalid_submission
            else _structured_submission_from_response(normalized, variant="gpt")
        )
    )
    if (
        events != provenance.get("event_count")
        or not thread_started or not turn_started
        or disabled_host_confirmations != 1
        or len(messages) != 1 or messages[0] != normalized_submission
        or _strict_json_object(last_payload, label="Codex last message") != normalized_submission
    ):
        _fail("Codex transport output does not match normalized model response")
    if normalized_path == response_path:
        _fail("ChatGPT normalized transport and controller response must be separately sealed")


def _sealed_codex_jsonl_event_count(
    *, project: Path, exchange: Mapping[str, Any], label: str,
) -> int:
    """Count the bound Codex JSONL events, independently of SSE completion count."""
    _path, payload = _load_external_bytes_locator(
        project=project, spec=exchange.get("codex_jsonl"),
        label=f"{label} Codex JSONL",
    )
    count = 0
    for line in payload.splitlines():
        if not line.strip():
            continue
        _strict_json_object(line, label=f"{label} Codex JSONL event")
        count += 1
    if count < 1:
        _fail(f"{label} Codex JSONL is empty")
    return count


def _load_and_validate_structured_solver(
    *, project: Path, seal: Mapping[str, Any],
    bundle_records: Mapping[str, tuple[dict[str, Any], str]] | None = None,
) -> tuple[dict[str, Any], bytes, dict[str, dict[str, Any]]]:
    """Rebuild every controller-side model request/response/artifact binding."""
    receipt_path, aggregate, aggregate_payload = _load_bound_external_receipt(
        project=project, spec=seal.get("structured_solver_receipt"),
        label="structured solver aggregate", max_bytes=_MAX_CONTROLLER_SEAL_BYTES,
    )
    if receipt_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail("structured solver aggregate must be controller-owned mode 0400")
    _strict_fields(aggregate, _STRUCTURED_SOLVER_FIELDS, label="structured solver aggregate")
    solver = seal.get("solver")
    scope = seal.get("freeze_scope")
    bundle = seal.get("blind_bundle")
    runtime = seal.get("runtime_inventory")
    if not all(isinstance(item, Mapping) for item in (solver, scope, bundle, runtime)):
        _fail("structured solver controller bindings are incomplete")
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3"),
    }.get(aggregate.get("variant"))
    if (
        aggregate.get("schema_version") != SCHEMA_VERSION
        or aggregate.get("protocol") != PROTOCOL
        or aggregate.get("phase") != "structured_solver_aggregate"
        or aggregate.get("request_profile") != _STRUCTURED_REQUEST_PROFILE
        or aggregate.get("tools_enabled") is not False
        or aggregate.get("store") is not False
        or aggregate.get("all_targets_finalized") is not True
        or expected_identity
        != (aggregate.get("model_family"), aggregate.get("model_id"))
        or any(aggregate.get(field) != solver.get(field) for field in _SOLVER_FIELDS)
        or aggregate.get("scope_ids") != scope.get("ids")
    ):
        _fail("structured solver aggregate metadata/model/scope is stale")
    aggregate_bundle = aggregate.get("bundle")
    if not isinstance(aggregate_bundle, Mapping):
        _fail("structured solver aggregate bundle binding is missing")
    _strict_fields(
        aggregate_bundle, _STRUCTURED_SOLVER_BUNDLE_FIELDS,
        label="structured solver aggregate bundle",
    )
    raw_bundle_path = aggregate_bundle.get("path")
    if not isinstance(raw_bundle_path, str) or not Path(raw_bundle_path).is_absolute():
        _fail("structured solver bundle path must be absolute")
    sealed_bundle_path = _resolve_project_locator(
        project, bundle.get("path"), label="questions-only bundle"
    )
    if (
        Path(raw_bundle_path).resolve() != sealed_bundle_path
        or aggregate_bundle.get("sha256") != bundle.get("sha256")
        or aggregate_bundle.get("row_count") != bundle.get("row_count")
        or aggregate_bundle.get("ids") != bundle.get("ids")
    ):
        _fail("structured solver aggregate bundle binding is stale")
    controller_sha = _require_sha256(
        aggregate.get("controller_binary_sha256"),
        field="structured solver controller_binary_sha256",
    )
    runtime_files = runtime.get("files")
    if not isinstance(runtime_files, Mapping) or controller_sha not in set(runtime_files.values()):
        _fail("structured solver controller binary is absent from sealed runtime inventory")
    request_count = aggregate.get("request_count")
    if not isinstance(request_count, int) or isinstance(request_count, bool) or request_count < 1:
        _fail("structured solver request_count must be positive")
    _precommit_path, _precommit, precommit_payload, _precommit_files = (
        _load_source_first_precommit(project=project, seal=seal)
    )
    if aggregate.get("source_first_precommit_sha256") != _sha256_bytes(
        precommit_payload
    ):
        _fail("structured solver does not bind the pre-solver source-first commitment")
    transport = aggregate.get("transport")
    if not isinstance(transport, Mapping):
        _fail("structured solver transport binding is missing")
    gpt_exchange_specs: list[Mapping[str, Any]] = []
    if aggregate.get("variant") == "kimi-k3":
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_KIMI_FIELDS,
            label="structured solver Kimi transport",
        )
        if aggregate.get("adapter") != "structured_broker_http_v1" or (
            transport.get("kind") != "structured_broker_http_v1"
        ):
            _fail("structured solver Kimi adapter/transport is stale")
        _ready, _ready_sha, transcript, _transcript_sha = (
            _load_and_validate_model_broker_binding(
                project=project,
                binding={
                    "ready_receipt": transport.get("ready_receipt"),
                    "transcript": transport.get("transcript"),
                },
                variant="kimi-k3", run_id=aggregate.get("run_id"),
                model_id=aggregate.get("model_id"), runtime=runtime,
                minimum_requests=1, exact_requests=request_count,
                request_profile=_STRUCTURED_REQUEST_PROFILE,
                label="structured solver model_broker",
            )
        )
        if aggregate.get("request_response_chain_sha256") != transcript.get(
            "request_response_chain_sha256"
        ):
            _fail("structured solver Kimi request chain is stale")
    elif aggregate.get("variant") == "gpt":
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_GPT_FIELDS,
            label="structured solver GPT transport",
        )
        if aggregate.get("adapter") != "chatgpt_login_proxy_v1" or (
            transport.get("kind") != "chatgpt_login_proxy_v1"
        ):
            _fail("structured solver GPT adapter/transport is stale")
        exchanges = transport.get("exchanges")
        if not isinstance(exchanges, list) or len(exchanges) != request_count:
            _fail("structured solver GPT exchange coverage differs from request count")
        gpt_exchange_specs = []
        exchange_chain = "0" * 64
        for index, spec in enumerate(exchanges, start=1):
            if not isinstance(spec, Mapping):
                _fail(f"structured solver GPT exchange {index} is not a locator")
            _strict_fields(spec, _EXTERNAL_RECEIPT_FIELDS, label="GPT exchange locator")
            digest = _require_sha256(spec.get("sha256"), field="GPT exchange sha256")
            exchange_chain = _sha256_bytes(
                bytes.fromhex(exchange_chain) + bytes.fromhex(digest)
            )
            gpt_exchange_specs.append(spec)
        if (
            transport.get("exchange_chain_sha256") != exchange_chain
            or aggregate.get("request_response_chain_sha256") != exchange_chain
        ):
            _fail("structured solver GPT exchange chain is stale")
    else:
        _fail("structured solver uses an unsupported transport variant")
    if bundle_records is None:
        _bundle_path, _bundle_payload, parsed = _parse_blind_bundle(
            project=project, seal=seal
        )
        bundle_records = parsed
    scope_ids = list(scope.get("ids") or [])
    targets = aggregate.get("targets")
    if not isinstance(targets, list) or len(targets) != len(scope_ids):
        _fail("structured solver target count differs from controller scope")
    by_id: dict[str, dict[str, Any]] = {}
    total_attempts = 0
    aggregate_parent = receipt_path.parent
    for expected_id, target in zip(scope_ids, targets, strict=True):
        if not isinstance(target, Mapping):
            _fail("structured solver target receipt must be an object")
        _strict_fields(target, _STRUCTURED_TARGET_FIELDS, label="structured solver target")
        if target.get("id") != expected_id or expected_id in by_id:
            _fail("structured solver target order/ID set differs from scope")
        if expected_id not in bundle_records:
            _fail(f"structured solver target is absent from bundle: {expected_id}")
        expected_adapter = (
            "chatgpt_login_proxy_v1"
            if aggregate.get("variant") == "gpt"
            else "structured_broker_http_v1"
        )
        if target.get("adapter") != expected_adapter:
            _fail(f"structured solver target adapter is stale for {expected_id}")
        row, blind_hash = bundle_records[expected_id]
        report_spec = target.get("source_report")
        if not isinstance(report_spec, Mapping):
            _fail(f"structured solver source_report binding is missing for {expected_id}")
        _strict_fields(
            report_spec, _EXTERNAL_RECEIPT_FIELDS,
            label=f"structured solver {expected_id} source_report",
        )
        raw_report_path = report_spec.get("path")
        if not isinstance(raw_report_path, str) or not Path(raw_report_path).is_absolute():
            _fail("structured solver source_report path must be absolute")
        report_path = _project_path_without_symlinks(
            Path(raw_report_path), project, label="structured solver source_report"
        )
        _require_controller_owned_readonly(
            report_path, label=f"structured solver source_report {expected_id}"
        )
        report, report_payload = _read_json(
            report_path, label=f"structured solver source_report {expected_id}"
        )
        if _sha256_bytes(report_payload) != report_spec.get("sha256"):
            _fail(f"structured solver source_report hash is stale for {expected_id}")
        expected_entry = _expected_report_entry(
            project=project, bundle_row=row, blind_hash=blind_hash
        )
        if (
            report.get("schema_version") != 3
            or report.get("evaluation_mode") != "answer_blind"
            or report.get("official_answer_seen") is not False
            or report.get("phase") != "solve"
            or report.get("blind_record_sha256") != blind_hash
            or report.get("entry") != expected_entry
            or report.get("previous_parts") != expected_entry.get("previous_parts", [])
        ):
            _fail(f"structured solver source_report differs from the bundle for {expected_id}")
        projection = _structured_problem_projection(row)
        projection_payload = _json_bytes(projection)
        projection_sha = _sha256_bytes(projection_payload)
        projection_path = aggregate_parent / (
            f"{aggregate.get('variant')}-{expected_id}-problem-projection.json"
        )
        _require_controller_owned_readonly(
            projection_path, label=f"structured problem projection {expected_id}"
        )
        if projection_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
            _fail("structured problem projection must be mode 0400")
        if (
            target.get("problem_projection_sha256") != projection_sha
            or _read_plain_bytes(
                projection_path, label=f"structured problem projection {expected_id}"
            ) != projection_payload
        ):
            _fail(f"structured problem projection is stale for {expected_id}")
        attempts = target.get("attempts")
        accepted_attempt = target.get("accepted_attempt")
        if (
            not isinstance(attempts, list) or not attempts
            or len(attempts) > _MAX_STRUCTURED_ATTEMPTS
            or not isinstance(accepted_attempt, int)
            or isinstance(accepted_attempt, bool)
            or accepted_attempt != len(attempts)
        ):
            _fail(f"structured solver attempt/acceptance count is invalid for {expected_id}")
        raw_target = report.get("output_lean")
        target_path = _resolve_project_locator(
            project, raw_target, label=f"structured solver target {expected_id}"
        )
        target_relative = target_path.relative_to(project).as_posix()
        source_report_relative = report_path.relative_to(project).as_posix()
        prepared_spec = target.get("prepared_blueprint")
        prepared_payload: bytes | None = None
        if prepared_spec is not None:
            _prepared_path, prepared_payload = _load_external_bytes_locator(
                project=project, spec=prepared_spec,
                label=f"structured prepared blueprint {expected_id}",
            )
        gpt_images, kimi_images = _structured_image_parts(project=project, row=row)
        prior_diagnostics: list[dict[str, Any]] = []
        previous_attempt_sha: str | None = None
        attempt_chain = "0" * 64
        accepted_submission: dict[str, Any] | None = None
        accepted_artifacts: dict[str, dict[str, str]] | None = None
        for attempt_number, locator in enumerate(attempts, start=1):
            attempt_path, attempt, attempt_payload = _load_bound_external_receipt(
                project=project, spec=locator,
                label=f"structured solver {expected_id} attempt {attempt_number}",
            )
            if attempt_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
                _fail("structured solver attempt receipt must be mode 0400")
            _strict_fields(
                attempt, _STRUCTURED_ATTEMPT_FIELDS,
                label=f"structured solver {expected_id} attempt {attempt_number}",
            )
            if (
                attempt.get("schema_version") != SCHEMA_VERSION
                or attempt.get("protocol") != PROTOCOL
                or attempt.get("phase") != "structured_solver_attempt"
                or attempt.get("target_id") != expected_id
                or attempt.get("attempt") != attempt_number
                or attempt.get("previous_attempt_sha256") != previous_attempt_sha
                or attempt.get("request_profile") != _STRUCTURED_REQUEST_PROFILE
                or attempt.get("tools_enabled") is not False
                or attempt.get("store") is not False
                or attempt.get("problem_projection_sha256") != projection_sha
                or any(
                    attempt.get(field) != aggregate.get(field)
                    for field in ("variant", "model_family", "model_id", "run_id")
                )
            ):
                _fail(f"structured solver attempt provenance is stale for {expected_id}")
            if attempt.get("prior_diagnostics_sha256") != _sha256_bytes(
                _json_bytes(prior_diagnostics)
            ):
                _fail(f"structured solver prior diagnostics chain is stale for {expected_id}")
            request_path, request, request_payload = _load_bound_external_receipt(
                project=project, spec=attempt.get("request"),
                label=f"structured solver {expected_id} request {attempt_number}",
                max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
            )
            expected_request = _structured_provider_request(
                variant=str(aggregate["variant"]), model_id=str(aggregate["model_id"]),
                projection=projection, gpt_images=gpt_images, kimi_images=kimi_images,
                diagnostics=prior_diagnostics,
            )
            if request != expected_request or request_payload != _json_bytes(expected_request):
                _fail(f"structured solver request is not the canonical blind prompt for {expected_id}")
            if request_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
                _fail("structured solver request must be mode 0400")
            status = attempt.get("status")
            response_path: Path | None = None
            response_payload: bytes | None = None
            submission: dict[str, Any] | None = None
            submission_path: Path | None = None
            constructed_candidate: dict[str, Any] | None = None
            invalid_response_submission = False
            transport_submission: dict[str, Any] | None = None
            if status == "transport_error":
                if any(
                    attempt.get(field) is not None
                    for field in (
                        "response", "submission", "constructed_candidate_sha256",
                        "staged_artifacts", "artifacts",
                    )
                ):
                    _fail(f"structured transport-error attempt carries artifacts for {expected_id}")
            else:
                response_path, _response_unused, response_payload = _load_bound_external_receipt(
                    project=project, spec=attempt.get("response"),
                    label=f"structured solver {expected_id} response {attempt_number}",
                    max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
                )
                response = _strict_json_object(
                    response_payload, label=f"structured solver {expected_id} provider response"
                )
                if (
                    response_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400
                    or response_path.parent != aggregate_parent
                ):
                    _fail("structured solver response must be a controller-owned mode 0400 artifact")
                try:
                    submission = _structured_submission_from_response(
                        response, variant=str(aggregate["variant"])
                    )
                except BlindEvaluationError:
                    if status != "rejected":
                        raise
                    invalid_response_submission = True
                    transport_submission = _structured_raw_submission_from_response(
                        response, variant=str(aggregate["variant"])
                    )
                    if attempt.get("submission") is not None:
                        submission_path, stored_submission, submission_payload = (
                            _load_bound_external_receipt(
                                project=project, spec=attempt.get("submission"),
                                label=(
                                    f"structured solver {expected_id} rejected raw "
                                    f"submission {attempt_number}"
                                ),
                            )
                        )
                        if (
                            submission_path.stat(follow_symlinks=False).st_mode & 0o777
                            != 0o400
                            or stored_submission != transport_submission
                            or submission_payload != _json_bytes(transport_submission)
                            or submission_path.parent != aggregate_parent
                        ):
                            _fail(
                                f"structured solver stored rejected submission is not "
                                f"response-derived for {expected_id}"
                            )
                if submission is not None:
                    transport_submission = submission
                    submission_path, stored_submission, submission_payload = (
                        _load_bound_external_receipt(
                            project=project, spec=attempt.get("submission"),
                            label=f"structured solver {expected_id} submission {attempt_number}",
                        )
                    )
                    if (
                        submission_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400
                        or stored_submission != submission
                        or submission_payload != _json_bytes(submission)
                        or submission_path.parent != aggregate_parent
                    ):
                        _fail(f"structured solver stored submission is not response-derived for {expected_id}")
                    try:
                        constructed_candidate = _construct_structured_candidate(
                            submission, target_id=expected_id, blind_hash=blind_hash,
                            source_entry=row,
                        )
                    except BlindEvaluationError:
                        if status == "accepted" or attempt.get("staged_artifacts") is not None:
                            raise
            expected_exchange = (
                gpt_exchange_specs[total_attempts]
                if aggregate.get("variant") == "gpt" else None
            )
            _validate_structured_transport_provenance(
                project=project, runtime=runtime, aggregate=aggregate,
                attempt=attempt, request_path=request_path,
                request_payload=request_payload, response_path=response_path,
                response_payload=response_payload,
                expected_gpt_exchange=expected_exchange,
                expected_submission=transport_submission,
                allow_invalid_submission=invalid_response_submission,
            )
            diagnostics = _validate_structured_diagnostics(
                attempt.get("diagnostics"),
                label=f"structured solver {expected_id} diagnostics {attempt_number}",
            )
            artifacts = attempt.get("artifacts")
            if status == "rejected":
                if artifacts is not None or not diagnostics or attempt_number == len(attempts):
                    _fail(f"structured rejected attempt is not fail-closed for {expected_id}")
                if invalid_response_submission and any(
                    item.get("kind") != "controller_scan" for item in diagnostics
                ):
                    _fail(f"structured invalid provider submission lacks controller-scan diagnostics for {expected_id}")
            elif status == "accepted":
                if (
                    attempt_number != len(attempts) or diagnostics
                    or submission is None or constructed_candidate is None
                ):
                    _fail(f"structured accepted attempt is not the terminal clean attempt for {expected_id}")
                accepted_artifacts = _structured_artifact_map(
                    artifacts, project=project,
                    label=f"structured solver {expected_id} accepted artifacts",
                )
                accepted_submission = submission
            elif status == "transport_error":
                if not diagnostics or attempt_number == len(attempts):
                    _fail(f"structured transport-error attempt is not fail-closed for {expected_id}")
            else:
                _fail(f"structured solver attempt has invalid status for {expected_id}")
            if constructed_candidate is None:
                if (
                    attempt.get("constructed_candidate_sha256") is not None
                    or attempt.get("staged_artifacts") is not None
                ):
                    _fail(f"structured invalid submission has a staged candidate for {expected_id}")
            else:
                expected_stage_payloads = {
                    "candidate": _json_bytes(constructed_candidate),
                    "lean": str(submission["lean_source"]).encode("utf-8"),  # type: ignore[index]
                    "blueprint": _compose_structured_blueprint(
                        generated=submission["blueprint"],  # type: ignore[index]
                        prepared_payload=prepared_payload,
                        target_relative=target_relative,
                        source_report_relative=source_report_relative,
                    ),
                }
                if attempt.get("constructed_candidate_sha256") != _sha256_bytes(
                    expected_stage_payloads["candidate"]
                ):
                    _fail(f"structured constructed candidate hash is stale for {expected_id}")
                staged = attempt.get("staged_artifacts")
                if not isinstance(staged, Mapping):
                    _fail(f"structured staged artifacts are missing for {expected_id}")
                _strict_fields(staged, _STRUCTURED_ARTIFACT_NAMES, label="staged artifacts")
                for name in sorted(_STRUCTURED_ARTIFACT_NAMES):
                    _stage_path, stage_payload = _load_external_bytes_locator(
                        project=project, spec=staged.get(name),
                        label=f"structured staged {name}",
                    )
                    if stage_payload != expected_stage_payloads[name]:
                        _fail(f"structured staged {name} differs from model submission")
            attempt_without_chain = dict(attempt)
            claimed_chain = _require_sha256(
                attempt_without_chain.pop("attempt_chain_sha256"),
                field=f"structured solver {expected_id} attempt_chain_sha256",
            )
            attempt_chain = _sha256_bytes(
                bytes.fromhex(attempt_chain) + _json_bytes(attempt_without_chain)
            )
            if claimed_chain != attempt_chain:
                _fail(f"structured solver attempt chain is invalid for {expected_id}")
            previous_attempt_sha = _sha256_bytes(attempt_payload)
            prior_diagnostics = diagnostics
            total_attempts += 1
        if accepted_submission is None or accepted_artifacts is None:
            _fail(f"structured solver has no accepted attempt for {expected_id}")
        final_artifacts = _structured_artifact_map(
            target.get("final_artifacts"), project=project,
            label=f"structured solver {expected_id} final artifacts",
        )
        if final_artifacts != accepted_artifacts or target.get(
            "target_chain_sha256"
        ) != attempt_chain:
            _fail(f"structured solver final artifact/attempt chain is stale for {expected_id}")
        target_stem = Path(target_relative).with_suffix("")
        composed_blueprint = _compose_structured_blueprint(
            generated=accepted_submission["blueprint"],
            prepared_payload=prepared_payload,
            target_relative=target_relative,
            source_report_relative=source_report_relative,
        )
        expected_paths = {
            "candidate": f"blind_candidates/{expected_id}.json",
            "lean": target_relative,
            "blueprint": (
                "blueprint/src/chapters/" + "_".join(target_stem.parts) + ".tex"
            ),
        }
        if {
            name: item["path"] for name, item in final_artifacts.items()
        } != expected_paths:
            _fail(f"structured solver artifact paths are not deterministic for {expected_id}")
        accepted_candidate = _construct_structured_candidate(
            accepted_submission, target_id=expected_id, blind_hash=blind_hash,
            source_entry=row,
        )
        candidate_payload = _json_bytes(accepted_candidate)
        expected_payloads = {
            "candidate": candidate_payload,
            "lean": str(accepted_submission["lean_source"]).encode("utf-8"),
            "blueprint": composed_blueprint,
        }
        for name, item in final_artifacts.items():
            artifact_path = _resolve_project_locator(
                project, item["path"], label=f"structured final {name} artifact"
            )
            payload = _read_plain_bytes(artifact_path, label=f"structured final {name} artifact")
            if payload != expected_payloads[name] or item["sha256"] != _sha256_bytes(payload):
                _fail(f"structured final {name} artifact differs from accepted response")
        if accepted_candidate.get("id") != expected_id or (
            accepted_candidate.get("blind_record_sha256") != blind_hash
        ):
            _fail(f"structured candidate bundle provenance is stale for {expected_id}")
        by_id[expected_id] = {
            "submission": accepted_submission,
            "artifacts": final_artifacts,
            "attempt_count": len(attempts),
            "source_report_path": report_path,
            "source_report_sha256": _sha256_bytes(report_payload),
        }
    if total_attempts != request_count or set(by_id) != set(scope_ids):
        _fail("structured solver aggregate omits or adds model attempts/targets")
    return aggregate, aggregate_payload, by_id


def _validate_verifier_receipt(
    receipt: Mapping[str, Any], *, seal: Mapping[str, Any]
) -> None:
    _strict_fields(receipt, _VERIFIER_RECEIPT_FIELDS, label="Lean verifier receipt")
    if (
        receipt.get("schema_version") != 1
        or receipt.get("protocol") != PROTOCOL
        or receipt.get("phase") != VERIFIER_PHASE
        or receipt.get("evaluation_mode") != "answer_blind"
    ):
        _fail("Lean verifier receipt has unsupported metadata")
    uid = receipt.get("verifier_uid")
    if not isinstance(uid, int) or isinstance(uid, bool) or uid == 0:
        _fail("Lean verifier receipt must be produced by a non-root UID")
    if receipt.get("network_answer_blind") is not False:
        _fail("Lean verifier receipt may not claim unverified network blindness")
    if receipt.get("compiled") is not True:
        _fail("Lean verifier receipt is not passing")
    runtime = receipt.get("runtime_executable")
    if not isinstance(runtime, dict):
        _fail("Lean verifier receipt runtime_executable must be an object")
    _strict_fields(runtime, _VERIFIER_RUNTIME_FIELDS, label="Lean verifier runtime")
    runtime_path = Path(str(runtime.get("path") or ""))
    if not runtime_path.is_absolute():
        _fail("Lean verifier runtime path must be absolute")
    _require_root_owned_readonly(runtime_path, label="Lean verifier runtime")
    if _sha256_bytes(_read_plain_bytes(runtime_path, label="Lean verifier runtime")) != _require_sha256(
        runtime.get("sha256"), field="Lean verifier runtime.sha256"
    ):
        _fail("Lean verifier runtime executable hash drift")
    dependency = seal["dependency_inventory"]
    runtime_inventory = seal["runtime_inventory"]
    snapshot = seal["snapshot_inventory"]
    assert (
        isinstance(dependency, Mapping)
        and isinstance(runtime_inventory, Mapping)
        and isinstance(snapshot, Mapping)
    )
    if receipt.get("dependency_inventory_sha256") != dependency.get("files_sha256"):
        _fail("Lean verifier receipt dependency inventory is stale")
    if receipt.get("runtime_inventory_sha256") != runtime_inventory.get("files_sha256"):
        _fail("Lean verifier receipt runtime inventory is stale")
    runtime_root = Path(str(runtime_inventory.get("root") or "")).resolve()
    try:
        runtime_relative = runtime_path.resolve().relative_to(runtime_root).as_posix()
    except ValueError:
        _fail("Lean verifier executable is outside the sealed controller runtime")
    runtime_files = runtime_inventory.get("files")
    if not isinstance(runtime_files, Mapping) or (
        runtime_files.get(runtime_relative) != runtime.get("sha256")
    ):
        _fail("Lean verifier executable is not bound by the runtime inventory")
    if receipt.get("snapshot_inventory_sha256") != snapshot.get("files_sha256"):
        _fail("Lean verifier receipt snapshot inventory is stale")
    scope_ids = seal["freeze_scope"]["ids"]
    if receipt.get("scope_ids") != scope_ids:
        _fail("Lean verifier receipt scope differs from controller freeze scope")
    records = receipt.get("records")
    if not isinstance(records, list) or len(records) != len(scope_ids):
        _fail("Lean verifier receipt record count differs from freeze scope")
    seen: set[str] = set()
    for row in records:
        if not isinstance(row, dict):
            _fail("Lean verifier receipt record must be an object")
        _strict_fields(row, _VERIFIER_RECORD_FIELDS, label="Lean verifier record")
        record_id = _require_nonempty_string(row.get("id"), field="Lean verifier record id")
        if record_id in seen or record_id not in scope_ids:
            _fail(f"Lean verifier receipt has duplicate/unscoped record: {record_id}")
        seen.add(record_id)
        for field in (
            "target_sha256", "candidate_sha256", "source_contract_sha256",
            "result_contracts_sha256",
        ):
            _require_sha256(row.get(field), field=f"Lean verifier {record_id}.{field}")
        checks = row.get("checks")
        if not isinstance(checks, list) or len(checks) != 2:
            _fail(f"Lean verifier {record_id} must have two result-contract checks")
        roles: set[str] = set()
        for check in checks:
            if not isinstance(check, dict):
                _fail(f"Lean verifier {record_id} check must be an object")
            _strict_fields(check, _VERIFIER_CHECK_FIELDS, label="Lean verifier check")
            role = str(check.get("role") or "")
            roles.add(role)
            if check.get("compiled") is not True:
                _fail(f"Lean verifier {record_id} has an uncompiled result contract")
            axioms = check.get("axioms")
            if not isinstance(axioms, list) or not set(axioms).issubset(
                {"propext", "Classical.choice", "Quot.sound"}
            ):
                _fail(f"Lean verifier {record_id} has non-standard axioms")
            for field in ("normalized_type_sha256", "result_payload_sha256"):
                _require_sha256(check.get(field), field=f"Lean verifier check.{field}")
        if roles != {"raw_result", "reported_result"}:
            _fail(f"Lean verifier {record_id} result roles are incomplete")
    if seen != set(scope_ids):
        _fail("Lean verifier receipt is missing scoped record(s)")
    _require_sha256(receipt.get("stdout_sha256"), field="Lean verifier stdout_sha256")
    _require_sha256(receipt.get("stderr_sha256"), field="Lean verifier stderr_sha256")


def _load_and_validate_verifier_invocation(
    *, project: Path, seal: Mapping[str, Any]
) -> tuple[dict[str, Any], bytes, dict[str, Any], bytes]:
    wrapper_path, wrapper, wrapper_payload = _load_bound_external_receipt(
        project=project,
        spec=seal.get("verifier_receipt"),
        label="Lean verifier invocation receipt",
    )
    _strict_fields(
        wrapper, _VERIFIER_INVOCATION_FIELDS,
        label="Lean verifier invocation receipt",
    )
    if (
        wrapper.get("schema_version") != 1
        or wrapper.get("protocol") != PROTOCOL
        or wrapper.get("phase") != "lean_verifier_invocation"
        or wrapper.get("exit_code") != 0
        or wrapper.get("solver_stopped") is not True
        or wrapper.get("descendants_stopped") is not True
        or wrapper.get("network_answer_blind") is not False
    ):
        _fail("Lean verifier invocation receipt is not a passing confined run")
    uid = wrapper.get("verifier_uid")
    if not isinstance(uid, int) or isinstance(uid, bool) or uid == 0:
        _fail("Lean verifier invocation UID must be non-root")
    _validate_dedicated_uid_quiescence(
        wrapper.get("dedicated_uid_quiescence"), expected_uid=uid
    )
    for field, seal_key in (
        ("dependency_inventory_sha256", "dependency_inventory"),
        ("runtime_inventory_sha256", "runtime_inventory"),
        ("snapshot_inventory_sha256", "snapshot_inventory"),
    ):
        inventory = seal.get(seal_key)
        if not isinstance(inventory, Mapping) or (
            wrapper.get(field) != inventory.get("files_sha256")
        ):
            _fail(f"Lean verifier invocation {field} is stale")
    verifier_snapshot_root, _verifier_snapshot_files = _validate_verifier_snapshot(
        seal, project=project
    )
    if wrapper.get("snapshot_root") != str(verifier_snapshot_root):
        _fail("Lean verifier invocation snapshot_root is stale")
    argv = wrapper.get("command_argv")
    if not isinstance(argv, list) or not argv or any(
        not isinstance(item, str) or not item for item in argv
    ):
        _fail("Lean verifier invocation command_argv is invalid")
    runtime = seal.get("runtime_inventory")
    dependency = seal.get("dependency_inventory")
    if not isinstance(runtime, Mapping) or not isinstance(dependency, Mapping):
        _fail("Lean verifier invocation lacks sealed runtime/dependency bindings")
    runtime_root = Path(str(runtime.get("root") or "")).resolve()
    runtime_files = runtime.get("files")
    command_path = Path(argv[0])
    try:
        command_relative = command_path.resolve(strict=True).relative_to(
            runtime_root
        ).as_posix()
    except (OSError, ValueError):
        _fail("Lean verifier command is outside the sealed runtime")
    if (
        not isinstance(runtime_files, Mapping)
        or runtime_files.get(command_relative)
        != _sha256_bytes(_read_plain_bytes(command_path, label="Lean verifier command"))
    ):
        _fail("Lean verifier command is absent or drifted from the runtime inventory")
    expected_core = [
        argv[0], "blind-verify-lean", "--project", str(verifier_snapshot_root),
        "--candidate-dir", "blind_candidates",
    ]
    if argv[: len(expected_core)] != expected_core:
        _fail("Lean verifier invocation core command arguments are stale")
    option_pairs = argv[2:]
    if len(option_pairs) % 2:
        _fail("Lean verifier invocation arguments are not option/value pairs")
    allowed_options = {
        "--project", "--candidate-dir", "--output", "--runtime-executable",
        "--runtime-root", "--dependency-root",
        "--expected-dependency-inventory-sha256",
        "--expected-runtime-inventory-sha256",
        "--expected-snapshot-inventory-sha256", "--timeout-s", "--scope-id",
    }
    parsed: dict[str, list[str]] = {}
    for index in range(0, len(option_pairs), 2):
        option, value = option_pairs[index : index + 2]
        if option not in allowed_options or not value:
            _fail("Lean verifier invocation contains an unsupported argument")
        parsed.setdefault(option, []).append(value)
    for option in allowed_options - {"--scope-id"}:
        if len(parsed.get(option, [])) != 1:
            _fail(f"Lean verifier invocation {option} must occur exactly once")
    if parsed.get("--project") != [str(verifier_snapshot_root)] or (
        parsed.get("--candidate-dir") != ["blind_candidates"]
    ):
        _fail("Lean verifier invocation snapshot/candidate arguments are stale")
    raw_output = Path(parsed["--output"][0])
    if not raw_output.is_absolute():
        _fail("Lean verifier raw receipt output must be absolute")
    try:
        timeout_value = int(parsed["--timeout-s"][0])
    except ValueError:
        _fail("Lean verifier timeout argument is invalid")
    if timeout_value < 1:
        _fail("Lean verifier timeout argument must be positive")
    singleton_options = {
        "--runtime-root": str(runtime_root),
        "--dependency-root": str(Path(str(dependency.get("root") or "")).resolve()),
        "--expected-dependency-inventory-sha256": str(
            dependency.get("files_sha256") or ""
        ),
        "--expected-runtime-inventory-sha256": str(
            runtime.get("files_sha256") or ""
        ),
        "--expected-snapshot-inventory-sha256": str(
            seal.get("snapshot_inventory", {}).get("files_sha256") or ""
        ),
    }
    for option, expected_value in singleton_options.items():
        if parsed.get(option) != [expected_value]:
            _fail(f"Lean verifier invocation {option} is missing or stale")
    scope_values = parsed.get("--scope-id", [])
    if scope_values != seal.get("freeze_scope", {}).get("ids"):
        _fail("Lean verifier invocation scope arguments are stale")
    log = wrapper.get("stdout_log")
    if not isinstance(log, Mapping):
        _fail("Lean verifier invocation stdout_log is missing")
    _strict_fields(log, _STDOUT_LOG_FIELDS, label="Lean verifier invocation stdout_log")
    raw_log = log.get("path")
    if not isinstance(raw_log, str) or not Path(raw_log).is_absolute():
        _fail("Lean verifier invocation stdout log path must be absolute")
    log_path = _outside_project(Path(raw_log), project, label="Lean verifier stdout log")
    _require_controller_owned_readonly(log_path, label="Lean verifier stdout log")
    log_payload = _read_plain_bytes(log_path, label="Lean verifier stdout log")
    if (
        log.get("size") != len(log_payload)
        or log.get("sha256") != _sha256_bytes(log_payload)
    ):
        _fail("Lean verifier invocation stdout log hash/size drift")
    _result_path, result, result_payload = _load_bound_external_receipt(
        project=project,
        spec=wrapper.get("verifier_receipt"),
        label="Lean verifier result receipt",
    )
    if result.get("verifier_uid") != uid:
        _fail("Lean verifier result UID disagrees with confined invocation")
    result_runtime = result.get("runtime_executable")
    if not isinstance(result_runtime, Mapping) or parsed.get(
        "--runtime-executable"
    ) != [result_runtime.get("path")]:
        _fail("Lean verifier runtime-executable argument is stale")
    _validate_verifier_receipt(result, seal=seal)
    return wrapper, wrapper_payload, result, result_payload


def _load_review_input_inventory(
    *, project: Path, attempt: Mapping[str, Any], label: str, source_first: bool
) -> tuple[Path, dict[str, str]]:
    raw_inventory = attempt.get("input_inventory")
    if not isinstance(raw_inventory, Mapping):
        _fail(f"{label} input inventory is missing")
    _strict_fields(raw_inventory, _DEPENDENCY_INVENTORY_FIELDS, label=f"{label} input inventory")
    raw_root = raw_inventory.get("root")
    if not isinstance(raw_root, str) or not Path(raw_root).is_absolute():
        _fail(f"{label} input root must be absolute")
    review_root = _outside_project(Path(raw_root), project, label=f"{label} input root")
    _require_controller_owned_readonly(review_root, label=f"{label} input root")
    expected_files = _validated_hash_map(
        raw_inventory.get("files"), label=f"{label} input files"
    )
    if raw_inventory.get("files_sha256") != _hash_index(expected_files):
        _fail(f"{label} input inventory digest is invalid")
    actual_files = _regular_file_inventory(review_root, label=f"{label} sanitized input")
    if actual_files != expected_files:
        _fail(f"{label} sanitized input inventory drift")
    forbidden_parts = {
        "formalization-review-gate.json", "proof-review-gate.json",
        "proof-journal", "logs", "task_results", "iter", "preflight",
    }
    for relative in actual_files:
        path = Path(relative)
        if set(path.parts) & forbidden_parts:
            _fail(f"{label} input contains solver gate/state material")
        if source_first and (
            path.suffix == ".lean"
            or "blind_candidates" in path.parts
            or "blueprint" in path.parts
            or relative == _SOURCE_COMMITMENT_INPUT
            or not (
                (path.parts and path.parts[0] == _SOURCE_FIRST_RECORD_DIRECTORY)
                or path.parts[:2] == ("icho_2026_source", "image")
            )
        ):
            _fail(
                "source-first Review input may contain only problem/source/image material"
            )
    return review_root, actual_files


def _source_first_allowed_locators(
    source_projection: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return the exact source locators accepted for one source projection."""
    locators = [
        f"source.{field}"
        for field in ("current_question", "shared_context", "previous_parts")
        if field in source_projection
    ]
    images = source_projection.get("images")
    if not isinstance(images, list) or not images:
        _fail("source-first locator contract requires problem images")
    for raw_path in images:
        if not isinstance(raw_path, str) or not raw_path:
            _fail("source-first locator contract has an invalid image path")
        locator = f"image:{raw_path}"
        if locator not in locators:
            locators.append(locator)
    return tuple(locators)


def _structured_source_locator_contract(
    projection: Mapping[str, Any],
) -> dict[str, tuple[str, ...]]:
    """Rebuild the per-record locator enum from the sealed source projection."""
    if projection.get("phase") != "structured_source_first_review":
        _fail("source locator contract requires a source-first projection")
    scope_ids = _strict_id_list(
        projection.get("scope_ids"), label="source locator contract scope"
    )
    raw_files = projection.get("files")
    if not isinstance(raw_files, list):
        _fail("source locator contract projection files are missing")
    files: dict[str, Mapping[str, Any]] = {}
    for item in raw_files:
        if not isinstance(item, Mapping):
            _fail("source locator contract projection file is invalid")
        path = item.get("path")
        if not isinstance(path, str) or not path or path in files:
            _fail("source locator contract projection path is invalid")
        files[path] = item
    contract: dict[str, tuple[str, ...]] = {}
    for record_id in scope_ids:
        relative = f"{_SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        item = files.get(relative)
        if (
            not isinstance(item, Mapping)
            or item.get("kind") != "text"
            or not isinstance(item.get("text"), str)
        ):
            _fail(f"source locator contract lacks source record {record_id}")
        source_projection = _strict_json_object(
            str(item["text"]).encode("utf-8"),
            label=f"source locator contract record {record_id}",
        )
        if source_projection.get("id") != record_id:
            _fail("source locator contract record ID is stale")
        locators = _source_first_allowed_locators(source_projection)
        for locator in locators:
            if not locator.startswith("image:"):
                continue
            image_path = (
                f"icho_2026_source/image/{locator.removeprefix('image:')}"
            )
            image = files.get(image_path)
            if not isinstance(image, Mapping) or image.get("kind") != "image":
                _fail(
                    f"source locator contract image is not attached for {record_id}"
                )
        contract[record_id] = locators
    return contract


def _structured_review_response_schema(*, source_first: bool) -> dict[str, Any]:
    """Full strict schema for only the model-owned Review judgments."""
    text = {"type": "string", "minLength": 1, "maxLength": 4096}

    def exact(properties: Mapping[str, Any]) -> dict[str, Any]:
        return {
            "type": "object", "properties": dict(properties),
            "required": sorted(properties), "additionalProperties": False,
        }

    audit = exact({
        "status": {"type": "string", "minLength": 1}, "evidence": text,
    })
    underdetermined = exact({
        "kind": {"type": "string"},
        "status": {"type": "string", "const": "underdetermined"},
        "reason": text,
        "remaining_constraints": {
            "type": "array", "items": text, "minItems": 1, "maxItems": 128,
        },
    })
    numeric = exact({
        "kind": {"type": "string", "const": "numeric"},
        "status": {"type": "string", "const": "derived"},
        "raw_expression": text, "raw_value": text,
        "certified_interval": exact({"lower": text, "upper": text}),
        "reported_value": text, "reporting_quantum": text, "tie_rule": text,
    })
    integer = exact({
        "kind": {"type": "string", "const": "integer"},
        "status": {"type": "string", "const": "derived"},
        "value": text, "proposition": text,
        "constraints": {"type": "array", "items": text, "minItems": 1},
    })
    symbolic = exact({
        "kind": {"type": "string", "enum": ["formula", "classification"]},
        "status": {"type": "string", "const": "derived"},
        "normalized_result": text, "proposition": text,
        "constraints": {"type": "array", "items": text, "minItems": 1},
    })
    finite_set = exact({
        "kind": {"type": "string", "const": "finite_set"},
        "status": {"type": "string", "const": "derived"},
        "normalized_members": {
            "type": "array", "items": text, "minItems": 1,
        },
        "proposition": text,
        "constraints": {"type": "array", "items": text, "minItems": 1},
    })
    result_spec = {
        "anyOf": [numeric, integer, symbolic, finite_set, underdetermined]
    }
    given = exact({"id": text, "source_locator": text, "fact": text})
    step = exact({
        "id": text, "claim": text,
        "depends_on": {
            "type": "array", "items": text, "minItems": 1,
        },
        "justification": text,
    })
    output = exact({
        "id": text,
        "derivation_step_ids": {
            "type": "array", "items": text, "minItems": 1,
        },
        "result_spec": result_spec,
    })
    if source_first:
        record = exact({
            "id": text, "status": {"type": "string", "const": "passed"},
            "givens": {"type": "array", "items": given, "minItems": 1},
            "derivation_steps": {
                "type": "array", "items": step, "minItems": 1,
            },
            "output_commitments": {
                "type": "array", "items": output, "minItems": 1,
            },
        })
    else:
        formal_checks = exact({name: audit for name in _FORMAL_REVIEW_CHECKS})
        bridge = exact({
            "claim": text, "carrier": text, "status": text, "evidence": text,
        })
        blind_checks = exact({
            name: audit for name in (
                "answer_independence", "raw_derivation", "reporting_rule_source",
                "tolerance_provenance", "candidate_domain_provenance",
                "lean_result_binding",
            )
        })
        contract_checks = exact({
            name: audit for name in (
                "statement_scope", "hypothesis_derivability",
                "conclusion_alignment", "bridge_completeness",
            )
        })
        chemistry_checks = exact({
            name: audit for name in (
                "chemical_semantics", "formula_mass_consistency",
                "staged_species_domain",
                "conservation_laws", "units_dimensions", "numerical_reporting",
                "structure_stereochemistry", "identification_uniqueness",
                "answer_smuggling",
            )
        })
        requested_review = exact({
            "lean_carrier": text, "status": text, "evidence": text,
        })
        conflict = exact({
            "source_claim": text, "blueprint_or_lean_claim": text,
            "status": text, "evidence": text,
        })
        image_review = exact({
            "inspected": {"type": "boolean"}, "evidence": text,
        })
        blind_review = exact({
            "blind_source_audit": blind_checks,
            "contract_audit": contract_checks,
            "requested_outputs": {
                "type": "array", "items": requested_review, "minItems": 1,
            },
            "blueprint_conflicts": {"type": "array", "items": conflict},
            "image_audit": {"type": "array", "items": image_review, "minItems": 1},
            "chemistry_checks": chemistry_checks,
        })
        formalization = exact({
            "checks": formal_checks,
            "bridge_obligations": {
                "type": "array", "items": bridge, "minItems": 1,
            },
            "blind_review": blind_review,
        })
        proof = exact({
            "proof_review_route": text, "reason": text,
            "evidence": text,
            "redraft_kind": {"type": "string"}, "blind_review": blind_review,
        })
        record = exact({
            "id": text,
            "source_alignment": exact({
                "status": {"type": "string", "const": "passed"},
                "evidence": text,
            }),
            "formalization": formalization,
            "proof": proof,
        })
    return exact({
        "records": {"type": "array", "items": record, "minItems": 1},
    })


def _structured_review_projection(
    *, root: Path, files: Mapping[str, str], scope_ids: Sequence[str],
    source_first: bool, source_records_sha256: str | None,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    gpt_images: list[dict[str, Any]] = []
    kimi_images: list[dict[str, Any]] = []
    for relative, digest in sorted(files.items()):
        path = root / relative
        payload = _read_plain_bytes(path, label="structured Review input")
        if _sha256_bytes(payload) != digest:
            _fail(f"structured Review input hash drift: {relative}")
        mime = {
            ".png": "image/png", ".jpg": "image/jpeg",
            ".jpeg": "image/jpeg", ".webp": "image/webp",
        }.get(path.suffix.lower())
        if mime is not None:
            encoded = base64.b64encode(payload).decode("ascii")
            records.append({
                "path": relative, "sha256": digest, "kind": "image",
                "media_type": mime,
            })
            gpt_images.append({
                "type": "input_image", "image_url": f"data:{mime};base64,{encoded}",
            })
            kimi_images.append({
                "type": "image",
                "source": {"type": "base64", "media_type": mime, "data": encoded},
            })
            continue
        if path.suffix.lower() == ".pdf":
            records.append({
                "path": relative, "sha256": digest, "kind": "binary_source_asset",
            })
            continue
        try:
            text = payload.decode("utf-8", errors="strict")
        except UnicodeDecodeError:
            records.append({
                "path": relative, "sha256": digest, "kind": "binary_bound_artifact",
            })
            continue
        records.append({
            "path": relative, "sha256": digest, "kind": "text", "text": text,
        })
    projection: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": (
            "structured_source_first_review"
            if source_first else "structured_artifact_review"
        ),
        "scope_ids": list(scope_ids),
        "input_inventory_sha256": _hash_index(files),
        "files": records,
    }
    if not source_first:
        projection["source_records_sha256"] = _require_sha256(
            source_records_sha256, field="structured Review source records"
        )
    return projection, gpt_images, kimi_images


def _structured_review_prompt(
    *, projection: Mapping[str, Any], source_first: bool,
) -> str:
    phase = "source-first derivation" if source_first else "artifact comparison"
    locator_instruction = ""
    if source_first:
        locator_contract = _structured_source_locator_contract(projection)
        locator_instruction = (
            " For every givens[].source_locator, copy exactly one whole string "
            "from source_locator_contract for that record ID. Never append page, "
            "item, range, or explanatory text and never invent another locator. "
            "General laws and reasoning belong in derivation_steps[].justification, "
            "not in source_locator. Treat reporting_policy, measurement_policy, "
            "and candidate_domain_policy only as controller policies; never turn "
            "them into givens or source locators. For a derived numeric result, "
            "raw_value, certified_interval.lower, certified_interval.upper, "
            "reported_value, and reporting_quantum must each be a unit-free exact "
            "numeric string: use only an ASCII finite decimal/scientific numeral "
            "or a canonical reduced n/d with positive denominator. Never include "
            "a unit, Unicode multiplication sign, comma, or prose in those five "
            "fields; the controller supplies the requested output unit. Do not "
            "use a degenerate interval, even when raw_value is exact: always "
            "satisfy certified_interval.lower < raw_value < "
            "certified_interval.upper with exact finite bounds, and keep the "
            "whole interval strictly inside the reported_value rounding cell "
            "of width reporting_quantum. Never set both interval bounds equal "
            "to raw_value. In every returned string, avoid the anchoring words "
            "candidate, artifact, Lean, blueprint, official, grader, marking, "
            "rubric, answer key, whatever, post-hoc, post hoc, and posthoc, even "
            "in a disclaimer; "
            "also avoid any phrase that says to accept something as correct. "
            "State the source-grounded reasoning positively instead. Do not "
            "infer a missing time basis, dimension, datum, or physical condition "
            "from the requested output, unit, or reporting policy. If the supplied "
            "source is insufficient to derive the requested result, return an "
            "underdetermined result_spec instead of adding an assumption. Use "
            "that branch only for a genuinely missing source constraint: keep "
            "kind exactly equal to the requested kind, set status to "
            "underdetermined, include exactly reason and remaining_constraints "
            "besides kind/status, name the missing data or conditions, and do not "
            "invent raw, interval, reported, proposition, or answer values.\n"
            "source_locator_contract="
            + json.dumps(
                locator_contract, ensure_ascii=False, sort_keys=True,
                separators=(",", ":"),
            )
        )
    return (
        f"Perform the independent answer-blind {phase}. Use only the supplied "
        "controller projection. Return exactly one JSON object matching the "
        "pinned response schema. Never use an official answer, grader, marking "
        "scheme, candidate-derived target for Pass A, tools, filesystem access, "
        "or network retrieval."
        + locator_instruction
        + "\nreview_projection="
        + json.dumps(
            projection, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        )
    )


def _structured_review_request(
    *, variant: str, model_id: str, projection: Mapping[str, Any],
    gpt_images: Sequence[Mapping[str, Any]],
    kimi_images: Sequence[Mapping[str, Any]], source_first: bool,
) -> dict[str, Any]:
    prompt = _structured_review_prompt(
        projection=projection, source_first=source_first
    )
    schema = _structured_review_response_schema(source_first=source_first)
    if variant == "gpt":
        return {
            "model": model_id, "store": False, "tools": [],
            "tool_choice": "none", "stream": True,
            "reasoning": {"effort": "max", "summary": "auto"},
            "input": [{
                "role": "user",
                "content": [{"type": "input_text", "text": prompt}, *gpt_images],
            }],
            "text": {"format": {
                "type": "json_schema",
                "name": (
                    "answer_blind_source_first_review"
                    if source_first else "answer_blind_artifact_review"
                ),
                "strict": True, "schema": schema,
            }},
        }
    if variant == "kimi-k3":
        return {
            "model": model_id, "tools": [], "max_tokens": 131072,
            "messages": [{
                "role": "user",
                "content": [{"type": "text", "text": prompt}, *kimi_images],
            }],
        }
    _fail(f"unsupported structured Review variant: {variant}")


def _structured_json_from_provider_response(
    response: Mapping[str, Any], *, variant: str, label: str,
) -> dict[str, Any]:
    texts: list[str] = []
    if variant == "gpt":
        output = response.get("output")
        if isinstance(output, list):
            for item in output:
                if not isinstance(item, Mapping) or not isinstance(item.get("content"), list):
                    continue
                texts.extend(
                    block["text"]
                    for block in item["content"]
                    if isinstance(block, Mapping)
                    and block.get("type") in {"output_text", "text"}
                    and isinstance(block.get("text"), str)
                )
    else:
        content = response.get("content")
        if isinstance(content, list):
            texts = [
                block["text"] for block in content
                if isinstance(block, Mapping) and block.get("type") == "text"
                and isinstance(block.get("text"), str)
            ]
    if len(texts) != 1:
        _fail(f"{label} provider response must contain exactly one JSON text block")
    return _strict_json_object(texts[0].encode("utf-8"), label=f"{label} response text")


def _model_blind_review_view(value: object, *, label: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        _fail(f"{label} blind Review certificate is missing")
    result = {
        field: value.get(field)
        for field in (
            "blind_source_audit", "contract_audit", "blueprint_conflicts",
            "chemistry_checks",
        )
    }
    requested = value.get("requested_outputs")
    if not isinstance(requested, list):
        _fail(f"{label} requested_outputs is missing")
    result["requested_outputs"] = [
        {
            "lean_carrier": item.get("lean_carrier"),
            "status": item.get("status"), "evidence": item.get("evidence"),
        }
        for item in requested if isinstance(item, Mapping)
    ]
    if len(result["requested_outputs"]) != len(requested):
        _fail(f"{label} requested_outputs contains an invalid item")
    images = value.get("image_audit")
    if not isinstance(images, list):
        _fail(f"{label} image_audit is missing")
    result["image_audit"] = [
        {
            "inspected": item.get("inspected"), "evidence": item.get("evidence"),
        }
        for item in images
        if isinstance(item, Mapping)
    ]
    if len(result["image_audit"]) != len(images):
        _fail(f"{label} image_audit contains an invalid item")
    return result


def _minimal_review_submission_from_semantic(
    semantic: Mapping[str, Any], *, source_first: bool,
) -> dict[str, Any]:
    records = semantic.get("records")
    if not isinstance(records, list):
        _fail("constructed Review semantic receipt has no records")
    projected: list[dict[str, Any]] = []
    for row in records:
        if not isinstance(row, Mapping):
            _fail("constructed Review semantic record is invalid")
        if source_first:
            outputs = row.get("output_commitments")
            if not isinstance(outputs, list):
                _fail("constructed source-first receipt lacks output commitments")
            projected.append({
                "id": row.get("id"), "status": row.get("status"),
                "givens": row.get("givens"),
                "derivation_steps": row.get("derivation_steps"),
                "output_commitments": [
                    {
                        "id": output.get("id"),
                        "derivation_step_ids": output.get("derivation_step_ids"),
                        "result_spec": output.get("result_spec"),
                    }
                    for output in outputs if isinstance(output, Mapping)
                ],
            })
            if len(projected[-1]["output_commitments"]) != len(outputs):
                _fail("constructed source-first output commitment is invalid")
            continue
        formal = row.get("formalization_certificate")
        proof = row.get("proof_certificate")
        if not isinstance(formal, Mapping) or not isinstance(proof, Mapping):
            _fail("constructed artifact Review lacks formal/proof certificates")
        projected.append({
            "id": row.get("id"),
            "source_alignment": row.get("source_alignment"),
            "formalization": {
                "checks": formal.get("checks"),
                "bridge_obligations": formal.get("bridge_obligations"),
                "blind_review": _model_blind_review_view(
                    formal.get("blind_review_certificate"), label="formalization"
                ),
            },
            "proof": {
                "proof_review_route": proof.get("proof_review_route"),
                "reason": proof.get("reason"),
                "evidence": proof.get("evidence"),
                "redraft_kind": proof.get("redraft_kind"),
                "blind_review": _model_blind_review_view(
                    proof.get("blind_review_certificate"), label="proof"
                ),
            },
        })
    return {"records": projected}


def _load_source_first_precommit(
    *, project: Path, seal: Mapping[str, Any],
) -> tuple[Path, dict[str, Any], bytes, dict[str, str]]:
    """Verify the immutable source-only model exchange created before solve."""
    path, precommit, payload = _load_bound_external_receipt(
        project=project, spec=seal.get("source_first_precommit"),
        label="source-first pre-solver commitment",
    )
    if path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail("source-first pre-solver commitment must be mode 0400")
    _strict_fields(
        precommit, _STRUCTURED_SOURCE_PRECOMMIT_FIELDS,
        label="source-first pre-solver commitment",
    )
    solver = seal.get("solver")
    scope = seal.get("freeze_scope")
    runtime = seal.get("runtime_inventory")
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3"),
    }.get(precommit.get("variant"))
    if (
        precommit.get("schema_version") != SCHEMA_VERSION
        or precommit.get("protocol") != PROTOCOL
        or precommit.get("phase") != "structured_source_first_precommit"
        or precommit.get("request_profile") != _STRUCTURED_REVIEW_PROFILE
        or precommit.get("tools_enabled") is not False
        or precommit.get("store") is not False
        or precommit.get("status") != "accepted"
        or precommit.get("finalized_before_solver") is not True
        or not isinstance(solver, Mapping)
        or any(precommit.get(field) != solver.get(field) for field in _SOLVER_FIELDS)
        or expected_identity
        != (precommit.get("model_family"), precommit.get("model_id"))
        or not isinstance(scope, Mapping)
        or precommit.get("scope_ids") != scope.get("ids")
        or not isinstance(runtime, Mapping)
    ):
        _fail("source-first pre-solver commitment metadata/scope is stale")
    controller_sha = _require_sha256(
        precommit.get("controller_binary_sha256"),
        field="source-first precommit controller_binary_sha256",
    )
    runtime_files = runtime.get("files")
    if not isinstance(runtime_files, Mapping) or controller_sha not in set(
        runtime_files.values()
    ):
        _fail("source-first precommit controller is absent from runtime inventory")
    review_root, input_files = _load_review_input_inventory(
        project=project, attempt=precommit,
        label="source-first pre-solver commitment", source_first=True,
    )
    projection, gpt_images, kimi_images = _structured_review_projection(
        root=review_root, files=input_files,
        scope_ids=precommit.get("scope_ids") or [], source_first=True,
        source_records_sha256=None,
    )
    projection_sha = _sha256_bytes(_json_bytes(projection))
    if precommit.get("review_projection_sha256") != projection_sha:
        _fail("source-first pre-solver projection hash is stale")
    schema_sha = _sha256_bytes(
        _json_bytes(_structured_review_response_schema(source_first=True))
    )
    adapter_provenance = precommit.get("adapter_provenance")
    if not isinstance(adapter_provenance, Mapping):
        _fail("source-first precommit adapter provenance is missing")
    _strict_fields(
        adapter_provenance, _STRUCTURED_REVIEW_ADAPTER_FIELDS,
        label="source-first precommit adapter provenance",
    )
    expected_adapter = {
        "gpt": ("openai_responses_v1", "openai_responses_single_json_text_v1"),
        "kimi-k3": (
            "anthropic_messages_v1", "anthropic_messages_single_json_text_v1",
        ),
    }.get(precommit.get("variant"))
    if (
        expected_adapter is None
        or (
            adapter_provenance.get("provider_api"),
            adapter_provenance.get("response_extractor"),
        ) != expected_adapter
        or adapter_provenance.get("response_schema_sha256") != schema_sha
    ):
        _fail("source-first precommit adapter/schema provenance is stale")
    request_path, request, request_payload = _load_bound_external_receipt(
        project=project, spec=precommit.get("request"),
        label="source-first precommit model request",
        max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
    )
    expected_request = _structured_review_request(
        variant=str(precommit["variant"]), model_id=str(precommit["model_id"]),
        projection=projection, gpt_images=gpt_images, kimi_images=kimi_images,
        source_first=True,
    )
    if request != expected_request or request_payload != _json_bytes(expected_request):
        _fail("source-first precommit request is not the canonical source-only prompt")
    response_path, response, response_payload = _load_bound_external_receipt(
        project=project, spec=precommit.get("response"),
        label="source-first precommit provider response",
        max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
    )
    normalized = _structured_json_from_provider_response(
        response, variant=str(precommit["variant"]),
        label="source-first precommit",
    )
    model_path, model_submission, model_payload = _load_bound_external_receipt(
        project=project, spec=precommit.get("model_submission"),
        label="source-first precommit model submission",
    )
    if (
        model_submission != normalized or model_payload != _json_bytes(normalized)
        or precommit.get("normalized_response_sha256")
        != _sha256_bytes(model_payload)
    ):
        _fail("source-first precommit model submission is not response-derived")
    for artifact_path in (request_path, response_path, model_path):
        if artifact_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
            _fail("source-first precommit model artifacts must be mode 0400")
    transport = precommit.get("transport")
    if not isinstance(transport, Mapping):
        _fail("source-first precommit transport is missing")
    if precommit.get("variant") == "kimi-k3":
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_KIMI_FIELDS,
            label="source-first precommit Kimi transport",
        )
        if (
            precommit.get("adapter") != "structured_broker_http_v1"
            or transport.get("kind") != "structured_broker_http_v1"
        ):
            _fail("source-first precommit Kimi transport is stale")
        _ready, _ready_sha, transcript, _transcript_sha = (
            _load_and_validate_model_broker_binding(
                project=project,
                binding={
                    "ready_receipt": transport.get("ready_receipt"),
                    "transcript": transport.get("transcript"),
                },
                variant="kimi-k3", run_id=precommit.get("run_id"),
                model_id=precommit.get("model_id"), runtime=runtime,
                minimum_requests=1, exact_requests=1,
                request_profile=_STRUCTURED_REVIEW_PROFILE,
                label="source-first precommit model_broker",
            )
        )
        if precommit.get("request_response_chain_sha256") != transcript.get(
            "request_response_chain_sha256"
        ):
            _fail("source-first precommit Kimi request chain is stale")
    else:
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_GPT_FIELDS,
            label="source-first precommit GPT transport",
        )
        exchanges = transport.get("exchanges")
        if (
            precommit.get("adapter") != "chatgpt_login_proxy_v1"
            or transport.get("kind") != "chatgpt_login_proxy_v1"
            or not isinstance(exchanges, list) or len(exchanges) != 1
            or not isinstance(exchanges[0], Mapping)
        ):
            _fail("source-first precommit GPT transport is stale")
        exchange_sha = _require_sha256(
            exchanges[0].get("sha256"), field="source-first GPT exchange sha256"
        )
        exchange_chain = _sha256_bytes(
            bytes.fromhex("0" * 64) + bytes.fromhex(exchange_sha)
        )
        if (
            transport.get("exchange_chain_sha256") != exchange_chain
            or precommit.get("request_response_chain_sha256") != exchange_chain
        ):
            _fail("source-first precommit GPT exchange chain is stale")
        _exchange_path, exchange, _exchange_payload = _load_bound_external_receipt(
            project=project, spec=exchanges[0],
            label="source-first precommit GPT exchange",
        )
        synthetic_attempt = {
            "adapter": "chatgpt_login_proxy_v1",
            "adapter_provenance": {
                "proxy_receipt": dict(exchanges[0]),
                "normalized_response_sha256": (
                    exchange.get("normalized_response", {}).get("sha256")
                    if isinstance(exchange.get("normalized_response"), Mapping) else None
                ),
                "upstream_raw_sse_sha256": (
                    exchange.get("upstream_raw_sse", {}).get("sha256")
                    if isinstance(exchange.get("upstream_raw_sse"), Mapping) else None
                ),
                "event_count": _sealed_codex_jsonl_event_count(
                    project=project, exchange=exchange,
                    label="source-first precommit GPT exchange",
                ),
            },
            "status": "accepted", "target_id": "independent-source-first-review",
            "attempt": 1, "request": precommit.get("request"),
        }
        _validate_structured_transport_provenance(
            project=project, runtime=runtime, aggregate=precommit,
            attempt=synthetic_attempt, request_path=request_path,
            request_payload=request_payload, response_path=response_path,
            response_payload=response_payload,
            expected_gpt_exchange=exchanges[0],
            expected_submission=model_submission,
        )
    return path, precommit, payload, input_files


def construct_structured_review_records(
    *,
    source_first: bool,
    model_submission: Mapping[str, Any],
    controller_records: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str],
) -> list[dict[str, Any]]:
    """Build only the deterministic per-target Review records.

    ``controller_records`` is deliberately explicit and hash-only.  Pass A
    records contain the canonical bundle/source projection bindings; Pass B
    records contain the current artifact/source-contract bindings.  The model
    never has to reproduce any digest or controller identity field.  This
    helper intentionally has no snapshot argument, so its output can be used
    to write controller-owned gates before the final clean snapshot is sealed.
    """
    expected_scope = _strict_id_list(list(scope_ids), label="structured Review scope")
    _strict_fields(model_submission, {"records"}, label="structured Review model submission")
    raw_records = model_submission.get("records")
    if not isinstance(raw_records, list) or len(raw_records) != len(expected_scope):
        _fail("structured Review model record count differs from scope")
    model_by_id: dict[str, Mapping[str, Any]] = {}
    for expected_id, raw in zip(expected_scope, raw_records, strict=True):
        if not isinstance(raw, Mapping) or raw.get("id") != expected_id:
            _fail("structured Review model records are not in exact scope order")
        if expected_id in model_by_id:
            _fail("structured Review model submission repeats an ID")
        model_by_id[expected_id] = raw
    if set(controller_records) != set(expected_scope):
        _fail("structured Review controller bindings differ from scope")

    def inject_blind_review(
        view: object, *, binding: Mapping[str, Any], label: str,
    ) -> dict[str, Any]:
        if not isinstance(view, Mapping):
            _fail(f"{label} blind Review verdict is missing")
        _strict_fields(
            view,
            {
                "blind_source_audit", "contract_audit", "requested_outputs",
                "blueprint_conflicts", "image_audit", "chemistry_checks",
            },
            label=f"{label} blind Review verdict",
        )
        requested_source = binding.get("requested_outputs")
        requested_model = view.get("requested_outputs")
        images_source = binding.get("images")
        images_model = view.get("image_audit")
        if (
            not isinstance(requested_source, list)
            or not isinstance(requested_model, list)
            or len(requested_source) != len(requested_model)
        ):
            _fail(f"{label} requested-output verdict coverage is incomplete")
        if (
            not isinstance(images_source, list)
            or not isinstance(images_model, list)
            or len(images_source) != len(images_model)
        ):
            _fail(f"{label} image verdict coverage is incomplete")
        requested: list[dict[str, Any]] = []
        for source, verdict in zip(requested_source, requested_model, strict=True):
            if not isinstance(source, Mapping) or not isinstance(verdict, Mapping):
                _fail(f"{label} requested-output verdict is invalid")
            _strict_fields(
                verdict, {"lean_carrier", "status", "evidence"},
                label=f"{label} requested-output verdict",
            )
            requested.append({
                "source_requirement": source.get("source_requirement"),
                **dict(verdict),
            })
        image_audit: list[dict[str, Any]] = []
        for source, verdict in zip(images_source, images_model, strict=True):
            if not isinstance(source, Mapping) or not isinstance(verdict, Mapping):
                _fail(f"{label} image verdict is invalid")
            _strict_fields(
                verdict, {"inspected", "evidence"},
                label=f"{label} image verdict",
            )
            image_audit.append({
                "path": source.get("path"), "sha256": source.get("sha256"),
                **dict(verdict),
            })
        return {
            "source_contract": binding.get("source_contract"),
            "blind_source_audit": view.get("blind_source_audit"),
            "contract_audit": view.get("contract_audit"),
            "requested_outputs": requested,
            "blueprint_conflicts": view.get("blueprint_conflicts"),
            "image_audit": image_audit,
            "chemistry_checks": view.get("chemistry_checks"),
        }

    constructed: list[dict[str, Any]] = []
    for record_id in expected_scope:
        model_record = model_by_id[record_id]
        binding = controller_records[record_id]
        if source_first:
            _strict_fields(
                binding,
                {
                    "blind_record_sha256", "source_record_sha256",
                    "requested_outputs",
                },
                label=f"source-first controller binding {record_id}",
            )
            _strict_fields(
                model_record,
                {"id", "status", "givens", "derivation_steps", "output_commitments"},
                label=f"source-first model record {record_id}",
            )
            requested = binding.get("requested_outputs")
            model_outputs = model_record.get("output_commitments")
            if (
                not isinstance(requested, list) or not isinstance(model_outputs, list)
                or len(requested) != len(model_outputs)
            ):
                _fail(f"source-first model output coverage is incomplete for {record_id}")
            outputs: list[dict[str, Any]] = []
            for source, verdict in zip(requested, model_outputs, strict=True):
                if not isinstance(source, Mapping) or not isinstance(verdict, Mapping):
                    _fail(f"source-first output commitment is invalid for {record_id}")
                _strict_fields(
                    verdict, {"id", "derivation_step_ids", "result_spec"},
                    label=f"source-first model output {record_id}",
                )
                if verdict.get("id") != source.get("id"):
                    _fail(f"source-first model output order/ID is stale for {record_id}")
                outputs.append({**dict(source), **dict(verdict)})
            constructed.append({
                "id": record_id,
                "blind_record_sha256": binding.get("blind_record_sha256"),
                "source_record_sha256": binding.get("source_record_sha256"),
                "requested_outputs_sha256": _sha256_bytes(_json_bytes(requested)),
                "status": model_record.get("status"),
                "givens": model_record.get("givens"),
                "derivation_steps": model_record.get("derivation_steps"),
                "output_commitments": outputs,
            })
            continue
        _strict_fields(
            binding,
            {
                "target", "target_sha256", "candidate_sha256",
                "source_report_sha256", "blueprint_sha256", "source_contract",
                "requested_outputs", "images", "source_commitment_record_sha256",
            },
            label=f"artifact Review controller binding {record_id}",
        )
        _strict_fields(
            model_record, {"id", "source_alignment", "formalization", "proof"},
            label=f"artifact Review model record {record_id}",
        )
        formal = model_record.get("formalization")
        proof = model_record.get("proof")
        if not isinstance(formal, Mapping) or not isinstance(proof, Mapping):
            _fail(f"artifact Review model certificates are missing for {record_id}")
        _strict_fields(
            formal, {"checks", "bridge_obligations", "blind_review"},
            label=f"artifact formalization verdict {record_id}",
        )
        _strict_fields(
            proof,
            {"proof_review_route", "reason", "evidence", "redraft_kind", "blind_review"},
            label=f"artifact proof verdict {record_id}",
        )
        source_contract = binding.get("source_contract")
        formal_blind = inject_blind_review(
            formal.get("blind_review"), binding=binding,
            label=f"formalization {record_id}",
        )
        proof_blind = inject_blind_review(
            proof.get("blind_review"), binding=binding,
            label=f"proof {record_id}",
        )
        requested = binding.get("requested_outputs")
        constructed.append({
            "id": record_id,
            "target": binding.get("target"),
            "target_sha256": binding.get("target_sha256"),
            "candidate_sha256": binding.get("candidate_sha256"),
            "source_report_sha256": binding.get("source_report_sha256"),
            "blueprint_sha256": binding.get("blueprint_sha256"),
            "source_contract_sha256": _sha256_bytes(_json_bytes(source_contract)),
            "requested_outputs_sha256": _sha256_bytes(_json_bytes(requested)),
            "source_commitment_record_sha256": binding.get(
                "source_commitment_record_sha256"
            ),
            "source_alignment": model_record.get("source_alignment"),
            "formalization_status": "passed",
            "formalization_certificate": {
                "schema_version": 2,
                "checks": formal.get("checks"),
                "bridge_obligations": formal.get("bridge_obligations"),
                "source_contract": source_contract,
                "blind_review_certificate": formal_blind,
            },
            "proof_status": "solved",
            "proof_certificate": {
                "proof_review_schema_version": 1,
                "proof_review_route": proof.get("proof_review_route"),
                "reason": proof.get("reason"),
                "evidence": proof.get("evidence"),
                "redraft_kind": proof.get("redraft_kind"),
                "source_contract": source_contract,
                "blind_review_certificate": proof_blind,
            },
        })
    return constructed


def construct_structured_review_envelope(
    *, source_first: bool, records: Sequence[Mapping[str, Any]],
    scope_ids: Sequence[str], variant: str, model_family: str, model_id: str,
    run_id: str, snapshot_inventory_sha256: str,
    review_input_inventory_sha256: str, review_projection_sha256: str,
    source_first_precommit_sha256: str | None = None,
    source_records_sha256: str | None = None,
) -> dict[str, Any]:
    """Inject final snapshot/run provenance around preconstructed records."""
    expected_scope = _strict_id_list(list(scope_ids), label="structured Review scope")
    normalized_records = [dict(record) for record in records]
    if [record.get("id") for record in normalized_records] != expected_scope:
        _fail("structured Review records are not in exact scope order")
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": (
            "independent_source_first_commitment"
            if source_first else "independent_artifact_review"
        ),
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "variant": variant, "model_family": model_family,
        "model_id": model_id, "run_id": run_id,
        "request_profile": _STRUCTURED_REVIEW_PROFILE,
        "snapshot_inventory_sha256": snapshot_inventory_sha256,
        "review_input_inventory_sha256": review_input_inventory_sha256,
        "review_projection_sha256": review_projection_sha256,
        "scope_ids": expected_scope, "records": normalized_records,
    }
    if source_first:
        result["source_first_precommit_sha256"] = _require_sha256(
            source_first_precommit_sha256,
            field="structured source-first precommit sha256",
        )
        result["source_records_sha256"] = _require_sha256(
            source_records_sha256, field="structured source records sha256"
        )
    else:
        if source_first_precommit_sha256 is not None:
            _fail("artifact Review envelope may not receive a precommit digest")
        result["source_records_sha256"] = _require_sha256(
            source_records_sha256,
            field="structured artifact Review source_records_sha256",
        )
    return result


def construct_structured_source_records_commitment(
    *, model_submission: Mapping[str, Any],
    controller_records: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str], variant: str, model_family: str, model_id: str,
    run_id: str, review_input_inventory_sha256: str,
    review_projection_sha256: str,
) -> dict[str, Any]:
    """Build the immutable Pass-A records artifact consumed by Pass B."""
    expected_scope = _strict_id_list(list(scope_ids), label="structured Review scope")
    records = construct_structured_review_records(
        source_first=True, model_submission=model_submission,
        controller_records=controller_records, scope_ids=expected_scope,
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "independent_source_first_records",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "variant": variant,
        "model_family": model_family,
        "model_id": model_id,
        "run_id": run_id,
        "request_profile": _STRUCTURED_REVIEW_PROFILE,
        "review_input_inventory_sha256": _require_sha256(
            review_input_inventory_sha256,
            field="source records input inventory sha256",
        ),
        "review_projection_sha256": _require_sha256(
            review_projection_sha256, field="source records projection sha256"
        ),
        "scope_ids": expected_scope,
        "records": records,
    }


def construct_structured_review_semantic(
    *, source_first: bool, model_submission: Mapping[str, Any],
    controller_records: Mapping[str, Mapping[str, Any]],
    scope_ids: Sequence[str], variant: str, model_family: str, model_id: str,
    run_id: str, snapshot_inventory_sha256: str,
    review_input_inventory_sha256: str, review_projection_sha256: str,
    source_first_precommit_sha256: str | None = None,
    source_records_sha256: str | None = None,
) -> dict[str, Any]:
    """Convenience composition of record construction and final envelope."""
    records = construct_structured_review_records(
        source_first=source_first, model_submission=model_submission,
        controller_records=controller_records, scope_ids=scope_ids,
    )
    return construct_structured_review_envelope(
        source_first=source_first, records=records, scope_ids=scope_ids,
        variant=variant, model_family=model_family, model_id=model_id,
        run_id=run_id,
        snapshot_inventory_sha256=snapshot_inventory_sha256,
        review_input_inventory_sha256=review_input_inventory_sha256,
        review_projection_sha256=review_projection_sha256,
        source_first_precommit_sha256=source_first_precommit_sha256,
        source_records_sha256=source_records_sha256,
    )


def _load_structured_review_pass(
    *, project: Path, seal: Mapping[str, Any], aggregate: Mapping[str, Any],
    spec: object, expected_fields: set[str], expected_phase: str, label: str,
    source_first: bool, expected_source_records_sha256: str | None,
) -> tuple[
    Path, dict[str, Any], bytes, dict[str, str], dict[str, Any], bytes,
    str, tuple[str, str],
]:
    attempt_path, attempt, attempt_payload = _load_bound_external_receipt(
        project=project, spec=spec, label=f"{label} structured attempt"
    )
    if attempt_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail(f"{label} structured attempt must be mode 0400")
    _strict_fields(attempt, expected_fields, label=f"{label} structured attempt")
    if (
        attempt.get("schema_version") != SCHEMA_VERSION
        or attempt.get("protocol") != PROTOCOL
        or attempt.get("phase") != expected_phase
        or attempt.get("request_profile") != _STRUCTURED_REVIEW_PROFILE
        or attempt.get("tools_enabled") is not False
        or attempt.get("store") is not False
        or attempt.get("status") != "accepted"
        or any(
            attempt.get(field) != aggregate.get(field)
            for field in (
                "variant", "model_family", "model_id", "run_id", "scope_ids",
                "snapshot_inventory_sha256", "controller_binary_sha256",
            )
        )
    ):
        _fail(f"{label} structured attempt provenance/status is stale")
    if source_first:
        precommit_path, precommit, precommit_payload, _precommit_files = (
            _load_source_first_precommit(project=project, seal=seal)
        )
        precommit_spec = attempt.get("source_first_precommit")
        sealed_precommit_spec = seal.get("source_first_precommit")
        if precommit_spec != sealed_precommit_spec:
            _fail("source-first final attempt does not bind the sealed pre-solver exchange")
        for field in _STRUCTURED_SOURCE_PRECOMMIT_FIELDS - {
            "phase", "finalized_before_solver",
        }:
            if attempt.get(field) != precommit.get(field):
                _fail(
                    "source-first final attempt does not byte-reuse its pre-solver "
                    f"{field} binding"
                )
        if (
            not isinstance(precommit_spec, Mapping)
            or Path(str(precommit_spec.get("path") or "")).resolve() != precommit_path
            or precommit_spec.get("sha256") != _sha256_bytes(precommit_payload)
        ):
            _fail("source-first final attempt precommit locator is stale")
    review_root, actual_files = _load_review_input_inventory(
        project=project, attempt=attempt, label=label, source_first=source_first
    )
    projection, gpt_images, kimi_images = _structured_review_projection(
        root=review_root, files=actual_files,
        scope_ids=attempt.get("scope_ids") or [], source_first=source_first,
        source_records_sha256=expected_source_records_sha256,
    )
    projection_sha = _sha256_bytes(_json_bytes(projection))
    if attempt.get("review_projection_sha256") != projection_sha:
        _fail(f"{label} review projection hash is stale")
    schema_sha = _sha256_bytes(_json_bytes(
        _structured_review_response_schema(source_first=source_first)
    ))
    adapter = attempt.get("adapter_provenance")
    if not isinstance(adapter, Mapping):
        _fail(f"{label} adapter_provenance is missing")
    _strict_fields(
        adapter, _STRUCTURED_REVIEW_ADAPTER_FIELDS,
        label=f"{label} adapter_provenance",
    )
    expected_adapter = {
        "gpt": (
            "openai_responses_v1", "openai_responses_single_json_text_v1"
        ),
        "kimi-k3": (
            "anthropic_messages_v1", "anthropic_messages_single_json_text_v1"
        ),
    }.get(attempt.get("variant"))
    if expected_adapter is None or (
        adapter.get("provider_api"), adapter.get("response_extractor")
    ) != expected_adapter or adapter.get("response_schema_sha256") != schema_sha:
        _fail(f"{label} adapter/response-schema provenance is stale")
    request_path, request, request_payload = _load_bound_external_receipt(
        project=project, spec=attempt.get("request"), label=f"{label} model request",
        max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
    )
    expected_request = _structured_review_request(
        variant=str(attempt["variant"]), model_id=str(attempt["model_id"]),
        projection=projection, gpt_images=gpt_images, kimi_images=kimi_images,
        source_first=source_first,
    )
    if request != expected_request or request_payload != _json_bytes(expected_request):
        _fail(f"{label} model request is not the canonical tool-free projection")
    response_path, _unused, response_payload = _load_bound_external_receipt(
        project=project, spec=attempt.get("response"), label=f"{label} provider response",
        max_bytes=_MAX_PROVIDER_RESPONSE_BYTES,
    )
    response = _strict_json_object(response_payload, label=f"{label} provider response")
    normalized = _structured_json_from_provider_response(
        response, variant=str(attempt["variant"]), label=label
    )
    model_path, model_submission, model_payload = _load_bound_external_receipt(
        project=project, spec=attempt.get("model_submission"),
        label=f"{label} model submission",
    )
    semantic_path, semantic, semantic_payload = _load_bound_external_receipt(
        project=project, spec=attempt.get("constructed_semantic_receipt"),
        label=f"{label} constructed semantic receipt",
    )
    for path, field in (
        (request_path, "request"), (response_path, "response"),
        (model_path, "model submission"),
        (semantic_path, "constructed semantic receipt"),
    ):
        if path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
            _fail(f"{label} {field} must be controller-owned mode 0400")
    normalized_payload = _json_bytes(normalized)
    if (
        model_submission != normalized
        or model_payload != normalized_payload
        or attempt.get("normalized_response_sha256")
        != _sha256_bytes(normalized_payload)
    ):
        _fail(f"{label} model submission is not provider-response-derived")
    expected_model_view = _minimal_review_submission_from_semantic(
        semantic, source_first=source_first
    )
    if expected_model_view != model_submission:
        _fail(f"{label} constructed semantic receipt is not deterministic from the model submission")
    runtime = seal.get("runtime_inventory")
    if not isinstance(runtime, Mapping):
        _fail(f"{label} runtime inventory is missing")
    transport = attempt.get("transport")
    if not isinstance(transport, Mapping):
        _fail(f"{label} transport binding is missing")
    if attempt.get("variant") == "kimi-k3":
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_KIMI_FIELDS,
            label=f"{label} Kimi transport",
        )
        if (
            attempt.get("adapter") != "structured_broker_http_v1"
            or transport.get("kind") != "structured_broker_http_v1"
        ):
            _fail(f"{label} Kimi adapter/transport is stale")
        _ready, ready_sha, transcript, transcript_sha = (
            _load_and_validate_model_broker_binding(
                project=project,
                binding={
                    "ready_receipt": transport.get("ready_receipt"),
                    "transcript": transport.get("transcript"),
                },
                variant="kimi-k3", run_id=attempt.get("run_id"),
                model_id=attempt.get("model_id"), runtime=runtime,
                minimum_requests=1, exact_requests=1,
                request_profile=_STRUCTURED_REVIEW_PROFILE,
                label=f"{label} model_broker",
            )
        )
        if attempt.get("request_response_chain_sha256") != transcript.get(
            "request_response_chain_sha256"
        ):
            _fail(f"{label} broker request/response chain is stale")
        transport_evidence = (ready_sha, transcript_sha)
    elif attempt.get("variant") == "gpt":
        _strict_fields(
            transport, _STRUCTURED_TRANSPORT_GPT_FIELDS,
            label=f"{label} GPT transport",
        )
        exchanges = transport.get("exchanges")
        if (
            attempt.get("adapter") != "chatgpt_login_proxy_v1"
            or transport.get("kind") != "chatgpt_login_proxy_v1"
            or not isinstance(exchanges, list) or len(exchanges) != 1
            or not isinstance(exchanges[0], Mapping)
        ):
            _fail(f"{label} GPT adapter/transport is stale")
        exchange_sha = _require_sha256(
            exchanges[0].get("sha256"), field=f"{label} GPT exchange sha256"
        )
        exchange_chain = _sha256_bytes(
            bytes.fromhex("0" * 64) + bytes.fromhex(exchange_sha)
        )
        if (
            transport.get("exchange_chain_sha256") != exchange_chain
            or attempt.get("request_response_chain_sha256") != exchange_chain
        ):
            _fail(f"{label} GPT exchange chain is stale")
        _exchange_path, exchange, _exchange_payload = _load_bound_external_receipt(
            project=project, spec=exchanges[0], label=f"{label} GPT exchange",
        )
        if not isinstance(exchange, Mapping):
            _fail(f"{label} GPT exchange receipt is invalid")
        expected_target_id = (
            "independent-source-first-review"
            if source_first else "independent-artifact-review"
        )
        synthetic_attempt = {
            "adapter": "chatgpt_login_proxy_v1",
            "adapter_provenance": {
                "proxy_receipt": dict(exchanges[0]),
                "normalized_response_sha256": (
                    exchange.get("normalized_response", {}).get("sha256")
                    if isinstance(exchange.get("normalized_response"), Mapping) else None
                ),
                "upstream_raw_sse_sha256": (
                    exchange.get("upstream_raw_sse", {}).get("sha256")
                    if isinstance(exchange.get("upstream_raw_sse"), Mapping) else None
                ),
                "event_count": _sealed_codex_jsonl_event_count(
                    project=project, exchange=exchange, label=f"{label} GPT exchange",
                ),
            },
            "status": "accepted", "target_id": expected_target_id,
            "attempt": 1, "request": attempt.get("request"),
        }
        _validate_structured_transport_provenance(
            project=project, runtime=runtime, aggregate=attempt,
            attempt=synthetic_attempt, request_path=request_path,
            request_payload=request_payload, response_path=response_path,
            response_payload=response_payload,
            expected_gpt_exchange=exchanges[0],
            expected_submission=model_submission,
        )
        transport_evidence = ("chatgpt_login_proxy_v1", exchange_sha)
    else:
        _fail(f"{label} has unsupported transport variant")
    return (
        attempt_path, attempt, attempt_payload, actual_files, semantic,
        semantic_payload, projection_sha, transport_evidence,
    )


_SOURCE_FIRST_ANCHOR_RE = re.compile(
    r"(?i)\b(candidate|artifact|lean|blueprint|official|grader|marking|rubric|"
    r"answer\s*key|whatever|post[ -]?hoc)\b|accept.{0,40}\bcorrect\b"
)


def _source_first_text(value: object, *, field: str) -> str:
    text = _require_nonempty_string(value, field=field)
    if len(text) > 4096:
        _fail(f"{field} exceeds the source-first text limit")
    if _SOURCE_FIRST_ANCHOR_RE.search(text):
        _fail(f"{field} contains candidate/artifact anchoring language")
    return text


def _validate_source_first_result_spec(
    value: object, *, output_kind: object, record_id: str, output_id: str,
) -> None:
    if not isinstance(value, Mapping):
        _fail(f"source-first output {record_id}/{output_id} result_spec is missing")
    kind = str(output_kind or "")
    status = value.get("status")
    if value.get("kind") != kind or status not in {"derived", "underdetermined"}:
        _fail(f"source-first output {record_id}/{output_id} has invalid kind/status")
    if status == "underdetermined":
        _strict_fields(
            value, _SOURCE_FIRST_UNDERDETERMINED_SPEC_FIELDS,
            label=f"source-first output {record_id}/{output_id} result_spec",
        )
        _source_first_text(value.get("reason"), field="source-first underdetermined reason")
        constraints = value.get("remaining_constraints")
        if not isinstance(constraints, list) or not constraints or len(constraints) > 128:
            _fail("source-first underdetermined result needs bounded remaining constraints")
        for constraint in constraints:
            _source_first_text(constraint, field="source-first remaining constraint")
        return
    if kind == "numeric":
        _strict_fields(
            value, _SOURCE_FIRST_NUMERIC_SPEC_FIELDS,
            label=f"source-first numeric output {record_id}/{output_id}",
        )
        expression = _source_first_text(
            value.get("raw_expression"), field="source-first numeric raw_expression"
        )
        if not re.search(r"\d", expression):
            _fail("source-first numeric raw_expression must contain a closed numeric term")
        for field in ("raw_value", "reported_value", "reporting_quantum"):
            _validate_bounded_numeric_text(
                value.get(field), field=f"source-first numeric {field}",
                allow_rational=field != "reported_value",
            )
        interval = value.get("certified_interval")
        if not isinstance(interval, Mapping) or set(interval) != {"lower", "upper"}:
            _fail("source-first numeric certified_interval must contain lower/upper")
        for field in ("lower", "upper"):
            _validate_bounded_numeric_text(
                interval.get(field), field=f"source-first numeric interval.{field}",
                allow_rational=True,
            )
        raw = _bounded_fraction(value.get("raw_value"), field="source-first raw_value")
        lower = _bounded_fraction(interval.get("lower"), field="source-first interval.lower")
        upper = _bounded_fraction(interval.get("upper"), field="source-first interval.upper")
        reported = _bounded_fraction(
            value.get("reported_value"), field="source-first reported_value"
        )
        quantum = _bounded_fraction(
            value.get("reporting_quantum"), field="source-first reporting_quantum"
        )
        if not lower < raw < upper:
            _fail("source-first raw value is not inside a nondegenerate certified interval")
        if quantum <= 0:
            _fail("source-first reporting quantum must be positive")
        if (reported / quantum).denominator != 1:
            _fail("source-first reported value is not an exact quantum multiple")
        half = quantum / 2
        if not (reported - half < lower and upper < reported + half):
            _fail("source-first interval is not wholly inside the committed rounding cell")
        _source_first_text(value.get("tie_rule"), field="source-first tie_rule")
        return
    if kind == "integer":
        _strict_fields(
            value, _SOURCE_FIRST_INTEGER_SPEC_FIELDS,
            label=f"source-first integer output {record_id}/{output_id}",
        )
        raw_value = _source_first_text(value.get("value"), field="source-first integer value")
        if not re.fullmatch(r"-?\d+", raw_value) or len(raw_value.lstrip("-")) > 192:
            _fail("source-first integer value must be a bounded exact integer")
    elif kind in {"formula", "classification"}:
        _strict_fields(
            value, _SOURCE_FIRST_SYMBOLIC_SPEC_FIELDS,
            label=f"source-first symbolic output {record_id}/{output_id}",
        )
        _source_first_text(
            value.get("normalized_result"), field="source-first normalized result"
        )
    elif kind == "finite_set":
        _strict_fields(
            value, _SOURCE_FIRST_SET_SPEC_FIELDS,
            label=f"source-first finite-set output {record_id}/{output_id}",
        )
        members = value.get("normalized_members")
        if (
            not isinstance(members, list) or not members or len(members) > 256
            or members != sorted(members)
            or len(members) != len(set(members))
        ):
            _fail("source-first finite-set members must be nonempty, sorted and unique")
        for member in members:
            _source_first_text(member, field="source-first finite-set member")
    else:
        _fail(f"source-first output has unsupported kind {kind!r}")
    _source_first_text(value.get("proposition"), field="source-first proposition")
    constraints = value.get("constraints")
    if not isinstance(constraints, list) or not constraints or len(constraints) > 128:
        _fail("source-first derived result needs bounded nonempty constraints")
    for constraint in constraints:
        _source_first_text(constraint, field="source-first constraint")


def _validate_source_first_commitment(
    *, commitment: Mapping[str, Any], attempt: Mapping[str, Any],
    seal: Mapping[str, Any], input_files: Mapping[str, str],
    review_projection_sha256: str, source_records: Mapping[str, Any],
    source_records_sha256: str, source_first_precommit_sha256: str,
) -> dict[str, dict[str, Any]]:
    _strict_fields(
        commitment, _SOURCE_FIRST_REVIEW_FIELDS,
        label="independent source-first commitment",
    )
    if (
        commitment.get("schema_version") != SCHEMA_VERSION
        or commitment.get("protocol") != PROTOCOL
        or commitment.get("phase") != "independent_source_first_commitment"
        or commitment.get("evaluation_mode") != "answer_blind"
        or commitment.get("official_answer_seen") is not False
        or any(
            commitment.get(field) != attempt.get(field)
            for field in (
                "variant", "model_family", "model_id", "run_id", "request_profile"
            )
        )
        or commitment.get("snapshot_inventory_sha256")
        != attempt.get("snapshot_inventory_sha256")
        or commitment.get("review_input_inventory_sha256")
        != _hash_index(input_files)
        or commitment.get("review_projection_sha256")
        != review_projection_sha256
        or commitment.get("source_first_precommit_sha256")
        != source_first_precommit_sha256
        or commitment.get("source_records_sha256") != source_records_sha256
    ):
        _fail("independent source-first commitment provenance is stale")
    scope_ids = seal.get("freeze_scope", {}).get("ids")
    if commitment.get("scope_ids") != scope_ids:
        _fail("independent source-first commitment scope differs from freeze scope")
    records = commitment.get("records")
    if records != source_records.get("records"):
        _fail("final source-first commitment records differ from the pre-B artifact")
    if not isinstance(records, list) or len(records) != len(scope_ids):
        _fail("independent source-first commitment record count differs from scope")
    by_id: dict[str, dict[str, Any]] = {}
    for record in records:
        if not isinstance(record, Mapping):
            _fail("independent source-first commitment record must be an object")
        _strict_fields(
            record, _SOURCE_FIRST_RECORD_FIELDS,
            label="independent source-first commitment record",
        )
        record_id = _require_nonempty_string(
            record.get("id"), field="source-first commitment id"
        )
        if record_id in by_id or record_id not in scope_ids:
            _fail("source-first commitment has duplicate/unscoped record")
        for field in (
            "blind_record_sha256", "source_record_sha256",
            "requested_outputs_sha256",
        ):
            _require_sha256(record.get(field), field=f"source-first {record_id}.{field}")
        if record.get("status") != "passed":
            _fail(f"source-first commitment did not pass for {record_id}")
        givens = record.get("givens")
        steps = record.get("derivation_steps")
        outputs = record.get("output_commitments")
        if not isinstance(givens, list) or not givens or len(givens) > 256:
            _fail(f"source-first commitment {record_id} needs bounded nonempty givens")
        if not isinstance(steps, list) or not steps or len(steps) > 512:
            _fail(f"source-first commitment {record_id} needs bounded derivation steps")
        if not isinstance(outputs, list) or not outputs or len(outputs) > 128:
            _fail(f"source-first commitment {record_id} needs bounded output commitments")
        known: set[str] = set()
        for given in givens:
            if not isinstance(given, Mapping):
                _fail("source-first given must be an object")
            _strict_fields(given, _SOURCE_FIRST_GIVEN_FIELDS, label="source-first given")
            given_id = _require_nonempty_string(given.get("id"), field="source-first given id")
            if given_id in known:
                _fail("source-first commitment contains duplicate evidence IDs")
            known.add(given_id)
            _source_first_text(given.get("source_locator"), field="source-first source locator")
            _source_first_text(given.get("fact"), field="source-first given fact")
        step_ids: set[str] = set()
        for step in steps:
            if not isinstance(step, Mapping):
                _fail("source-first derivation step must be an object")
            _strict_fields(
                step, _SOURCE_FIRST_DERIVATION_FIELDS,
                label="source-first derivation step",
            )
            step_id = _require_nonempty_string(step.get("id"), field="source-first step id")
            dependencies = step.get("depends_on")
            if (
                step_id in known
                or not isinstance(dependencies, list)
                or not dependencies
                or len(dependencies) != len(set(map(str, dependencies)))
                or any(not isinstance(item, str) or item not in known for item in dependencies)
            ):
                _fail("source-first derivation must be an ordered dependency-closed DAG")
            _source_first_text(step.get("claim"), field="source-first derivation claim")
            _source_first_text(
                step.get("justification"), field="source-first derivation justification"
            )
            known.add(step_id)
            step_ids.add(step_id)
        output_ids: set[str] = set()
        for output in outputs:
            if not isinstance(output, Mapping):
                _fail("source-first output commitment must be an object")
            _strict_fields(
                output, _SOURCE_FIRST_OUTPUT_FIELDS,
                label="source-first output commitment",
            )
            output_id = _require_nonempty_string(
                output.get("id"), field="source-first output id"
            )
            derivations = output.get("derivation_step_ids")
            if (
                output_id in output_ids
                or not isinstance(derivations, list)
                or not derivations
                or len(derivations) != len(set(map(str, derivations)))
                or any(item not in step_ids for item in derivations)
            ):
                _fail("source-first output commitment has invalid derivation coverage")
            output_ids.add(output_id)
            for field in ("source_requirement", "kind"):
                _source_first_text(
                    output.get(field), field=f"source-first output {output_id}.{field}"
                )
            if not isinstance(output.get("unit"), str):
                _fail("source-first output unit must be a string")
            if not isinstance(output.get("reporting_policy"), Mapping):
                _fail("source-first output commitment lacks a reporting policy")
            _validate_source_first_result_spec(
                output.get("result_spec"), output_kind=output.get("kind"),
                record_id=record_id, output_id=output_id,
            )
        by_id[record_id] = dict(record)
    if set(by_id) != set(scope_ids):
        _fail("source-first commitment is missing scoped record(s)")
    return by_id


def _validate_artifact_review_receipt(
    *, review: Mapping[str, Any], attempt: Mapping[str, Any],
    seal: Mapping[str, Any], input_files: Mapping[str, str],
    source_records_sha256: str, review_projection_sha256: str,
) -> dict[str, dict[str, Any]]:
    _strict_fields(review, _INDEPENDENT_REVIEW_FIELDS, label="independent artifact Review receipt")
    if (
        review.get("schema_version") != SCHEMA_VERSION
        or review.get("protocol") != PROTOCOL
        or review.get("phase") != "independent_artifact_review"
        or review.get("evaluation_mode") != "answer_blind"
        or review.get("official_answer_seen") is not False
        or any(
            review.get(field) != attempt.get(field)
            for field in (
                "variant", "model_family", "model_id", "run_id", "request_profile"
            )
        )
        or review.get("snapshot_inventory_sha256")
        != attempt.get("snapshot_inventory_sha256")
        or review.get("review_input_inventory_sha256") != _hash_index(input_files)
        or review.get("review_projection_sha256") != review_projection_sha256
        or review.get("source_records_sha256") != source_records_sha256
    ):
        _fail("independent artifact Review semantic receipt provenance is stale")
    scope_ids = seal.get("freeze_scope", {}).get("ids")
    if review.get("scope_ids") != scope_ids:
        _fail("independent artifact Review scope differs from controller freeze scope")
    records = review.get("records")
    if not isinstance(records, list) or len(records) != len(scope_ids):
        _fail("independent artifact Review record count differs from scope")
    by_id: dict[str, dict[str, Any]] = {}
    for record in records:
        if not isinstance(record, Mapping):
            _fail("independent artifact Review record must be an object")
        _strict_fields(record, _INDEPENDENT_REVIEW_RECORD_FIELDS, label="independent artifact Review record")
        record_id = _require_nonempty_string(record.get("id"), field="independent Review record id")
        if record_id in by_id or record_id not in scope_ids:
            _fail("independent artifact Review has duplicate/unscoped record")
        for field in (
            "target_sha256", "candidate_sha256", "source_report_sha256",
            "blueprint_sha256", "source_contract_sha256", "requested_outputs_sha256",
            "source_commitment_record_sha256",
        ):
            _require_sha256(record.get(field), field=f"independent Review {record_id}.{field}")
        alignment = record.get("source_alignment")
        if not isinstance(alignment, Mapping):
            _fail("independent artifact Review source_alignment is missing")
        _strict_fields(alignment, _SOURCE_ALIGNMENT_FIELDS, label="independent Review source_alignment")
        if alignment.get("status") != "passed":
            _fail("independent artifact Review does not align with the source-first commitment")
        _require_nonempty_string(alignment.get("evidence"), field="independent Review source alignment evidence")
        if record.get("formalization_status") != "passed" or record.get("proof_status") != "solved":
            _fail("independent Review record is not passing both Review stages")
        formal = record.get("formalization_certificate")
        proof = record.get("proof_certificate")
        if not isinstance(formal, Mapping) or not isinstance(proof, Mapping):
            _fail("independent Review record lacks full certificates")
        formal_fields = set(formal)
        missing_formal = _INDEPENDENT_FORMAL_CERTIFICATE_REQUIRED_FIELDS - formal_fields
        extra_formal = formal_fields - (
            _INDEPENDENT_FORMAL_CERTIFICATE_REQUIRED_FIELDS
            | _INDEPENDENT_FORMAL_CERTIFICATE_OPTIONAL_FIELDS
        )
        if missing_formal or extra_formal:
            _fail(
                "independent formalization Review certificate has invalid fields: "
                f"missing={sorted(missing_formal)}, extra={sorted(extra_formal)}"
            )
        if any(
            formal.get(field) is not None
            for field in _INDEPENDENT_FORMAL_CERTIFICATE_OPTIONAL_FIELDS
        ):
            _fail(
                "independent answer-blind Review may not carry official-answer "
                "alignment or source-inconsistency content"
            )
        _strict_fields(proof, _INDEPENDENT_PROOF_CERTIFICATE_FIELDS, label="independent proof Review certificate")
        by_id[record_id] = dict(record)
    if set(by_id) != set(scope_ids):
        _fail("independent artifact Review is missing scoped record(s)")
    return by_id


def _validate_source_records_commitment(
    *, records_artifact: Mapping[str, Any], source_attempt: Mapping[str, Any],
    seal: Mapping[str, Any], source_files: Mapping[str, str],
    source_projection_sha256: str,
) -> None:
    _strict_fields(
        records_artifact, _SOURCE_FIRST_RECORDS_COMMITMENT_FIELDS,
        label="source-first records commitment",
    )
    scope_ids = seal.get("freeze_scope", {}).get("ids")
    if (
        records_artifact.get("schema_version") != SCHEMA_VERSION
        or records_artifact.get("protocol") != PROTOCOL
        or records_artifact.get("phase") != "independent_source_first_records"
        or records_artifact.get("evaluation_mode") != "answer_blind"
        or records_artifact.get("official_answer_seen") is not False
        or any(
            records_artifact.get(field) != source_attempt.get(field)
            for field in (
                "variant", "model_family", "model_id", "run_id", "request_profile"
            )
        )
        or records_artifact.get("review_input_inventory_sha256")
        != _hash_index(source_files)
        or records_artifact.get("review_projection_sha256")
        != source_projection_sha256
        or records_artifact.get("scope_ids") != scope_ids
        or not isinstance(records_artifact.get("records"), list)
        or len(records_artifact["records"]) != len(scope_ids)
    ):
        _fail("source-first records commitment provenance/scope is stale")


def validate_structured_source_records(
    *, records_commitment: Mapping[str, Any],
    bundle_records: Mapping[str, Mapping[str, Any]],
    input_files: Mapping[str, str],
) -> dict[str, dict[str, Any]]:
    """Deep-validate Pass-A records before any solver or Pass-B request.

    This public pure validator is intentionally snapshot-free.  It validates
    the complete evidence DAG/numeric commitments by reusing the final freeze
    validator, then binds every record to the canonical source-only projection
    and requested-output contract supplied by the trusted controller.
    """
    if not isinstance(records_commitment, Mapping):
        _fail("source-first records commitment must be an object")
    _strict_fields(
        records_commitment, _SOURCE_FIRST_RECORDS_COMMITMENT_FIELDS,
        label="source-first records commitment",
    )
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3"),
    }.get(records_commitment.get("variant"))
    if (
        records_commitment.get("schema_version") != SCHEMA_VERSION
        or records_commitment.get("protocol") != PROTOCOL
        or records_commitment.get("phase") != "independent_source_first_records"
        or records_commitment.get("evaluation_mode") != "answer_blind"
        or records_commitment.get("official_answer_seen") is not False
        or records_commitment.get("request_profile") != _STRUCTURED_REVIEW_PROFILE
        or expected_identity != (
            records_commitment.get("model_family"),
            records_commitment.get("model_id"),
        )
    ):
        _fail("source-first records commitment metadata/model is stale")
    _require_nonempty_string(
        records_commitment.get("run_id"), field="source-first records run_id"
    )
    _require_sha256(
        records_commitment.get("review_projection_sha256"),
        field="source-first records review_projection_sha256",
    )
    scope_ids = _strict_id_list(
        records_commitment.get("scope_ids"), label="source-first records scope"
    )
    if set(bundle_records) != set(scope_ids):
        _fail("source-first records bundle bindings differ from scope")
    if records_commitment.get("review_input_inventory_sha256") != _hash_index(
        input_files
    ):
        _fail("source-first records input inventory digest is stale")
    synthetic_attempt = {
        field: records_commitment.get(field)
        for field in ("variant", "model_family", "model_id", "run_id", "request_profile")
    }
    synthetic_attempt.update({
        "snapshot_inventory_sha256": "0" * 64,
        "review_input_inventory_sha256": _hash_index(input_files),
        "review_projection_sha256": records_commitment.get(
            "review_projection_sha256"
        ),
    })
    synthetic_commitment = {
        **dict(records_commitment),
        "phase": "independent_source_first_commitment",
        "snapshot_inventory_sha256": "0" * 64,
        "source_first_precommit_sha256": "1" * 64,
        "source_records_sha256": "2" * 64,
    }
    rows = _validate_source_first_commitment(
        commitment=synthetic_commitment,
        attempt=synthetic_attempt,
        seal={"freeze_scope": {"ids": scope_ids}},
        input_files=input_files,
        review_projection_sha256=str(
            records_commitment.get("review_projection_sha256") or ""
        ),
        source_records=records_commitment,
        source_records_sha256="2" * 64,
        source_first_precommit_sha256="1" * 64,
    )
    for record_id in scope_ids:
        row = bundle_records[record_id]
        if not isinstance(row, Mapping):
            _fail(f"source-first bundle record is invalid for {record_id}")
        projection = _source_first_projection(row)
        expected_projection_path = (
            f"{_SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        )
        expected_projection_sha = _sha256_bytes(_json_bytes(projection))
        if input_files.get(expected_projection_path) != expected_projection_sha:
            _fail(f"source-first input lacks canonical projection for {record_id}")
        record = rows[record_id]
        allowed_locators = {
            f"source.{field}"
            for field in ("current_question", "shared_context", "previous_parts")
            if field in projection
        }
        allowed_locators.update(
            f"image:{path}"
            for path in row.get("images", [])
            if isinstance(path, str) and path
        )
        givens = record.get("givens")
        if not isinstance(givens, list) or any(
            not isinstance(given, Mapping)
            or given.get("source_locator") not in allowed_locators
            for given in givens
        ):
            _fail(f"source-first records cite non-source material for {record_id}")
        requested = row.get("requested_outputs")
        committed = record.get("output_commitments")
        if (
            not isinstance(requested, list)
            or not isinstance(committed, list)
            or len(committed) != len(requested)
            or any(not isinstance(item, Mapping) for item in committed)
            or record.get("blind_record_sha256")
            != _sha256_bytes(_json_bytes(row))
            or record.get("source_record_sha256") != expected_projection_sha
            or record.get("requested_outputs_sha256")
            != _sha256_bytes(_json_bytes(requested))
        ):
            _fail(f"source-first records do not bind canonical source for {record_id}")
        if [
            {
                key: item.get(key)
                for key in ("id", "source_requirement", "kind", "unit", "reporting_policy")
            }
            for item in committed if isinstance(item, Mapping)
        ] != requested:
            _fail(f"source-first records do not exactly cover requested outputs for {record_id}")
        top_reporting = row.get("reporting_policy")
        if not isinstance(top_reporting, Mapping):
            _fail(f"source-first reporting policy is missing for {record_id}")
        for source_output, commitment_output in zip(
            requested, committed, strict=True
        ):
            assert isinstance(source_output, Mapping) and isinstance(
                commitment_output, Mapping
            )
            if source_output.get("kind") != "numeric":
                continue
            spec = commitment_output.get("result_spec")
            policy = source_output.get("reporting_policy")
            if not isinstance(spec, Mapping) or not isinstance(policy, Mapping):
                _fail(f"source-first numeric policy/spec is missing for {record_id}")
            # An underdetermined numeric output deliberately has no reported
            # value or rounding cell.  Its missing-data constraints were
            # already checked by _validate_source_first_result_spec above;
            # applying the derived-value reporting contract here would make
            # the schema's underdetermined branch impossible to use.
            if spec.get("status") == "underdetermined":
                continue
            expected_tie = policy.get("tie_rule", top_reporting.get("tie_rule"))
            reported_text = str(spec.get("reported_value"))
            try:
                expected_quantum = _rounding_quantum(
                    policy, Decimal(reported_text)
                )
            except InvalidOperation:
                expected_quantum = None
            if (
                spec.get("tie_rule") != expected_tie
                or expected_quantum is None
                or _bounded_fraction(
                    spec.get("reporting_quantum"),
                    field=f"source-first {record_id} reporting quantum",
                ) != Fraction(expected_quantum)
            ):
                _fail(
                    f"source-first reporting quantum/tie rule does not match "
                    f"predeclared policy for {record_id}/{source_output.get('id')}"
                )
    return rows


def _load_independent_review_invocation(
    *, project: Path, seal: Mapping[str, Any]
) -> tuple[
    dict[str, Any], bytes, dict[str, Any], bytes, dict[str, Any], bytes,
    dict[str, str], dict[str, str], dict[str, Any], bytes,
]:
    aggregate_path, aggregate, aggregate_payload = _load_bound_external_receipt(
        project=project, spec=seal.get("independent_review_receipt"),
        label="independent Review aggregate receipt",
    )
    if (aggregate_path.stat(follow_symlinks=False).st_mode & 0o777) != 0o400:
        _fail("independent Review aggregate receipt must be mode 0400")
    _strict_fields(
        aggregate, _STRUCTURED_REVIEW_AGGREGATE_FIELDS,
        label="independent Review aggregate receipt",
    )
    scope_ids = seal.get("freeze_scope", {}).get("ids")
    solver = seal.get("solver")
    snapshot = seal.get("snapshot_inventory")
    runtime = seal.get("runtime_inventory")
    expected_identity = {
        "gpt": ("openai", "gpt-5.6-sol"),
        "kimi-k3": ("moonshot", "kimi-k3"),
    }.get(aggregate.get("variant"))
    if (
        aggregate.get("schema_version") != SCHEMA_VERSION
        or aggregate.get("protocol") != PROTOCOL
        or aggregate.get("phase") != "structured_independent_review_aggregate"
        or aggregate.get("request_profile") != _STRUCTURED_REVIEW_PROFILE
        or aggregate.get("tools_enabled") is not False
        or aggregate.get("store") is not False
        or aggregate.get("all_passes_finalized") is not True
        or aggregate.get("scope_ids") != scope_ids
        or not isinstance(solver, Mapping)
        or any(aggregate.get(field) != solver.get(field) for field in _SOLVER_FIELDS)
        or expected_identity
        != (aggregate.get("model_family"), aggregate.get("model_id"))
        or not isinstance(snapshot, Mapping)
        or aggregate.get("snapshot_inventory_sha256")
        != snapshot.get("files_sha256")
    ):
        _fail("independent Review aggregate metadata/scope is stale")
    controller_sha = _require_sha256(
        aggregate.get("controller_binary_sha256"),
        field="independent Review controller_binary_sha256",
    )
    runtime_files = runtime.get("files") if isinstance(runtime, Mapping) else None
    if not isinstance(runtime_files, Mapping) or controller_sha not in set(
        runtime_files.values()
    ):
        _fail("independent Review controller binary is absent from runtime inventory")
    (
        source_attempt_path, source_attempt, source_attempt_payload,
        source_files, commitment, commitment_payload, source_projection_sha,
        source_broker_pair,
    ) = _load_structured_review_pass(
        project=project, seal=seal, aggregate=aggregate,
        spec=aggregate.get("source_first_attempt"),
        expected_fields=_STRUCTURED_SOURCE_REVIEW_ATTEMPT_FIELDS,
        expected_phase="structured_source_first_review_attempt",
        label="independent source-first Review", source_first=True,
        expected_source_records_sha256=None,
    )
    commitment_sha = _sha256_bytes(commitment_payload)
    records_path, source_records, source_records_payload = (
        _load_bound_external_receipt(
            project=project, spec=source_attempt.get("source_records_commitment"),
            label="source-first records commitment",
        )
    )
    if records_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail("source-first records commitment must be mode 0400")
    source_records_sha = _sha256_bytes(source_records_payload)
    precommit_spec = seal.get("source_first_precommit")
    if not isinstance(precommit_spec, Mapping):
        _fail("source-first precommit binding is missing")
    precommit_sha = _require_sha256(
        precommit_spec.get("sha256"), field="source-first precommit sha256"
    )
    _validate_source_records_commitment(
        records_artifact=source_records, source_attempt=source_attempt,
        seal=seal, source_files=source_files,
        source_projection_sha256=source_projection_sha,
    )
    (
        evaluation_attempt_path, evaluation_attempt, evaluation_attempt_payload,
        evaluation_files, review, review_payload, evaluation_projection_sha,
        evaluation_broker_pair,
    ) = _load_structured_review_pass(
        project=project, seal=seal, aggregate=aggregate,
        spec=aggregate.get("artifact_review_attempt"),
        expected_fields=_STRUCTURED_ARTIFACT_REVIEW_ATTEMPT_FIELDS,
        expected_phase="structured_artifact_review_attempt",
        label="independent artifact Review", source_first=False,
        expected_source_records_sha256=source_records_sha,
    )
    review_sha = _sha256_bytes(review_payload)
    records_spec = evaluation_attempt.get("source_records_commitment")
    repeated_records_path, repeated_records, repeated_records_payload = _load_bound_external_receipt(
        project=project, spec=records_spec,
        label="artifact Review source-first records",
    )
    source_receipt_spec = source_attempt.get("constructed_semantic_receipt")
    if not isinstance(source_receipt_spec, Mapping):
        _fail("source-first structured Review lacks its commitment locator")
    if (
        repeated_records_path != records_path
        or repeated_records != source_records
        or repeated_records_payload != source_records_payload
        or evaluation_attempt.get("source_first_attempt_sha256")
        != _sha256_bytes(source_attempt_payload)
        or aggregate.get("source_records_sha256") != source_records_sha
        or aggregate.get("source_commitment_sha256") != commitment_sha
        or aggregate.get("semantic_review_sha256") != review_sha
        or source_broker_pair == evaluation_broker_pair
    ):
        _fail("independent Review A-to-B commitment/hash chain is stale")
    _solver_path, solver_aggregate, _solver_payload = _load_bound_external_receipt(
        project=project, spec=seal.get("structured_solver_receipt"),
        label="structured solver aggregate",
    )
    solver_transport = solver_aggregate.get("transport")
    if not isinstance(solver_transport, Mapping):
        _fail("structured solver transport is absent during independent Review binding")
    if solver_aggregate.get("variant") == "kimi-k3":
        _solver_ready, solver_ready_sha, _solver_transcript, solver_transcript_sha = (
            _load_and_validate_model_broker_binding(
                project=project,
                binding={
                    "ready_receipt": solver_transport.get("ready_receipt"),
                    "transcript": solver_transport.get("transcript"),
                },
                variant="kimi-k3", run_id=solver_aggregate.get("run_id"),
                model_id=solver_aggregate.get("model_id"), runtime=runtime,
                minimum_requests=1,
                exact_requests=solver_aggregate.get("request_count"),
                request_profile=_STRUCTURED_REQUEST_PROFILE,
                label="structured solver model_broker",
            )
        )
        if (solver_ready_sha, solver_transcript_sha) in {
            source_broker_pair, evaluation_broker_pair
        }:
            _fail("solve and Review passes must use distinct broker lifecycles")
    if evaluation_files.get(_SOURCE_COMMITMENT_INPUT) != source_records_sha:
        _fail("artifact Review input does not contain the exact source-first records")
    source_rows = _validate_source_first_commitment(
        commitment=commitment, attempt=source_attempt, seal=seal,
        input_files=source_files, review_projection_sha256=source_projection_sha,
        source_records=source_records, source_records_sha256=source_records_sha,
        source_first_precommit_sha256=precommit_sha,
    )
    review_rows = _validate_artifact_review_receipt(
        review=review, attempt=evaluation_attempt, seal=seal,
        input_files=evaluation_files, source_records_sha256=source_records_sha,
        review_projection_sha256=evaluation_projection_sha,
    )
    for record_id, row in review_rows.items():
        if row.get("source_commitment_record_sha256") != _sha256_bytes(
            _json_bytes(source_rows[record_id])
        ):
            _fail(f"artifact Review does not bind source-first record {record_id}")
    return (
        aggregate, aggregate_payload, commitment, commitment_payload,
        review, review_payload, source_files, evaluation_files,
        source_records, source_records_payload,
    )


def _load_controller_seal(
    *, project: Path, path: Path | str, expected_sha256: str
) -> tuple[Path, dict[str, Any], bytes]:
    seal_path = Path(path)
    if not seal_path.is_absolute():
        seal_path = Path.cwd() / seal_path
    seal_path = _outside_project(seal_path, project, label="controller seal")
    _require_controller_owned_readonly(seal_path, label="controller seal")
    seal, payload = _read_json(
        seal_path, label="controller seal", max_bytes=_MAX_CONTROLLER_SEAL_BYTES
    )
    expected = _require_sha256(
        expected_sha256, field="expected_controller_seal_sha256"
    )
    if _sha256_bytes(payload) != expected:
        _fail("controller seal SHA-256 does not match controller expectation")
    _strict_fields(seal, _CONTROLLER_BINDING_FIELDS, label="controller seal")
    if seal.get("schema_version") != SCHEMA_VERSION:
        _fail("controller seal requires schema_version=1")
    if seal.get("protocol") != PROTOCOL or seal.get("phase") != CONTROLLER_PHASE:
        _fail("controller seal has an unsupported protocol or phase")
    if seal.get("solver_stopped") is not True:
        _fail("controller seal must attest solver_stopped=true")
    _require_sha256(
        seal.get("seed_manifest_sha256"),
        field="controller seal seed_manifest_sha256",
    )
    bundle = seal.get("blind_bundle")
    if not isinstance(bundle, dict):
        _fail("controller seal blind_bundle must be an object")
    _strict_fields(bundle, _CONTROLLER_BUNDLE_FIELDS, label="controller seal blind_bundle")
    _require_sha256(bundle.get("sha256"), field="controller seal blind_bundle.sha256")
    if not isinstance(bundle.get("row_count"), int) or isinstance(
        bundle.get("row_count"), bool
    ) or bundle["row_count"] < 1:
        _fail("controller seal blind_bundle.row_count must be positive")
    bundle_ids = _strict_id_list(bundle.get("ids"), label="controller seal bundle ids")
    if bundle["row_count"] != len(bundle_ids):
        _fail("controller seal blind_bundle row_count and ids disagree")
    raw_bundle_path = bundle.get("path")
    _resolve_project_locator(project, raw_bundle_path, label="questions-only bundle")

    scope = seal.get("freeze_scope")
    if not isinstance(scope, dict):
        _fail("controller seal freeze_scope must be an object")
    _strict_fields(scope, _CONTROLLER_SCOPE_FIELDS, label="controller seal freeze_scope")
    kind = scope.get("kind")
    if kind not in {"full", "pilot"}:
        _fail("controller seal freeze_scope.kind must be full or pilot")
    scope_ids = _strict_id_list(scope.get("ids"), label="controller seal scope ids")
    if not set(scope_ids).issubset(bundle_ids):
        _fail("controller seal freeze scope is not a subset of bundle IDs")
    if kind == "full" and scope_ids != bundle_ids:
        _fail("a full controller freeze scope must equal the complete bundle ID set")

    generated = seal.get("generated_files")
    if not isinstance(generated, dict):
        _fail("controller seal generated_files must be an object")
    if set(generated) != _CONTROLLER_GENERATED_FILES:
        _fail("controller seal must bind config, MCP config, and protocol document exactly")
    for relative, digest in generated.items():
        _resolve_project_locator(project, relative, label="controller-generated file")
        _require_sha256(digest, field=f"controller seal generated_files[{relative}]")
    _validate_dependency_inventory(seal, project=project)
    _validate_runtime_inventory(seal, project=project)
    _validate_snapshot_inventory(seal, project=project)
    _validate_verifier_snapshot(seal, project=project)
    structured, _structured_payload, _structured_targets = (
        _load_and_validate_structured_solver(project=project, seal=seal)
    )
    _load_and_validate_verifier_invocation(project=project, seal=seal)
    _load_independent_review_invocation(project=project, seal=seal)
    return seal_path, seal, payload


def _parse_blind_bundle(
    *, project: Path, seal: Mapping[str, Any]
) -> tuple[Path, bytes, dict[str, tuple[dict[str, Any], str]]]:
    spec = seal["blind_bundle"]
    assert isinstance(spec, Mapping)
    path = _resolve_project_locator(
        project, spec.get("path"), label="questions-only bundle"
    )
    payload = _read_plain_bytes(path, label="questions-only bundle")
    if _sha256_bytes(payload) != spec.get("sha256"):
        _fail("questions-only bundle hash does not match controller seal")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(f"questions-only bundle is not UTF-8: {exc}")
    records: dict[str, tuple[dict[str, Any], str]] = {}
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            _fail(f"invalid questions-only JSON at {path}:{line_number}: {exc}")
        if not isinstance(row, dict):
            _fail(f"questions-only row {line_number} must be an object")
        leakage = _find_leakage_keys(row, path=f"bundle[{line_number}]")
        if leakage:
            _fail("questions-only bundle contains leakage field(s): " + ", ".join(leakage))
        if row.get("schema_version") != SCHEMA_VERSION or row.get("protocol") != PROTOCOL:
            _fail(f"questions-only row {line_number} has unsupported schema/protocol")
        if (
            str(row.get("evaluation_mode") or "").replace("-", "_") != "answer_blind"
            or row.get("official_answer_seen") is not False
            or row.get("phase") != "solve"
        ):
            _fail(f"questions-only row {line_number} is not a blind solve record")
        if "blind_record_sha256" in row:
            _fail(f"questions-only row {line_number} contains reserved blind hash")
        record_id = _require_nonempty_string(
            row.get("id"), field=f"questions-only row {line_number}.id"
        )
        if not _SAFE_ID_RE.fullmatch(record_id):
            _fail(f"questions-only row {line_number} has unsafe ID")
        if record_id in records:
            _fail(f"duplicate questions-only bundle id: {record_id}")
        records[record_id] = (row, _sha256_bytes(_json_bytes(row)))
    actual_ids = sorted(records)
    expected_ids = spec.get("ids")
    if actual_ids != expected_ids or len(records) != spec.get("row_count"):
        _fail("questions-only bundle ID set/row count does not match controller seal")
    return path, payload, records


def _validated_hash_map(value: object, *, label: str) -> dict[str, str]:
    if not isinstance(value, dict) or not value:
        _fail(f"{label} must be a non-empty path-to-SHA-256 object")
    result: dict[str, str] = {}
    for raw_path, raw_digest in value.items():
        path = str(raw_path)
        if not path or Path(path).is_absolute() or ".." in Path(path).parts or "\\" in path:
            _fail(f"{label} contains an unsafe project path: {path!r}")
        result[path] = _require_sha256(raw_digest, field=f"{label}[{path}]")
    return result


def _regular_file_inventory(
    root: Path, *, label: str, require_controller_owner: bool = True,
    exclude_roots: Sequence[Path] = (),
) -> dict[str, str]:
    if root.is_symlink() or not root.is_dir():
        _fail(f"{label} must be a regular, non-symlink directory: {root}")
    exclusions = tuple(path.resolve() for path in exclude_roots)
    inventory: dict[str, str] = {}
    total_bytes = 0

    def account(size: int) -> None:
        nonlocal total_bytes
        if len(inventory) >= _MAX_INVENTORY_FILES:
            _fail(f"{label} exceeds the file-count safety limit")
        total_bytes += size
        if total_bytes > _MAX_INVENTORY_TOTAL_BYTES:
            _fail(f"{label} exceeds the total-byte safety limit")

    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(root).as_posix()
            try:
                resolved_child = child.resolve(strict=True)
            except OSError as exc:
                _fail(f"{label} contains a broken entry: {relative}: {exc}")
            if resolved_child in exclusions:
                continue
            if child.is_symlink():
                try:
                    resolved_child.relative_to(root.resolve())
                except (OSError, ValueError) as exc:
                    _fail(f"{label} contains an escaping/broken symlink: {relative}: {exc}")
                if not resolved_child.is_dir():
                    _fail(f"{label} directory symlink has a non-directory target: {relative}")
                if require_controller_owner and child.lstat().st_uid != os.geteuid():
                    _fail(f"{label} directory symlink is not controller-owned: {relative}")
                target = os.readlink(child)
                account(len(target.encode("utf-8")))
                inventory[relative] = _sha256_bytes(
                    b"symlink\0" + target.encode("utf-8")
                )
                # The target must already be reachable through a canonical
                # in-root directory.  Do not follow it a second time.
                continue
            if require_controller_owner:
                _require_controller_owned_readonly(child, label=f"{label} directory")
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            child = base / name
            relative = child.relative_to(root).as_posix()
            if child.is_symlink():
                try:
                    resolved = child.resolve(strict=True)
                    resolved.relative_to(root.resolve())
                except (OSError, ValueError) as exc:
                    _fail(f"{label} contains an escaping/broken symlink: {relative}: {exc}")
                if not resolved.is_file():
                    _fail(f"{label} file symlink has a non-file target: {relative}")
                if require_controller_owner and child.lstat().st_uid != os.geteuid():
                    _fail(f"{label} file symlink is not controller-owned: {relative}")
                target = os.readlink(child)
                account(len(target.encode("utf-8")))
                inventory[relative] = _sha256_bytes(
                    b"symlink\0" + target.encode("utf-8")
                )
                continue
            if not child.is_file():
                _fail(f"{label} contains an unsafe filesystem entry: {relative}")
            if require_controller_owner:
                _require_controller_owned_readonly(child, label=f"{label} file")
            digest, size = _sha256_plain_file_streaming(
                child,
                label=f"{label} file",
                max_bytes=_MAX_INVENTORY_TOTAL_BYTES,
            )
            account(size)
            inventory[relative] = digest
    if not inventory:
        _fail(f"{label} contains no regular files")
    return dict(sorted(inventory.items()))


def _project_snapshot_inventory(
    project: Path, *, dependency_root: Path, require_controller_owner: bool = True
) -> dict[str, str]:
    """Hash the complete solver snapshot, excluding only fresh Git metadata.

    ``.lake/packages`` may be a single symlink to the separately inventoried,
    controller-owned dependency tree.  Every other symlink or special entry is
    rejected.  Generated build outputs and fresh Git metadata are included.
    """
    if require_controller_owner:
        _require_controller_owned_readonly(project, label="solver snapshot root")
    inventory: dict[str, str] = {}
    total_bytes = 0
    for directory, names, files in os.walk(project, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(project).as_posix()
            if relative in {".lake/build", ".lake/config"} or relative.startswith(
                (".lake/build/", ".lake/config/")
            ):
                _fail(
                    "solver snapshot contains untrusted Lake build/config state; "
                    f"a clean verifier snapshot is required: {relative}"
                )
            if child.is_symlink():
                if relative == ".lake/packages" and child.resolve() == dependency_root:
                    if require_controller_owner and child.lstat().st_uid != os.geteuid():
                        _fail("solver dependency symlink is not controller-owned")
                    continue
                _fail(f"solver snapshot contains an unapproved symlink: {relative}")
            if not child.is_dir():
                _fail(f"solver snapshot contains an unsafe directory entry: {relative}")
            if require_controller_owner:
                _require_controller_owned_readonly(child, label="solver snapshot directory")
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            child = base / name
            relative = child.relative_to(project).as_posix()
            if child.suffix in {".olean", ".ilean"}:
                _fail(
                    "solver snapshot contains a solver-produced compiled Lean artifact: "
                    + relative
                )
            if child.is_symlink() or not child.is_file():
                _fail(f"solver snapshot contains an unsafe file entry: {relative}")
            if require_controller_owner:
                _require_controller_owned_readonly(child, label="solver snapshot file")
            if len(inventory) >= _MAX_INVENTORY_FILES:
                _fail("solver snapshot exceeds the file-count safety limit")
            digest, size = _sha256_plain_file_streaming(
                child,
                label="solver snapshot file",
                max_bytes=_MAX_INVENTORY_TOTAL_BYTES,
            )
            total_bytes += size
            if total_bytes > _MAX_INVENTORY_TOTAL_BYTES:
                _fail("solver snapshot exceeds the total-byte safety limit")
            inventory[relative] = digest
    if not inventory:
        _fail("solver snapshot contains no regular files")
    return dict(sorted(inventory.items()))


def _validate_dependency_inventory(
    seal: Mapping[str, Any], *, project: Path
) -> None:
    raw = seal.get("dependency_inventory")
    if not isinstance(raw, dict):
        _fail("controller seal dependency_inventory must be an object")
    _strict_fields(
        raw, _DEPENDENCY_INVENTORY_FIELDS, label="controller seal dependency_inventory"
    )
    root_raw = raw.get("root")
    if not isinstance(root_raw, str) or not Path(root_raw).is_absolute():
        _fail("controller dependency root must be an absolute path")
    dependency_root = Path(root_raw).resolve()
    _outside_project(dependency_root, project, label="controller dependency root")
    _require_controller_owned_readonly(
        dependency_root, label="controller dependency root"
    )
    expected = _validated_hash_map(
        raw.get("files"), label="controller seal dependency_inventory.files"
    )
    if raw.get("files_sha256") != _hash_index(expected):
        _fail("controller dependency inventory index hash is invalid")
    actual = _regular_file_inventory(
        dependency_root, label="controller dependency tree"
    )
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(
            path for path in set(actual) & set(expected) if actual[path] != expected[path]
        )
        _fail(
            "controller dependency inventory drift "
            f"(missing={missing}, extra={extra}, changed={changed})"
        )


def _validate_runtime_inventory(
    seal: Mapping[str, Any], *, project: Path
) -> None:
    raw = seal.get("runtime_inventory")
    if not isinstance(raw, dict):
        _fail("controller seal runtime_inventory must be an object")
    _strict_fields(raw, _RUNTIME_INVENTORY_FIELDS, label="controller seal runtime_inventory")
    root_raw = raw.get("root")
    if not isinstance(root_raw, str) or not Path(root_raw).is_absolute():
        _fail("controller runtime root must be an absolute path")
    runtime_root = Path(root_raw).resolve()
    _outside_project(runtime_root, project, label="controller runtime root")
    _require_controller_owned_readonly(runtime_root, label="controller runtime root")
    dependency = seal.get("dependency_inventory")
    if not isinstance(dependency, Mapping):
        _fail("controller seal dependency inventory is missing")
    dependency_root = Path(str(dependency.get("root") or "")).resolve()
    expected = _validated_hash_map(
        raw.get("files"), label="controller seal runtime_inventory.files"
    )
    if raw.get("files_sha256") != _hash_index(expected):
        _fail("controller runtime inventory index hash is invalid")
    actual = _regular_file_inventory(
        runtime_root,
        label="controller answer-blind runtime",
        exclude_roots=(dependency_root,),
    )
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(
            path for path in set(actual) & set(expected) if actual[path] != expected[path]
        )
        _fail(
            "controller runtime inventory drift "
            f"(missing={missing}, extra={extra}, changed={changed})"
        )


def _validate_snapshot_inventory(
    seal: Mapping[str, Any], *, project: Path
) -> dict[str, str]:
    raw = seal.get("snapshot_inventory")
    if not isinstance(raw, dict):
        _fail("controller seal snapshot_inventory must be an object")
    _strict_fields(
        raw, _SNAPSHOT_INVENTORY_FIELDS, label="controller seal snapshot_inventory"
    )
    expected = _validated_hash_map(
        raw.get("files"), label="controller seal snapshot_inventory.files"
    )
    if raw.get("files_sha256") != _hash_index(expected):
        _fail("controller snapshot inventory index hash is invalid")
    dependency = seal["dependency_inventory"]
    assert isinstance(dependency, Mapping)
    dependency_root = Path(str(dependency["root"])).resolve()
    actual = _project_snapshot_inventory(project, dependency_root=dependency_root)
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(
            path for path in set(actual) & set(expected) if actual[path] != expected[path]
        )
        _fail(
            "solver snapshot inventory drift "
            f"(missing={missing}, extra={extra}, changed={changed})"
        )
    return actual


def _validate_verifier_snapshot(
    seal: Mapping[str, Any], *, project: Path
) -> tuple[Path, dict[str, str]]:
    """Re-hash the external, traversable clean snapshot used by the verifier."""
    raw = seal.get("verifier_snapshot")
    if not isinstance(raw, Mapping):
        _fail("controller seal verifier_snapshot must be an object")
    _strict_fields(
        raw, _VERIFIER_SNAPSHOT_FIELDS, label="controller seal verifier_snapshot"
    )
    raw_root = raw.get("root")
    if not isinstance(raw_root, str) or not Path(raw_root).is_absolute():
        _fail("controller verifier snapshot root must be absolute")
    root = _outside_project(
        Path(raw_root), project, label="controller verifier snapshot root"
    )
    for ancestor in (root, *root.parents):
        if ancestor.stat(follow_symlinks=False).st_mode & 0o001 == 0:
            _fail(
                "controller verifier snapshot path must be world-traversable: "
                f"{ancestor}"
            )
    _require_controller_owned_readonly(root, label="controller verifier snapshot root")
    expected = _validated_hash_map(
        raw.get("files"), label="controller seal verifier_snapshot.files"
    )
    if raw.get("files_sha256") != _hash_index(expected):
        _fail("controller verifier snapshot inventory digest is invalid")
    actual = _regular_file_inventory(root, label="controller verifier snapshot")
    if actual != expected:
        _fail("controller verifier snapshot inventory drift")
    sealed = seal.get("snapshot_inventory")
    if not isinstance(sealed, Mapping) or (
        expected != sealed.get("files")
        or raw.get("files_sha256") != sealed.get("files_sha256")
    ):
        _fail("controller verifier snapshot differs from the sealed project snapshot")
    for directory, names, files in os.walk(root, followlinks=False):
        base = Path(directory)
        if base.stat(follow_symlinks=False).st_mode & 0o005 != 0o005:
            _fail("controller verifier snapshot directories must be world-traversable")
        for name in [*names, *files]:
            child = base / name
            if child.is_symlink():
                _fail("controller verifier snapshot may not contain symlinks")
            if child.is_file() and child.stat(follow_symlinks=False).st_mode & 0o004 == 0:
                _fail("controller verifier snapshot files must be world-readable")
    return root, expected


def _validate_seed_and_root_files(
    *, project: Path, seal: Mapping[str, Any], bundle_path: Path, bundle_payload: bytes
) -> list[dict[str, str]]:
    seed_path = _project_path_without_symlinks(
        project / SEED_MANIFEST, project, label="seed isolation manifest"
    )
    seed, seed_payload = _read_json(seed_path, label="seed isolation manifest")
    if _sha256_bytes(seed_payload) != seal.get("seed_manifest_sha256"):
        _fail("seed isolation manifest hash does not match controller seal")
    if (
        seed.get("schema_version") != 1
        or seed.get("protocol") != "icho-problem-only-solver-seed-v1"
        or seed.get("source_revision_disclosed") is not False
        or seed.get("isolation_claims") != {"filesystem": True, "network": False}
    ):
        _fail("seed isolation manifest has invalid blind-boundary metadata")
    payload_index = _validated_hash_map(seed.get("payload_files"), label="seed payload_files")
    if seed.get("payload_sha256") != _hash_index(payload_index):
        _fail("seed payload index hash is invalid")
    bundle_spec = seed.get("blind_bundle")
    if not isinstance(bundle_spec, dict):
        _fail("seed isolation manifest has no blind_bundle object")
    relative_bundle = bundle_path.relative_to(project).as_posix()
    controller_bundle = seal["blind_bundle"]
    assert isinstance(controller_bundle, Mapping)
    if (
        bundle_spec.get("path") != relative_bundle
        or bundle_spec.get("sha256") != _sha256_bytes(bundle_payload)
        or bundle_spec.get("row_count") != controller_bundle.get("row_count")
        or seed.get("blind_bundle_sha256") != _sha256_bytes(bundle_payload)
        or payload_index.get(relative_bundle) != _sha256_bytes(bundle_payload)
    ):
        _fail("seed manifest blind bundle binding is stale or mismatched")
    if seed.get("target_ids") != controller_bundle.get("ids"):
        _fail("seed manifest target_ids do not match controller bundle IDs")
    if seed.get("target_ids_sha256") != _sha256_bytes(
        _json_bytes(controller_bundle.get("ids"))
    ):
        _fail("seed manifest target_ids digest is invalid")
    for relative, expected in payload_index.items():
        if relative in _MUTABLE_SEED_PATHS:
            continue
        path = _resolve_project_locator(project, relative, label="sealed seed payload")
        actual = _sha256_bytes(_read_plain_bytes(path, label="sealed seed payload"))
        if actual != expected:
            _fail(f"seed payload hash drift detected: {relative}")

    artifacts = [
        _artifact(
            project=project,
            path=seed_path,
            kind="seed_isolation_manifest",
            payload=seed_payload,
        )
    ]
    for relative, expected in sorted(payload_index.items()):
        path = _resolve_project_locator(project, relative, label="sealed seed payload")
        payload = _read_plain_bytes(path, label="sealed seed payload")
        if relative not in _MUTABLE_SEED_PATHS and _sha256_bytes(payload) != expected:
            _fail(f"seed payload hash drift detected: {relative}")
        artifacts.append(
            _artifact(
                project=project,
                path=path,
                kind=(
                    "questions_only_bundle"
                    if path == bundle_path
                    else "problem_image"
                    if relative.startswith("icho_2026_source/image/")
                    else "problem_pdf"
                    if relative.startswith("icho_2026_source/raw/")
                    else "sealed_seed_payload"
                ),
                payload=payload,
            )
        )
    generated = seal["generated_files"]
    assert isinstance(generated, Mapping)
    for relative in sorted(generated):
        path = _resolve_project_locator(project, relative, label="controller-generated file")
        payload = _read_plain_bytes(path, label="controller-generated file")
        if _sha256_bytes(payload) != generated[relative]:
            _fail(f"controller-generated file hash drift detected: {relative}")
        artifacts.append(
            _artifact(
                project=project,
                path=path,
                kind={
                    CONFIG_FILE: "answer_blind_config",
                    MCP_FILE: "answer_blind_mcp_config",
                    PROTOCOL_FILE: "answer_blind_protocol",
                    AGENTS_FILE: "answer_blind_agents_policy",
                }[relative],
                payload=payload,
            )
        )
    config, _ = _read_json(project / CONFIG_FILE, label="answer-blind config")
    metadata = config.get("answer_blind")
    if not isinstance(metadata, dict) or (
        metadata.get("protocol") != PROTOCOL
        or metadata.get("phase") != "solve"
        or metadata.get("official_answer_seen") is not False
        or metadata.get("isolation")
        != {"filesystem_answer_blind": True, "network_answer_blind": False}
    ):
        _fail("answer-blind config metadata is invalid")
    return artifacts


def _controller_context(
    *, project: Path, controller_seal: Path | str, expected_controller_seal_sha256: str
) -> dict[str, Any]:
    _seal_path, seal, seal_payload = _load_controller_seal(
        project=project,
        path=controller_seal,
        expected_sha256=expected_controller_seal_sha256,
    )
    bundle_path, bundle_payload, bundle_records = _parse_blind_bundle(
        project=project, seal=seal
    )
    root_artifacts = _validate_seed_and_root_files(
        project=project,
        seal=seal,
        bundle_path=bundle_path,
        bundle_payload=bundle_payload,
    )
    snapshot_inventory = _validate_snapshot_inventory(seal, project=project)
    verifier_snapshot_root, verifier_snapshot_files = _validate_verifier_snapshot(
        seal, project=project
    )
    structured_receipt, structured_payload, structured_targets = (
        _load_and_validate_structured_solver(
            project=project, seal=seal, bundle_records=bundle_records
        )
    )
    (
        verifier_invocation,
        verifier_invocation_payload,
        verifier_receipt,
        verifier_payload,
    ) = _load_and_validate_verifier_invocation(project=project, seal=seal)
    (
        review_aggregate,
        review_aggregate_payload,
        source_first_commitment,
        source_first_commitment_payload,
        independent_review,
        independent_review_payload,
        source_first_input_files,
        artifact_review_input_files,
        source_first_records,
        source_first_records_payload,
    ) = _load_independent_review_invocation(project=project, seal=seal)
    return {
        "seal": seal,
        "seal_sha256": _sha256_bytes(seal_payload),
        "bundle_path": bundle_path,
        "bundle_payload": bundle_payload,
        "bundle_records": bundle_records,
        "scope_ids": list(seal["freeze_scope"]["ids"]),
        "root_artifacts": root_artifacts,
        "snapshot_inventory": snapshot_inventory,
        "verifier_snapshot_root": verifier_snapshot_root,
        "verifier_snapshot_files": verifier_snapshot_files,
        "structured_solver_receipt": structured_receipt,
        "structured_solver_receipt_sha256": _sha256_bytes(structured_payload),
        "structured_solver_targets": structured_targets,
        "verifier_invocation": verifier_invocation,
        "verifier_invocation_sha256": _sha256_bytes(verifier_invocation_payload),
        "verifier_receipt": verifier_receipt,
        "verifier_receipt_sha256": _sha256_bytes(verifier_invocation_payload),
        "lean_verifier_result_sha256": _sha256_bytes(verifier_payload),
        "independent_review_invocation": review_aggregate,
        "source_first_commitment": source_first_commitment,
        "independent_review_receipt": independent_review,
        "independent_review_receipt_sha256": _sha256_bytes(
            review_aggregate_payload
        ),
        "source_first_commitment_sha256": _sha256_bytes(
            source_first_commitment_payload
        ),
        "source_first_records": source_first_records,
        "source_first_records_sha256": _sha256_bytes(
            source_first_records_payload
        ),
        "independent_review_semantic_sha256": _sha256_bytes(
            independent_review_payload
        ),
        "source_first_input_files": source_first_input_files,
        "artifact_review_input_files": artifact_review_input_files,
    }


def _expected_report_entry(
    *, project: Path, bundle_row: Mapping[str, Any], blind_hash: str
) -> dict[str, Any]:
    """Rebuild the deterministic answer-blind ingestion projection."""
    expected = dict(bundle_row)
    # ``physics-formalize`` hashes the canonical input row first, then stores
    # the normalized native entry with surrounding question whitespace
    # stripped.  Replay that deterministic ingestion step here while keeping
    # ``blind_hash`` bound to the unmodified bundle row.
    expected["question"] = str(bundle_row.get("question") or "").strip()
    expected["blind_record_sha256"] = blind_hash
    images = bundle_row.get("images")
    if not isinstance(images, list) or not images:
        _fail(f"bundle row {bundle_row.get('id')} has no image inventory")
    locators: list[str] = []
    for raw in images:
        if not isinstance(raw, str) or not raw.strip():
            _fail(f"bundle row {bundle_row.get('id')} has an invalid image locator")
        path = _resolve_project_locator(
            project,
            f"icho_2026_source/image/{raw}",
            label="bundle problem image",
        )
        locator = path.relative_to(project).as_posix()
        if locator not in locators:
            locators.append(locator)
    expected["image"] = str(bundle_row.get("image") or images[0])
    expected["image_paths"] = locators
    expected["image_path"] = locators[0]
    return expected


def _source_first_projection(bundle_row: Mapping[str, Any]) -> dict[str, Any]:
    """Build the only source record visible before artifact evaluation.

    The raw ingestion report is deliberately excluded because it carries
    solver-side locators such as ``output_lean``.  This projection is rebuilt
    from the hash-bound questions-only bundle by both controller and freezer.
    """
    projection = {
        "schema_version": bundle_row.get("schema_version"),
        "protocol": bundle_row.get("protocol"),
        "evaluation_mode": bundle_row.get("evaluation_mode"),
        "official_answer_seen": bundle_row.get("official_answer_seen"),
        "phase": "source_first_review",
        "id": bundle_row.get("id"),
        "current_question": bundle_row.get("current_question"),
        "shared_context": bundle_row.get("shared_context"),
        "previous_parts": bundle_row.get("previous_parts"),
        "images": bundle_row.get("images"),
        "problem_assets": bundle_row.get("problem_assets"),
        "requested_outputs": bundle_row.get("requested_outputs"),
        "reporting_policy": bundle_row.get("reporting_policy"),
        "measurement_policy": bundle_row.get("measurement_policy"),
        "candidate_domain_policy": bundle_row.get("candidate_domain_policy"),
    }
    _strict_fields(
        projection, _SOURCE_FIRST_PROJECTION_FIELDS,
        label=f"source-first projection {bundle_row.get('id')}",
    )
    if (
        projection["schema_version"] != SCHEMA_VERSION
        or projection["protocol"] != PROTOCOL
        or projection["evaluation_mode"] != "answer_blind"
        or projection["official_answer_seen"] is not False
    ):
        _fail("source-first projection has invalid answer-blind metadata")
    for field in ("id", "current_question"):
        _require_nonempty_string(
            projection.get(field), field=f"source-first projection.{field}"
        )
    if not isinstance(projection.get("shared_context"), str):
        _fail("source-first projection shared_context must be a string")
    previous = projection.get("previous_parts")
    if not isinstance(previous, list):
        _fail("source-first projection previous_parts must be a list")
    previous_fields = {"source_id", "part_id", "question", "dependency_policy"}
    for item in previous:
        if not isinstance(item, Mapping):
            _fail("source-first projection previous part must be an object")
        _strict_fields(item, previous_fields, label="source-first previous part")
        for field in ("source_id", "part_id", "question", "dependency_policy"):
            _require_nonempty_string(
                item.get(field), field=f"source-first previous part.{field}"
            )
    if not isinstance(projection.get("images"), list) or not projection["images"]:
        _fail("source-first projection requires problem images")
    if not isinstance(projection.get("problem_assets"), list):
        _fail("source-first projection problem_assets must be a list")
    for field in (
        "requested_outputs", "reporting_policy", "measurement_policy",
        "candidate_domain_policy",
    ):
        value = projection.get(field)
        if not isinstance(value, (list, Mapping)) or not value:
            _fail(f"source-first projection {field} is missing")
    leakage = _find_leakage_keys(projection, path="source_first_projection")
    if leakage:
        _fail(
            "source-first projection contains answer-bearing metadata: "
            + ", ".join(leakage)
        )
    return projection


def _strict_candidate_inventory(
    directory: Path, *, expected_names: set[str]
) -> None:
    actual_names: set[str] = set()
    for child in directory.iterdir():
        if child.is_symlink() or not child.is_file():
            _fail(f"candidate directory contains an unsafe entry: {child.name}")
        actual_names.add(child.name)
    missing = sorted(expected_names - actual_names)
    extra = sorted(actual_names - expected_names)
    if missing or extra:
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        _fail("candidate/source-report set is not one-to-one: " + "; ".join(details))


_STANDARD_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
_AXIOM_LIST_RE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")


def _lean_module_name(target: Path, project: Path) -> str:
    try:
        relative = target.resolve().relative_to(project.resolve()).with_suffix("")
    except ValueError:
        _fail(f"Lean verifier target escapes project: {target}")
    if not relative.parts or any(
        not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part)
        for part in relative.parts
    ):
        _fail(f"Lean verifier target is not an importable module: {relative}")
    return ".".join(relative.parts)


def _require_root_owned_readonly(path: Path, *, label: str) -> None:
    try:
        metadata = path.stat(follow_symlinks=False)
    except OSError as exc:
        _fail(f"cannot stat {label} {path}: {exc}")
    if metadata.st_uid != 0 or metadata.st_mode & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable: {path}")


def _assert_root_owned_readonly_tree(
    root: Path, *, label: str, allowed_symlink: Path | None = None
) -> None:
    _require_root_owned_readonly(root, label=label)
    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            if child.is_symlink():
                if allowed_symlink is None or child.resolve() != allowed_symlink.resolve():
                    _fail(f"{label} contains an unapproved symlink: {child}")
                if child.lstat().st_uid != 0:
                    _fail(f"{label} symlink is not root-owned: {child}")
                continue
            _require_root_owned_readonly(child, label=f"{label} directory")
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            child = base / name
            if child.is_symlink():
                try:
                    resolved = child.resolve(strict=True)
                    resolved.relative_to(root.resolve())
                except (OSError, ValueError) as exc:
                    _fail(f"{label} contains an escaping/broken symlink: {child}: {exc}")
                if child.lstat().st_uid != 0:
                    _fail(f"{label} symlink is not root-owned: {child}")
                continue
            _require_root_owned_readonly(child, label=f"{label} file")


def _parse_axioms(section: str, *, declaration: str) -> list[str]:
    matches = list(_AXIOM_LIST_RE.finditer(section))
    no_axiom_matches = list(
        re.finditer(r"does not depend on any axioms", section)
    )
    if len(matches) + len(no_axiom_matches) != 1:
        _fail(
            f"Lean emitted ambiguous #print axioms evidence for {declaration}"
        )
    if matches:
        match = matches[0]
        axioms = sorted(
            item.strip().strip("'\"")
            for item in match.group(1).split(",")
            if item.strip()
        )
    elif no_axiom_matches:
        axioms = []
    else:
        _fail(f"could not parse #print axioms output for {declaration}")
    unexpected = sorted(set(axioms) - _STANDARD_LEAN_AXIOMS)
    if unexpected:
        _fail(
            f"Lean result declaration {declaration} depends on non-standard axiom(s): "
            + ", ".join(unexpected)
        )
    return axioms


def _copy_clean_lean_sources(*, project: Path, destination: Path, dependency: Path) -> None:
    """Create a verifier-owned source-only project with sealed dependencies.

    Solver-produced Lake configuration, build output and compiled modules are
    intentionally never copied.  The verifier generates its own disposable
    build state below ``destination``.
    """

    destination.mkdir(mode=0o700)
    root_files = {"lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"}
    copied_root_config = False
    for source in sorted(project.rglob("*")):
        if source.is_symlink() or not source.is_file():
            continue
        relative = source.relative_to(project)
        if any(part in {".git", ".lake"} for part in relative.parts):
            continue
        if source.suffix != ".lean" and relative.as_posix() not in root_files:
            continue
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        copied_root_config = copied_root_config or relative.name in {"lakefile.toml", "lakefile.lean"}
    if not copied_root_config:
        _fail("sealed verifier snapshot contains no Lake project configuration")
    lake_dir = destination / ".lake"
    lake_dir.mkdir(mode=0o700)
    (lake_dir / "packages").symlink_to(dependency, target_is_directory=True)


def _run_clean_lean_result_checks(
    *,
    runtime_path: Path,
    project_path: Path,
    dependency_path: Path,
    output_parent: Path,
    timeout_s: int,
    pending: list[dict[str, Any]],
) -> tuple[dict[str, tuple[bytes, bytes, list[dict[str, Any]]]], bytes, bytes]:
    """Compile sealed source plus trusted checks in a disposable clean build."""

    results: dict[str, tuple[bytes, bytes, list[dict[str, Any]]]] = {}
    aggregate_stdout = b""
    aggregate_stderr = b""
    environment = {
        "HOME": str(output_parent),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": f"{runtime_path.parent}:/usr/bin:/bin",
        "TMPDIR": str(output_parent),
    }
    try:
        with tempfile.TemporaryDirectory(
            prefix="blind-lean-clean-", dir=output_parent
        ) as temporary:
            clean_project = Path(temporary) / "project"
            _copy_clean_lean_sources(
                project=project_path,
                destination=clean_project,
                dependency=dependency_path,
            )
            seed_build = subprocess.run(
                [str(runtime_path), "build", "IChO2026Chem"],
                cwd=clean_project,
                env=environment,
                capture_output=True,
                timeout=timeout_s,
                check=False,
            )
            build_stdout = seed_build.stdout or b""
            build_stderr = seed_build.stderr or b""
            if not isinstance(build_stdout, bytes):
                build_stdout = str(build_stdout).encode("utf-8")
            if not isinstance(build_stderr, bytes):
                build_stderr = str(build_stderr).encode("utf-8")
            aggregate_stdout += b"__ARCHON_CLEAN_SEED_BUILD__\0" + build_stdout
            aggregate_stderr += b"__ARCHON_CLEAN_SEED_BUILD__\0" + build_stderr
            if seed_build.returncode != 0:
                combined = (build_stdout + b"\n" + build_stderr).decode(
                    "utf-8", errors="replace"
                )
                _fail(
                    "Lean verifier could not create a clean sealed seed build: "
                    + combined[-2000:].strip()
                )

            probe_root = clean_project / ".archon-verifier"
            probe_root.mkdir(mode=0o700)
            for item in pending:
                record_id = str(item["id"])
                target_payload = item["target_payload"]
                contracts = item["contracts"]
                assert isinstance(target_payload, bytes) and isinstance(contracts, list)
                raw_target = item.get("target")
                if isinstance(raw_target, str) and raw_target:
                    relative_target = Path(raw_target)
                else:
                    safe_record = re.sub(r"[^A-Za-z0-9_]", "_", record_id)
                    relative_target = Path("Problems") / f"VerifierTarget_{safe_record}.lean"
                if (
                    relative_target.is_absolute()
                    or relative_target.suffix != ".lean"
                    or ".." in relative_target.parts
                ):
                    _fail(f"Lean verifier has an invalid target locator for {record_id}")
                clean_target = clean_project / relative_target
                clean_target.parent.mkdir(parents=True, exist_ok=True)
                clean_target.write_bytes(target_payload)
                module = _lean_module_name(clean_target, clean_project)
                olean = (
                    clean_project / ".lake/build/lib/lean"
                    / relative_target.with_suffix(".olean")
                )
                olean.parent.mkdir(parents=True, exist_ok=True)
                target_build = subprocess.run(
                    [
                        str(runtime_path), "env", "lean", "-o", str(olean),
                        str(clean_target),
                    ],
                    cwd=clean_project,
                    env=environment,
                    capture_output=True,
                    timeout=timeout_s,
                    check=False,
                )
                target_stdout = target_build.stdout or b""
                target_stderr = target_build.stderr or b""
                if not isinstance(target_stdout, bytes):
                    target_stdout = str(target_stdout).encode("utf-8")
                if not isinstance(target_stderr, bytes):
                    target_stderr = str(target_stderr).encode("utf-8")
                aggregate_stdout += (
                    record_id.encode("utf-8") + b"\0__ARCHON_TARGET_BUILD__\0"
                    + target_stdout
                )
                aggregate_stderr += (
                    record_id.encode("utf-8") + b"\0__ARCHON_TARGET_BUILD__\0"
                    + target_stderr
                )
                if target_build.returncode != 0:
                    combined = (target_stdout + b"\n" + target_stderr).decode(
                        "utf-8", errors="replace"
                    )
                    _fail(
                        f"Lean verifier could not clean-compile {record_id}: "
                        + combined[-2000:].strip()
                    )
                probe_lines = [
                    f"import {module}",
                    "",
                    "/- Trusted isolated result checks. -/",
                ]
                markers: list[tuple[str, str]] = []
                for index, result_contract in enumerate(contracts):
                    declaration = str(result_contract["declaration"])
                    expected_type = str(result_contract["expected_type"])
                    nonce = secrets.token_hex(24)
                    begin = f"__ARCHON_RESULT_BEGIN_{index}_{nonce}__"
                    end = f"__ARCHON_RESULT_END_{index}_{nonce}__"
                    markers.append((begin, end))
                    probe_lines.extend([
                        f'#eval IO.println "{begin}"',
                        f"#check {declaration}",
                        f"example : ({expected_type}) := {declaration}",
                        f"#print axioms {declaration}",
                        f'#eval IO.println "{end}"',
                        "",
                    ])
                probe = probe_root / f"ResultContractProbe_{record_id}.lean"
                probe.write_bytes("\n".join(probe_lines).encode("utf-8"))
                completed = subprocess.run(
                    [str(runtime_path), "env", "lean", str(probe)],
                    cwd=clean_project,
                    env=environment,
                    capture_output=True,
                    timeout=timeout_s,
                    check=False,
                )
                stdout = completed.stdout or b""
                stderr = completed.stderr or b""
                if not isinstance(stdout, bytes):
                    stdout = str(stdout).encode("utf-8")
                if not isinstance(stderr, bytes):
                    stderr = str(stderr).encode("utf-8")
                aggregate_stdout += record_id.encode("utf-8") + b"\0" + stdout
                aggregate_stderr += record_id.encode("utf-8") + b"\0" + stderr
                combined = (stdout + b"\n" + stderr).decode("utf-8", errors="replace")
                if completed.returncode != 0:
                    _fail(
                        f"Lean verifier rejected {record_id}: "
                        + combined[-2000:].strip()
                    )
                checks: list[dict[str, Any]] = []
                for index, result_contract in enumerate(contracts):
                    begin, end = markers[index]
                    if begin not in combined or end not in combined:
                        _fail(f"Lean verifier output markers are incomplete for {record_id}")
                    section = combined.split(begin, 1)[1].split(end, 1)[0]
                    checks.append({
                        "role": result_contract["role"],
                        "declaration": result_contract["declaration"],
                        "normalized_type_sha256": result_contract["expected_type_sha256"],
                        "result_payload_sha256": result_contract["result_payload_sha256"],
                        "axioms": _parse_axioms(
                            section, declaration=str(result_contract["declaration"])
                        ),
                        "compiled": True,
                    })
                results[record_id] = (stdout, stderr, checks)
    except subprocess.TimeoutExpired:
        _fail("Lean verifier clean build/check timed out")
    except OSError as exc:
        _fail(f"Lean verifier could not execute its clean build/check: {exc}")
    return results, aggregate_stdout, aggregate_stderr


def verify_blind_lean(
    *,
    project: Path | str,
    candidate_dir: Path | str,
    output: Path | str,
    runtime_executable: Path | str,
    runtime_root: Path | str,
    dependency_root: Path | str,
    expected_dependency_inventory_sha256: str,
    expected_runtime_inventory_sha256: str,
    expected_snapshot_inventory_sha256: str,
    scope_ids: Iterable[str],
    timeout_s: int = 300,
) -> dict[str, Any]:
    """Run Lean only as a non-root verifier and emit a hash-bound receipt."""
    verifier_uid = os.geteuid()
    if verifier_uid == 0:
        _fail("Lean verification refuses to run as root")
    if not isinstance(timeout_s, int) or isinstance(timeout_s, bool) or timeout_s < 1:
        _fail("Lean verifier timeout_s must be positive")
    project_path = _project_path(project)
    dependency_path = Path(dependency_root).resolve()
    if not dependency_path.is_dir() or dependency_path.is_symlink():
        _fail("Lean verifier dependency root must be a regular directory")
    _outside_project(dependency_path, project_path, label="Lean verifier dependency root")
    _assert_root_owned_readonly_tree(dependency_path, label="Lean dependency tree")
    _assert_root_owned_readonly_tree(
        project_path, label="Lean verifier snapshot", allowed_symlink=dependency_path
    )

    runtime_path = Path(runtime_executable).resolve()
    if not runtime_path.is_absolute() or runtime_path.is_symlink() or not runtime_path.is_file():
        _fail("Lean verifier runtime must be an absolute regular executable")
    _outside_project(runtime_path, project_path, label="Lean verifier runtime")
    _require_root_owned_readonly(runtime_path, label="Lean verifier runtime")
    if not os.access(runtime_path, os.X_OK):
        _fail("Lean verifier runtime is not executable")
    runtime_root_path = Path(runtime_root).resolve()
    if not runtime_root_path.is_dir() or runtime_root_path.is_symlink():
        _fail("Lean verifier runtime root must be a regular directory")
    _outside_project(runtime_root_path, project_path, label="Lean verifier runtime root")
    _assert_root_owned_readonly_tree(runtime_root_path, label="answer-blind runtime")
    try:
        runtime_relative = runtime_path.relative_to(runtime_root_path).as_posix()
    except ValueError:
        _fail("Lean verifier executable is outside the supplied runtime root")

    dependency_inventory = _regular_file_inventory(
        dependency_path,
        label="Lean dependency tree",
        require_controller_owner=False,
    )
    dependency_digest = _hash_index(dependency_inventory)
    if dependency_digest != _require_sha256(
        expected_dependency_inventory_sha256,
        field="expected_dependency_inventory_sha256",
    ):
        _fail("Lean verifier dependency inventory differs from controller expectation")
    runtime_inventory = _regular_file_inventory(
        runtime_root_path,
        label="answer-blind runtime",
        require_controller_owner=False,
        exclude_roots=(dependency_path,),
    )
    runtime_digest = _hash_index(runtime_inventory)
    if runtime_digest != _require_sha256(
        expected_runtime_inventory_sha256,
        field="expected_runtime_inventory_sha256",
    ):
        _fail("Lean verifier runtime inventory differs from controller expectation")
    runtime_sha = _sha256_bytes(
        _read_plain_bytes(runtime_path, label="Lean verifier runtime")
    )
    if runtime_inventory.get(runtime_relative) != runtime_sha:
        _fail("Lean verifier executable is absent from the runtime inventory")
    snapshot_inventory = _project_snapshot_inventory(
        project_path,
        dependency_root=dependency_path,
        require_controller_owner=False,
    )
    snapshot_digest = _hash_index(snapshot_inventory)
    if snapshot_digest != _require_sha256(
        expected_snapshot_inventory_sha256,
        field="expected_snapshot_inventory_sha256",
    ):
        _fail("Lean verifier snapshot inventory differs from controller expectation")

    ids = _strict_id_list(sorted(scope_ids), label="Lean verifier scope_ids")
    reports_by_id: dict[str, tuple[Path, dict[str, Any], bytes]] = {}
    for report_path, report, report_payload in _discover_blind_reports(project_path):
        entry = report.get("entry")
        if not isinstance(entry, dict):
            _fail(f"Lean verifier source report has no entry: {report_path}")
        record_id = _require_nonempty_string(entry.get("id"), field="source report entry.id")
        if record_id in reports_by_id:
            _fail(f"duplicate Lean verifier source report id: {record_id}")
        reports_by_id[record_id] = (report_path, report, report_payload)
    if sorted(reports_by_id) != ids:
        _fail("Lean verifier source-report set differs from declared scope")

    candidates_path = Path(candidate_dir)
    if not candidates_path.is_absolute():
        candidates_path = project_path / candidates_path
    candidates_path = _project_path_without_symlinks(
        candidates_path, project_path, label="Lean verifier candidate directory"
    )
    _strict_candidate_inventory(
        candidates_path, expected_names={f"{record_id}.json" for record_id in ids}
    )

    output_path = Path(output)
    if not output_path.is_absolute():
        output_path = Path.cwd() / output_path
    output_path = _outside_project(output_path, project_path, label="Lean verifier receipt")
    if output_path.parent.is_symlink() or not output_path.parent.is_dir():
        _fail("Lean verifier receipt parent must be an existing regular directory")
    if output_path.exists() or output_path.is_symlink():
        _fail("Lean verifier receipt output must be new")

    pending: list[dict[str, Any]] = []
    for record_id in ids:
        _report_path, report, _report_payload = reports_by_id[record_id]
        blind_hash = _require_sha256(
            report.get("blind_record_sha256"), field=f"source report {record_id} blind hash"
        )
        candidate_path = candidates_path / f"{record_id}.json"
        candidate, candidate_payload = _read_json(candidate_path, label="blind candidate")
        _validate_candidate(candidate, expected_id=record_id, expected_blind_hash=blind_hash)
        entry = report.get("entry")
        assert isinstance(entry, Mapping)
        _validate_candidate_source_policies(
            candidate, source_entry=entry, record_id=record_id
        )
        target_path = _resolve_project_locator(
            project_path, report.get("output_lean"), label="Lean verifier target"
        )
        target_payload = _validate_lean_target(
            target_path,
            project=project_path,
            declarations=candidate["lean_declarations"],
            raw_expression=(
                str(candidate["raw_result"].get("lean_expression") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("raw_result"), Mapping)
                else None
            ),
            derivation_spec=(
                str(candidate["raw_result"].get("derivation_spec") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("raw_result"), Mapping)
                else None
            ),
            reported_value=(
                str(candidate["reported_result"].get("value") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("reported_result"), Mapping)
                else None
            ),
        )
        contract = build_review_source_contract(
            project_path=project_path, target=target_path
        )
        if not is_answer_blind_contract(contract) or not contract.get("valid"):
            _fail(f"Lean verifier source contract is invalid for {record_id}")
        provenance = source_contract_provenance(contract)
        pending.append({
            "id": record_id,
            "target_payload": target_payload,
            "contracts": candidate["lean_result_contracts"],
            "target": target_path.relative_to(project_path).as_posix(),
            "target_sha256": _sha256_bytes(target_payload),
            "candidate": candidate_path.relative_to(project_path).as_posix(),
            "candidate_sha256": _sha256_bytes(candidate_payload),
            "source_contract_sha256": _sha256_bytes(_json_bytes(provenance)),
            "result_contracts_sha256": _sha256_bytes(
                _json_bytes(candidate["lean_result_contracts"])
            ),
        })

    # Only after every untrusted target has passed the mechanical source/import
    # scan do we elaborate any of them.  The helper builds trusted seed modules
    # from source in verifier-private storage and appends checks directly to a
    # byte-for-byte copy of each sealed target; it never imports a solver .olean.
    check_results, verifier_stdout, verifier_stderr = _run_clean_lean_result_checks(
        runtime_path=runtime_path,
        project_path=project_path,
        dependency_path=dependency_path,
        output_parent=output_path.parent,
        timeout_s=timeout_s,
        pending=pending,
    )
    record_receipts: list[dict[str, Any]] = []
    for item in pending:
        record_id = str(item["id"])
        result = check_results.get(record_id)
        if result is None:
            _fail(f"Lean verifier clean result is missing {record_id}")
        _stdout, _stderr, checks = result
        record_receipts.append({
            key: value
            for key, value in item.items()
            if key not in {"target_payload", "contracts"}
        } | {"checks": checks})

    receipt: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "phase": VERIFIER_PHASE,
        "evaluation_mode": "answer_blind",
        "verifier_uid": verifier_uid,
        "network_answer_blind": False,
        "runtime_executable": {
            "path": str(runtime_path),
            "sha256": runtime_sha,
        },
        "dependency_inventory_sha256": dependency_digest,
        "runtime_inventory_sha256": runtime_digest,
        "snapshot_inventory_sha256": snapshot_digest,
        "scope_ids": ids,
        "records": record_receipts,
        "compiled": True,
        "stdout_sha256": _sha256_bytes(verifier_stdout),
        "stderr_sha256": _sha256_bytes(verifier_stderr),
    }
    _validate_verifier_receipt(
        receipt,
        seal={
            "dependency_inventory": {"files_sha256": dependency_digest},
            "runtime_inventory": {
                "root": str(runtime_root_path),
                "files": runtime_inventory,
                "files_sha256": runtime_digest,
            },
            "snapshot_inventory": {"files_sha256": snapshot_digest},
            "freeze_scope": {"ids": ids},
        },
    )
    _atomic_write_new(output_path, _json_bytes(receipt))
    return receipt


def _require_trusted_controller_runtime(project: Path) -> None:
    for label, raw in (
        ("blind evaluation runtime", __file__),
        ("source-contract runtime", build_review_source_contract.__code__.co_filename),
        ("sorry-count runtime", file_open_sorry_count.__code__.co_filename),
    ):
        path = Path(raw).resolve()
        _outside_project(path, project, label=label)
        _require_controller_owned_readonly(path, label=label)


def _verifier_records(receipt: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    records = receipt.get("records")
    assert isinstance(records, list)
    return {str(row["id"]): row for row in records if isinstance(row, dict)}


def _validate_verifier_record_against_current(
    *,
    record_id: str,
    verifier: Mapping[str, Any],
    target_path: Path,
    target_payload: bytes,
    candidate_path: Path,
    candidate_payload: bytes,
    candidate: Mapping[str, Any],
    source_contract: Mapping[str, Any],
    project: Path,
) -> dict[str, Any]:
    row = _verifier_records(verifier).get(record_id)
    if row is None:
        _fail(f"Lean verifier receipt is missing {record_id}")
    expected_target = target_path.relative_to(project).as_posix()
    expected_candidate = candidate_path.relative_to(project).as_posix()
    expected_values = {
        "target": expected_target,
        "target_sha256": _sha256_bytes(target_payload),
        "candidate": expected_candidate,
        "candidate_sha256": _sha256_bytes(candidate_payload),
        "source_contract_sha256": _sha256_bytes(_json_bytes(source_contract)),
        "result_contracts_sha256": _sha256_bytes(
            _json_bytes(candidate["lean_result_contracts"])
        ),
    }
    for field, expected in expected_values.items():
        if row.get(field) != expected:
            _fail(f"Lean verifier receipt is stale for {record_id}: {field}")
    by_role = {
        str(item.get("role")): item
        for item in row["checks"]
        if isinstance(item, Mapping)
    }
    for contract in candidate["lean_result_contracts"]:
        role = str(contract["role"])
        check = by_role.get(role)
        if check is None or (
            check.get("declaration") != contract.get("declaration")
            or check.get("normalized_type_sha256")
            != contract.get("expected_type_sha256")
            or check.get("result_payload_sha256")
            != contract.get("result_payload_sha256")
            or check.get("compiled") is not True
        ):
            _fail(f"Lean verifier result contract is stale for {record_id}:{role}")
    return dict(row)


def _validate_independent_review_record_against_current(
    *,
    source_row: object,
    row: object,
    record_id: str,
    blind_record_sha256: str,
    bundle_row: Mapping[str, Any],
    target_path: Path,
    target_payload: bytes,
    candidate: Mapping[str, Any],
    candidate_payload: bytes,
    report_payload: bytes,
    blueprint_payload: bytes,
    source_contract: Mapping[str, Any],
    requested_outputs: object,
) -> None:
    if not isinstance(source_row, Mapping) or source_row.get("id") != record_id:
        _fail(f"source-first commitment is missing current record {record_id}")
    requested_hash = _sha256_bytes(_json_bytes(requested_outputs))
    source_projection = _source_first_projection(bundle_row)
    if (
        source_row.get("blind_record_sha256") != blind_record_sha256
        or source_row.get("source_record_sha256")
        != _sha256_bytes(_json_bytes(source_projection))
        or source_row.get("requested_outputs_sha256") != requested_hash
    ):
        _fail(f"source-first commitment is stale for {record_id}")
    expected_outputs = requested_outputs
    committed_outputs = source_row.get("output_commitments")
    if not isinstance(expected_outputs, list) or not isinstance(committed_outputs, list):
        _fail(f"source-first requested outputs are invalid for {record_id}")
    projected_commitments = [
        {
            field: output.get(field)
            for field in ("id", "source_requirement", "kind", "unit", "reporting_policy")
        }
        for output in committed_outputs
        if isinstance(output, Mapping)
    ]
    projected_expected = [
        {
            field: output.get(field)
            for field in ("id", "source_requirement", "kind", "unit", "reporting_policy")
        }
        for output in expected_outputs
        if isinstance(output, Mapping)
    ]
    if projected_commitments != projected_expected or len(projected_expected) != len(
        expected_outputs
    ):
        _fail(
            f"source-first commitment does not exactly cover requested_outputs for {record_id}"
        )
    reporting_policy = bundle_row.get("reporting_policy")
    if not isinstance(reporting_policy, Mapping):
        _fail(f"source-first reporting policy is missing for {record_id}")
    if len(expected_outputs) == 1:
        candidate_values = {
            str(expected_outputs[0].get("id")): candidate.get("reported_result", {}).get(
                "value"
            )
        }
        candidate_raw_specs: Mapping[str, Any] = {
            str(expected_outputs[0].get("id")): candidate.get("raw_result", {})
        }
    else:
        candidate_values = candidate.get("reported_result", {}).get("value")
        candidate_raw_specs = candidate.get("raw_result", {}).get("value")
        if not isinstance(candidate_values, dict) or not isinstance(
            candidate_raw_specs, Mapping
        ):
            _fail(f"candidate multi-output binding is invalid for {record_id}")
    for expected_output, committed_output in zip(
        expected_outputs, committed_outputs, strict=True
    ):
        assert isinstance(expected_output, Mapping) and isinstance(committed_output, Mapping)
        output_id = str(expected_output.get("id"))
        spec = committed_output.get("result_spec")
        assert isinstance(spec, Mapping)
        if spec.get("status") == "underdetermined":
            candidate_item = candidate_values.get(output_id)
            if len(expected_outputs) == 1:
                candidate_underdetermined = candidate.get("result_kind") == "underdetermined"
            else:
                candidate_underdetermined = (
                    isinstance(candidate_item, Mapping)
                    and candidate_item.get("status") == "underdetermined"
                    and candidate_item.get("value") is None
                )
            if not candidate_underdetermined:
                _fail(
                    f"candidate contradicts source-first underdetermination for {record_id}/{output_id}"
                )
            continue
        candidate_item = candidate_values.get(output_id)
        if len(expected_outputs) > 1:
            if not isinstance(candidate_item, Mapping) or candidate_item.get("status") != "derived":
                _fail(f"candidate output is not derived for {record_id}/{output_id}")
            candidate_value = candidate_item.get("value")
            candidate_raw_spec = candidate_raw_specs.get(output_id)
            if not isinstance(candidate_raw_spec, Mapping):
                _fail(f"candidate raw output spec is missing for {record_id}/{output_id}")
        else:
            candidate_value = candidate_item
            candidate_raw_spec = candidate_raw_specs[output_id]
        if expected_output.get("kind") == "numeric":
            candidate_interval = candidate_raw_spec.get("certified_interval")
            committed_interval = spec.get("certified_interval")
            if not isinstance(candidate_interval, Mapping) or not isinstance(
                committed_interval, Mapping
            ):
                _fail(
                    f"candidate/source-first numeric interval is missing for "
                    f"{record_id}/{output_id}"
                )
            if (
                expected_output.get("reporting_policy", {}).get(
                    "tie_rule", reporting_policy.get("tie_rule")
                ) != spec.get("tie_rule")
                or _bounded_fraction(
                    candidate_value,
                    field=f"candidate {record_id}/{output_id} reported value",
                )
                != _bounded_fraction(
                    spec.get("reported_value"),
                    field=f"source-first {record_id}/{output_id} reported value",
                )
                or _bounded_fraction(
                    candidate_raw_spec.get("raw_value")
                    if len(expected_outputs) > 1
                    else candidate_raw_spec.get("value"),
                    field=f"candidate {record_id}/{output_id} raw value",
                )
                != _bounded_fraction(
                    spec.get("raw_value"),
                    field=f"source-first {record_id}/{output_id} raw value",
                )
                or any(
                    _bounded_fraction(
                        candidate_interval.get(bound),
                        field=f"candidate {record_id}/{output_id} interval {bound}",
                    )
                    != _bounded_fraction(
                        committed_interval.get(bound),
                        field=f"source-first {record_id}/{output_id} interval {bound}",
                    )
                    for bound in ("lower", "upper")
                )
                or str(
                    candidate_raw_spec.get("expression")
                    if len(expected_outputs) == 1
                    else candidate_raw_spec.get("raw_expression")
                ).strip()
                != str(spec.get("raw_expression")).strip()
            ):
                _fail(
                    f"candidate numeric result differs from source-first commitment for {record_id}/{output_id}"
                )
            reported_text = str(spec.get("reported_value"))
            try:
                expected_quantum = _rounding_quantum(
                    expected_output.get("reporting_policy"), Decimal(reported_text)
                )
            except InvalidOperation:
                expected_quantum = None
            if expected_quantum is None or _bounded_fraction(
                str(spec.get("reporting_quantum")),
                field="source-first reporting quantum",
            ) != Fraction(expected_quantum):
                _fail(
                    f"source-first reporting quantum does not match predeclared policy for {record_id}/{output_id}"
                )
        elif expected_output.get("kind") == "integer":
            committed_value = spec.get("value")
            if str(candidate_value) != str(committed_value):
                _fail(
                    f"candidate integer differs from source-first commitment for {record_id}/{output_id}"
                )
        elif expected_output.get("kind") in {"formula", "classification"}:
            if str(candidate_value) != str(spec.get("normalized_result")):
                _fail(
                    f"candidate symbolic result differs from source-first commitment for {record_id}/{output_id}"
                )
        elif expected_output.get("kind") == "finite_set":
            expected_text = json.dumps(
                spec.get("normalized_members"), ensure_ascii=False,
                sort_keys=True, separators=(",", ":"),
            )
            if candidate_value != spec.get("normalized_members") and str(
                candidate_value
            ) != expected_text:
                _fail(
                    f"candidate finite set differs from source-first commitment for {record_id}/{output_id}"
                )
    permitted_locators = {
        f"source.{field}"
        for field in ("current_question", "shared_context", "previous_parts")
        if field in source_projection
    }
    permitted_locators.update(
        f"image:{path}"
        for path in bundle_row.get("images", [])
        if isinstance(path, str) and path
    )
    givens = source_row.get("givens")
    assert isinstance(givens, list)
    if any(
        not isinstance(given, Mapping)
        or given.get("source_locator") not in permitted_locators
        for given in givens
    ):
        _fail(f"source-first commitment cites non-source material for {record_id}")
    if not isinstance(row, Mapping) or row.get("id") != record_id:
        _fail(f"independent Review receipt is missing current record {record_id}")
    expected_hashes = {
        "target_sha256": _sha256_bytes(target_payload),
        "candidate_sha256": _sha256_bytes(candidate_payload),
        "source_report_sha256": _sha256_bytes(report_payload),
        "blueprint_sha256": _sha256_bytes(blueprint_payload),
        "source_contract_sha256": _sha256_bytes(
            _json_bytes(source_contract_provenance(source_contract))
        ),
        "requested_outputs_sha256": requested_hash,
        "source_commitment_record_sha256": _sha256_bytes(_json_bytes(source_row)),
    }
    if row.get("target") != target_path.as_posix():
        # Controller receipts use the sanitized snapshot's project-relative target.
        expected_target = str(source_contract.get("target") or "")
        if row.get("target") != expected_target:
            _fail(f"independent Review target locator is stale for {record_id}")
    for field, expected in expected_hashes.items():
        if row.get(field) != expected:
            _fail(f"independent Review {field} is stale for {record_id}")
    provenance = source_contract_provenance(source_contract)
    formal = row.get("formalization_certificate")
    proof = row.get("proof_certificate")
    assert isinstance(formal, Mapping) and isinstance(proof, Mapping)
    _validate_gate_record(
        gate_name="formalization Review gate",
        record={"status": "passed", "certificate": dict(formal)},
        expected_status="passed",
        expected_provenance=provenance,
        expected_contract=source_contract,
        requested_outputs=requested_outputs,
    )
    _validate_gate_record(
        gate_name="proof Review gate",
        record={"status": "solved", **dict(proof)},
        expected_status="solved",
        expected_provenance=provenance,
        expected_contract=source_contract,
        requested_outputs=requested_outputs,
    )


def _build_current_freeze_manifest(
    *,
    project: Path,
    candidate_dir: Path | str,
    controller_seal: Path | str,
    expected_controller_seal_sha256: str,
    frozen_at: str,
) -> dict[str, Any]:
    _require_trusted_controller_runtime(project)
    context = _controller_context(
        project=project,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
    )
    seal = context["seal"]
    bundle_records = context["bundle_records"]
    scope_ids = context["scope_ids"]
    scope_set = set(scope_ids)
    verifier = context["verifier_receipt"]
    independent_review = context["independent_review_receipt"]
    source_first_commitment = context["source_first_commitment"]
    independent_rows = {
        str(row["id"]): row
        for row in independent_review["records"]
        if isinstance(row, Mapping)
    }
    source_first_rows = {
        str(row["id"]): row
        for row in source_first_commitment["records"]
        if isinstance(row, Mapping)
    }

    candidates_path = Path(candidate_dir)
    if not candidates_path.is_absolute():
        candidates_path = project / candidates_path
    candidates_path = _project_path_without_symlinks(
        candidates_path, project, label="candidate directory"
    )
    if not candidates_path.is_dir():
        _fail(f"candidate directory must be a regular project directory: {candidates_path}")

    formal_path, formal_gate, formal_payload = _load_gate(
        project, FORMALIZATION_GATE, label="formalization Review gate"
    )
    proof_path, proof_gate, proof_payload = _load_gate(
        project, PROOF_GATE, label="proof Review gate"
    )
    formal_targets = formal_gate["targets"]
    proof_targets = proof_gate["targets"]

    by_id: dict[str, tuple[Path, dict[str, Any], bytes]] = {}
    target_ids: dict[str, str] = {}
    for report_path, report, report_payload in _discover_blind_reports(project):
        if report.get("schema_version") != 3:
            _fail(f"answer-blind source report requires schema_version=3: {report_path}")
        if report.get("official_answer_seen") is not False or report.get("phase") != "solve":
            _fail(f"source report is not a blind solve artifact: {report_path}")
        leakage = _find_leakage_keys(report, path=f"report[{report_path.name}]")
        if leakage:
            _fail("answer-blind source report contains leakage field(s): " + ", ".join(leakage))
        entry = report.get("entry")
        if not isinstance(entry, dict):
            _fail(f"answer-blind source report has no entry object: {report_path}")
        record_id = _require_nonempty_string(entry.get("id"), field=f"{report_path}.entry.id")
        if record_id in by_id:
            _fail(f"duplicate answer-blind source report id: {record_id}")
        if record_id not in scope_set:
            _fail(f"answer-blind source report is outside controller scope: {record_id}")
        bundle_row, canonical_hash = bundle_records[record_id]
        blind_hash = _require_sha256(
            report.get("blind_record_sha256"), field=f"{report_path}.blind_record_sha256"
        )
        if blind_hash != canonical_hash:
            _fail(f"source report does not bind the canonical bundle row: {record_id}")
        expected_entry = _expected_report_entry(
            project=project, bundle_row=bundle_row, blind_hash=canonical_hash
        )
        if entry != expected_entry:
            _fail(f"source report entry differs from deterministic bundle projection: {record_id}")
        if report.get("previous_parts") != expected_entry.get("previous_parts", []):
            _fail(f"source report previous_parts differs from bundle row: {record_id}")
        target_path = _resolve_project_locator(
            project, report.get("output_lean"), label="source-report Lean target"
        )
        relative_target = target_path.relative_to(project).as_posix()
        if relative_target in target_ids:
            _fail(
                f"multiple source reports bind the same Lean target: "
                f"{target_ids[relative_target]}, {record_id}"
            )
        target_ids[relative_target] = record_id
        by_id[record_id] = (report_path, report, report_payload)

    if sorted(by_id) != scope_ids:
        _fail(
            "source-report ID set differs from controller freeze scope "
            f"(expected={scope_ids}, actual={sorted(by_id)})"
        )
    if set(formal_targets) != set(target_ids) or set(proof_targets) != set(target_ids):
        _fail("Review gate target sets must exactly equal the controller freeze scope")
    _strict_candidate_inventory(
        candidates_path,
        expected_names={f"{record_id}.json" for record_id in scope_ids},
    )

    records: list[dict[str, Any]] = []
    artifact_index: dict[str, dict[str, str]] = {}
    expected_artifact_review_input = {
        str(artifact["path"]): str(artifact["sha256"])
        for artifact in context["root_artifacts"]
    }
    expected_artifact_review_input[_SOURCE_COMMITMENT_INPUT] = context[
        "source_first_records_sha256"
    ]
    expected_source_first_input: dict[str, str] = {}

    def add_artifact(item: dict[str, str]) -> None:
        old = artifact_index.get(item["path"])
        if old is not None and old != item:
            _fail(f"artifact path was assigned conflicting hashes: {item['path']}")
        artifact_index[item["path"]] = item

    for artifact in context["root_artifacts"]:
        add_artifact(artifact)
    add_artifact(_artifact(
        project=project, path=formal_path, kind="formalization_review_gate",
        payload=formal_payload,
    ))
    add_artifact(_artifact(
        project=project, path=proof_path, kind="proof_review_gate", payload=proof_payload,
    ))

    for record_id in scope_ids:
        report_path, report, report_payload = by_id[record_id]
        bundle_row, blind_hash = bundle_records[record_id]
        candidate_path = candidates_path / f"{record_id}.json"
        candidate, candidate_payload = _read_json(candidate_path, label="blind candidate")
        _validate_candidate(candidate, expected_id=record_id, expected_blind_hash=blind_hash)
        _validate_candidate_source_policies(
            candidate, source_entry=bundle_row, record_id=record_id
        )

        target_path = _resolve_project_locator(project, report.get("output_lean"), label="Lean target")
        contract = build_review_source_contract(project_path=project, target=target_path)
        if not is_answer_blind_contract(contract) or not contract.get("valid"):
            errors = contract.get("errors") or ["invalid answer-blind source contract"]
            _fail(f"source contract is invalid for {record_id}: " + "; ".join(map(str, errors)))
        expected = source_contract_provenance(contract)
        if (
            expected.get("entry_id") != record_id
            or expected.get("blind_record_sha256") != blind_hash
        ):
            _fail(f"source contract bundle identity is stale for {record_id}")
        reviewed_candidate_path = _resolve_project_locator(
            project, expected.get("blind_candidate_record"), label="reviewed blind candidate"
        )
        if reviewed_candidate_path != candidate_path or (
            _sha256_bytes(candidate_payload) != expected.get("blind_candidate_sha256")
        ):
            _fail(f"reviewed candidate binding is stale for {record_id}")
        expected_report = _resolve_project_locator(
            project, expected.get("source_report"), label="source report"
        )
        if expected_report != report_path or _sha256_bytes(report_payload) != expected.get("source_sha256"):
            _fail(f"source report binding is stale for {record_id}")

        rel_target = str(expected["target"])
        _validate_gate_record(
            gate_name="formalization Review gate",
            record=formal_targets.get(rel_target), expected_status="passed",
            expected_provenance=expected, expected_contract=contract,
            requested_outputs=bundle_row.get("requested_outputs"),
        )
        _validate_gate_record(
            gate_name="proof Review gate",
            record=proof_targets.get(rel_target), expected_status="solved",
            expected_provenance=expected, expected_contract=contract,
            requested_outputs=bundle_row.get("requested_outputs"),
        )
        target_payload = _validate_lean_target(
            target_path,
            project=project,
            declarations=candidate["lean_declarations"],
            raw_expression=(
                str(candidate["raw_result"].get("lean_expression") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("raw_result"), Mapping)
                else None
            ),
            derivation_spec=(
                str(candidate["raw_result"].get("derivation_spec") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("raw_result"), Mapping)
                else None
            ),
            reported_value=(
                str(candidate["reported_result"].get("value") or "")
                if candidate.get("result_kind") == "numeric"
                and isinstance(candidate.get("reported_result"), Mapping)
                else None
            ),
        )
        if _sha256_bytes(target_payload) != expected.get("lean_sha256"):
            _fail(f"Lean target hash is stale for {record_id}")
        blueprint_path = _resolve_project_locator(
            project, expected.get("blueprint"), label="blueprint"
        )
        blueprint_payload = _read_plain_bytes(blueprint_path, label="blueprint")
        if _sha256_bytes(blueprint_payload) != expected.get("blueprint_sha256"):
            _fail(f"blueprint hash is stale for {record_id}")

        structured_target = context["structured_solver_targets"].get(record_id)
        if not isinstance(structured_target, Mapping):
            _fail(f"structured solver receipt is missing current target {record_id}")
        structured_artifacts = structured_target.get("artifacts")
        if not isinstance(structured_artifacts, Mapping):
            _fail(f"structured solver artifact binding is missing for {record_id}")
        expected_structured_artifacts = {
            "candidate": {
                "path": candidate_path.relative_to(project).as_posix(),
                "sha256": _sha256_bytes(candidate_payload),
            },
            "lean": {
                "path": target_path.relative_to(project).as_posix(),
                "sha256": _sha256_bytes(target_payload),
            },
            "blueprint": {
                "path": blueprint_path.relative_to(project).as_posix(),
                "sha256": _sha256_bytes(blueprint_payload),
            },
        }
        if (
            structured_target.get("source_report_path") != report_path
            or structured_target.get("source_report_sha256")
            != _sha256_bytes(report_payload)
            or structured_artifacts != expected_structured_artifacts
        ):
            _fail(f"current artifacts do not match the structured model response for {record_id}")

        verifier_record = _validate_verifier_record_against_current(
            record_id=record_id, verifier=verifier, target_path=target_path,
            target_payload=target_payload, candidate_path=candidate_path,
            candidate_payload=candidate_payload, candidate=candidate,
            source_contract=expected, project=project,
        )
        target_artifact = _artifact(
            project=project, path=target_path, kind="lean_target", payload=target_payload
        )
        blueprint_artifact = _artifact(
            project=project, path=blueprint_path, kind="blueprint", payload=blueprint_payload
        )
        report_artifact = _artifact(
            project=project, path=report_path, kind="source_report", payload=report_payload
        )
        candidate_artifact = _artifact(
            project=project, path=candidate_path, kind="blind_candidate", payload=candidate_payload
        )
        for artifact in (target_artifact, blueprint_artifact, report_artifact, candidate_artifact):
            add_artifact(artifact)
            expected_artifact_review_input[artifact["path"]] = artifact["sha256"]
        source_record_path = (
            f"{_SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        )
        expected_source_first_input[source_record_path] = _sha256_bytes(
            _json_bytes(_source_first_projection(bundle_row))
        )

        _validate_independent_review_record_against_current(
            source_row=source_first_rows.get(record_id),
            row=independent_rows.get(record_id),
            record_id=record_id,
            blind_record_sha256=blind_hash,
            bundle_row=bundle_row,
            target_path=target_path,
            target_payload=target_payload,
            candidate=candidate,
            candidate_payload=candidate_payload,
            report_payload=report_payload,
            blueprint_payload=blueprint_payload,
            source_contract=contract,
            requested_outputs=bundle_row.get("requested_outputs"),
        )

        page_assets = {
            str(item.get("path")): str(item.get("sha256"))
            for item in bundle_row.get("problem_assets", [])
            if isinstance(item, Mapping) and item.get("kind") == "problem_page"
        }
        image_artifacts: list[dict[str, str]] = []
        for image in expected.get("images", []):
            if not isinstance(image, Mapping):
                _fail(f"invalid image provenance for {record_id}")
            image_path = _resolve_project_locator(project, image.get("path"), label="problem image")
            image_artifact = _artifact(project=project, path=image_path, kind="problem_image")
            basename = image_path.name
            if (
                image_artifact["sha256"] != image.get("sha256")
                or page_assets.get(basename) != image_artifact["sha256"]
            ):
                _fail(f"problem image does not bind the bundle for {record_id}: {basename}")
            add_artifact(image_artifact)
            image_artifacts.append(image_artifact)
            expected_source_first_input[image_artifact["path"]] = image_artifact[
                "sha256"
            ]

        records.append({
            "id": record_id,
            "blind_record_sha256": blind_hash,
            "candidate": candidate,
            "candidate_artifact": candidate_artifact,
            "target_artifact": target_artifact,
            "blueprint_artifact": blueprint_artifact,
            "source_report_artifact": report_artifact,
            "problem_image_artifacts": image_artifacts,
            "source_contract": expected,
            "lean_verifier_record": verifier_record,
            "formalization_gate_status": "passed",
            "proof_gate_status": "solved",
        })

    if context["source_first_input_files"] != dict(
        sorted(expected_source_first_input.items())
    ):
        _fail(
            "source-first Review sanitized input must contain exactly scoped "
            "canonical source projections and problem images"
        )
    if context["artifact_review_input_files"] != dict(
        sorted(expected_artifact_review_input.items())
    ):
        _fail(
            "artifact Review sanitized input must contain exactly the bound "
            "problem/candidate/source/blueprint artifacts and source commitment"
        )

    artifacts = sorted(artifact_index.values(), key=lambda item: (item["path"], item["kind"]))
    controller_binding = {
        "controller_seal_sha256": context["seal_sha256"],
        "scope_kind": seal["freeze_scope"]["kind"],
        "scope_ids": scope_ids,
        "bundle_sha256": seal["blind_bundle"]["sha256"],
        "bundle_row_count": seal["blind_bundle"]["row_count"],
        "seed_manifest_sha256": seal["seed_manifest_sha256"],
        "snapshot_inventory_sha256": seal["snapshot_inventory"]["files_sha256"],
        "dependency_inventory_sha256": seal["dependency_inventory"]["files_sha256"],
        "runtime_inventory_sha256": seal["runtime_inventory"]["files_sha256"],
        "verifier_snapshot_sha256": seal["verifier_snapshot"]["files_sha256"],
        "source_first_precommit_sha256": seal["source_first_precommit"][
            "sha256"
        ],
        "structured_solver_receipt_sha256": context[
            "structured_solver_receipt_sha256"
        ],
        "verifier_receipt_sha256": context["verifier_receipt_sha256"],
        "lean_verifier_result_sha256": context["lean_verifier_result_sha256"],
        "independent_review_receipt_sha256": context[
            "independent_review_receipt_sha256"
        ],
    }
    manifest: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": FREEZE_PHASE,
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "frozen_at": frozen_at,
        "project_binding": ".",
        "solver": dict(seal["solver"]),
        "isolation": dict(seal["isolation"]),
        "controller_binding": controller_binding,
        "record_count": len(records),
        "records": records,
        "artifacts": artifacts,
    }
    leakage = _find_leakage_keys(manifest, path="manifest")
    if leakage:
        _fail("refusing to freeze a manifest with leakage field(s): " + ", ".join(leakage))
    return manifest


def _trusted_receipt_locator_for_seal(
    *, project: Path, raw: Path | str, label: str
) -> dict[str, str]:
    """Bind one already-finalized controller receipt into a new seal.

    Structured solve/Review and verifier receipts are controller artifacts,
    not solver outputs.  Requiring an external mode-0400 regular file keeps the
    seal producer from accidentally blessing a mutable workspace copy.
    """
    path = Path(raw)
    if not path.is_absolute():
        path = Path.cwd() / path
    path = _outside_project(path, project, label=label)
    _require_controller_owned_readonly(path, label=label)
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a regular, non-symlink file: {path}")
    if path.stat(follow_symlinks=False).st_mode & 0o777 != 0o400:
        _fail(f"{label} must be finalized mode 0400")
    payload = _read_plain_bytes(
        path, label=label, max_bytes=_MAX_CONTROLLER_SEAL_BYTES
    )
    # Reject opaque/non-object inputs before putting their digest in a seal.
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _fail(f"invalid JSON in {label} {path}: {exc}")
    if not isinstance(value, dict):
        _fail(f"{label} must contain one JSON object: {path}")
    return {"path": str(path.resolve()), "sha256": _sha256_bytes(payload)}


def create_blind_verifier_snapshot(
    *, project: Path | str, dependency_root: Path | str, output: Path | str
) -> dict[str, Any]:
    """Publish a root-owned, world-readable clean source snapshot for verify.

    The copy is byte-for-byte identical to the sealed project inventory while
    deliberately excluding no additional files: build/config/olean state is
    already rejected by :func:`_project_snapshot_inventory`.  Publication is
    an atomic directory rename, so the verifier never observes a partial tree.
    """
    if os.geteuid() != 0:
        _fail("verifier snapshot creation must run as root")
    project_path = _project_path(project)
    _require_trusted_controller_runtime(project_path)
    dependency_path = Path(dependency_root).resolve()
    _outside_project(
        dependency_path, project_path, label="controller dependency root"
    )
    source_files = _project_snapshot_inventory(
        project_path, dependency_root=dependency_path
    )
    output_path = _controller_output_path(
        output, project=project_path, label="verifier snapshot output"
    )
    for ancestor in (output_path.parent, *output_path.parent.parents):
        if ancestor.stat(follow_symlinks=False).st_mode & 0o001 == 0:
            _fail(
                "verifier snapshot output path must be world-traversable: "
                f"{ancestor}"
            )
    if output_path.exists() or output_path.is_symlink():
        _fail(f"refusing to overwrite existing output: {output_path}")
    temporary = Path(
        tempfile.mkdtemp(prefix=f".{output_path.name}.", dir=output_path.parent)
    )
    try:
        os.chmod(temporary, 0o755)
        for relative, expected in source_files.items():
            source = _resolve_project_locator(
                project_path, relative, label="sealed snapshot source"
            )
            target = temporary / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            os.chmod(target.parent, 0o755)
            payload = _read_plain_bytes(source, label="sealed snapshot source")
            if _sha256_bytes(payload) != expected:
                _fail(f"solver snapshot changed during copy: {relative}")
            fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
            try:
                with os.fdopen(fd, "wb") as handle:
                    handle.write(payload)
                    handle.flush()
                    os.fchmod(handle.fileno(), 0o444)
                    os.fsync(handle.fileno())
            except BaseException:
                try:
                    os.close(fd)
                except OSError:
                    pass
                raise
        os.replace(temporary, output_path)
        temporary = Path()
        directory_fd = os.open(output_path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        if temporary != Path() and temporary.exists():
            shutil.rmtree(temporary)
    copied = _regular_file_inventory(
        output_path, label="controller verifier snapshot"
    )
    if copied != source_files:
        _fail("published verifier snapshot differs from sealed project bytes")
    return {
        "root": str(output_path),
        "files": copied,
        "files_sha256": _hash_index(copied),
    }


def _controller_bundle_spec(
    *, project: Path, bundle: Path | str
) -> dict[str, Any]:
    path = Path(bundle)
    if not path.is_absolute():
        path = project / path
    path = _project_path_without_symlinks(
        path, project, label="questions-only bundle"
    )
    payload = _read_plain_bytes(path, label="questions-only bundle")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(f"questions-only bundle is not UTF-8: {exc}")
    ids: list[str] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            _fail(f"invalid questions-only JSON at {path}:{line_number}: {exc}")
        if not isinstance(row, dict):
            _fail(f"questions-only row {line_number} must be an object")
        ids.append(
            _require_nonempty_string(
                row.get("id"), field=f"questions-only row {line_number}.id"
            )
        )
    if not ids:
        _fail("questions-only bundle contains no rows")
    if len(ids) != len(set(ids)):
        _fail("questions-only bundle contains duplicate IDs")
    sorted_ids = sorted(ids)
    _strict_id_list(sorted_ids, label="questions-only bundle IDs")
    return {
        "path": path.relative_to(project).as_posix(),
        "sha256": _sha256_bytes(payload),
        "row_count": len(sorted_ids),
        "ids": sorted_ids,
    }


def create_blind_controller_seal(
    *,
    project: Path | str,
    bundle: Path | str,
    structured_solver_receipt: Path | str,
    source_first_precommit: Path | str,
    independent_review_receipt: Path | str,
    verifier_receipt: Path | str,
    dependency_root: Path | str,
    runtime_root: Path | str,
    verifier_snapshot: Path | str,
    output: Path | str,
    scope_kind: str = "full",
    scope_ids: Sequence[str] | None = None,
) -> dict[str, Any]:
    """Create the root-owned authorization consumed by freeze and grade.

    This is the structured, tool-free controller finalize path.  It does not
    execute Lean or a model.  It inventories the stopped clean snapshot and
    trusted roots, then semantically replays every already-finalized solver,
    source-first, artifact-Review, and low-privilege verifier receipt before
    publishing a new mode-0400 seal outside the solver project.
    """
    if os.geteuid() != 0:
        _fail("controller seal creation must run as root")
    project_path = _project_path(project)
    _require_trusted_controller_runtime(project_path)
    output_path = _controller_output_path(
        output, project=project_path, label="controller seal output"
    )
    bundle_spec = _controller_bundle_spec(project=project_path, bundle=bundle)
    bundle_ids = list(bundle_spec["ids"])
    if scope_kind not in {"full", "pilot"}:
        _fail("controller seal scope_kind must be full or pilot")
    selected_ids = (
        bundle_ids
        if scope_ids is None
        else _strict_id_list(list(scope_ids), label="controller seal scope IDs")
    )
    if not set(selected_ids).issubset(bundle_ids):
        _fail("controller seal scope is not a subset of the bundle")
    if scope_kind == "full" and selected_ids != bundle_ids:
        _fail("a full controller seal must cover every bundle ID")

    dependency_path = Path(dependency_root).resolve()
    runtime_path = Path(runtime_root).resolve()
    for path, label in (
        (dependency_path, "controller dependency root"),
        (runtime_path, "controller runtime root"),
    ):
        _outside_project(path, project_path, label=label)
        _require_controller_owned_readonly(path, label=label)
    dependency_files = _regular_file_inventory(
        dependency_path, label="controller dependency tree"
    )
    runtime_files = _regular_file_inventory(
        runtime_path,
        label="controller answer-blind runtime",
        exclude_roots=(dependency_path,),
    )
    snapshot_files = _project_snapshot_inventory(
        project_path, dependency_root=dependency_path
    )
    verifier_snapshot_path = Path(verifier_snapshot).resolve()
    _outside_project(
        verifier_snapshot_path, project_path, label="controller verifier snapshot"
    )
    verifier_snapshot_files = _regular_file_inventory(
        verifier_snapshot_path, label="controller verifier snapshot"
    )
    if verifier_snapshot_files != snapshot_files:
        _fail("controller verifier snapshot differs from the sealed project snapshot")

    solver_locator = _trusted_receipt_locator_for_seal(
        project=project_path, raw=structured_solver_receipt,
        label="structured solver aggregate",
    )
    precommit_locator = _trusted_receipt_locator_for_seal(
        project=project_path, raw=source_first_precommit,
        label="source-first pre-solver commitment",
    )
    review_locator = _trusted_receipt_locator_for_seal(
        project=project_path, raw=independent_review_receipt,
        label="structured independent Review aggregate",
    )
    verifier_locator = _trusted_receipt_locator_for_seal(
        project=project_path, raw=verifier_receipt,
        label="Lean verifier invocation",
    )
    protected_inputs = {
        Path(locator["path"]).resolve()
        for locator in (
            solver_locator, precommit_locator, review_locator, verifier_locator
        )
    }
    if output_path in protected_inputs:
        _fail("controller seal output may not overwrite a bound receipt")

    solver_aggregate, _ = _read_json(
        Path(solver_locator["path"]), label="structured solver aggregate",
        max_bytes=_MAX_CONTROLLER_SEAL_BYTES,
    )
    solver_identity = {
        field: _require_nonempty_string(
            solver_aggregate.get(field), field=f"structured solver {field}"
        )
        for field in _SOLVER_FIELDS
    }
    generated_files = {
        relative: _sha256_bytes(
            _read_plain_bytes(
                _resolve_project_locator(
                    project_path, relative, label="controller-generated file"
                ),
                label="controller-generated file",
            )
        )
        for relative in sorted(_CONTROLLER_GENERATED_FILES)
    }
    seed_path = _project_path_without_symlinks(
        project_path / SEED_MANIFEST,
        project_path,
        label="seed isolation manifest",
    )
    seed_payload = _read_plain_bytes(seed_path, label="seed isolation manifest")
    seal: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": CONTROLLER_PHASE,
        "solver_stopped": True,
        "seed_manifest_sha256": _sha256_bytes(seed_payload),
        "blind_bundle": bundle_spec,
        "freeze_scope": {"kind": scope_kind, "ids": selected_ids},
        "generated_files": generated_files,
        "dependency_inventory": {
            "root": str(dependency_path),
            "files": dependency_files,
            "files_sha256": _hash_index(dependency_files),
        },
        "runtime_inventory": {
            "root": str(runtime_path),
            "files": runtime_files,
            "files_sha256": _hash_index(runtime_files),
        },
        "snapshot_inventory": {
            "files": snapshot_files,
            "files_sha256": _hash_index(snapshot_files),
        },
        "verifier_snapshot": {
            "root": str(verifier_snapshot_path),
            "files": verifier_snapshot_files,
            "files_sha256": _hash_index(verifier_snapshot_files),
        },
        "independent_review_receipt": review_locator,
        "solver": solver_identity,
        "isolation": {
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
        },
        "structured_solver_receipt": solver_locator,
        "source_first_precommit": precommit_locator,
        "verifier_receipt": verifier_locator,
    }

    # Validate from current bytes before publication.  Passing these checks is
    # what grants authorization; no solver-authored status bit is trusted.
    _strict_fields(seal, _CONTROLLER_BINDING_FIELDS, label="controller seal")
    bundle_path, bundle_payload, bundle_records = _parse_blind_bundle(
        project=project_path, seal=seal
    )
    _validate_dependency_inventory(seal, project=project_path)
    _validate_runtime_inventory(seal, project=project_path)
    _validate_snapshot_inventory(seal, project=project_path)
    _validate_verifier_snapshot(seal, project=project_path)
    _validate_seed_and_root_files(
        project=project_path,
        seal=seal,
        bundle_path=bundle_path,
        bundle_payload=bundle_payload,
    )
    _load_source_first_precommit(project=project_path, seal=seal)
    _load_and_validate_structured_solver(
        project=project_path, seal=seal, bundle_records=bundle_records
    )
    _load_and_validate_verifier_invocation(project=project_path, seal=seal)
    _load_independent_review_invocation(project=project_path, seal=seal)

    _atomic_write_new(output_path, _json_bytes(seal), mode=0o400)
    return seal


def freeze_blind_evaluation(
    *,
    project: Path | str,
    candidate_dir: Path | str,
    output: Path | str,
    controller_seal: Path | str,
    expected_controller_seal_sha256: str,
) -> dict[str, Any]:
    """Freeze one controller-authorized scope without reading a grader key."""
    project_path = _project_path(project)
    output_path = _controller_output_path(
        output, project=project_path, label="freeze output"
    )
    manifest = _build_current_freeze_manifest(
        project=project_path,
        candidate_dir=candidate_dir,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
        frozen_at=_utcnow(),
    )
    _validate_frozen_manifest(manifest)
    _verify_frozen_artifacts(project=project_path, manifest=manifest)
    _atomic_write_new(output_path, _json_bytes(manifest), mode=0o400)
    return manifest


def _validate_frozen_manifest(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    _strict_fields(manifest, _FROZEN_MANIFEST_FIELDS, label="frozen manifest")
    if manifest.get("schema_version") != SCHEMA_VERSION:
        _fail("frozen manifest requires schema_version=1")
    if manifest.get("protocol") != PROTOCOL:
        _fail("frozen manifest protocol is unsupported")
    if manifest.get("phase") != FREEZE_PHASE:
        _fail("manifest is not a completed answer-blind freeze")
    if manifest.get("evaluation_mode") != "answer_blind":
        _fail("manifest is not answer_blind")
    if manifest.get("official_answer_seen") is not False:
        _fail("frozen manifest claims official answer exposure")
    if manifest.get("project_binding") != ".":
        _fail("frozen manifest project_binding must be '.'")
    _require_nonempty_string(manifest.get("frozen_at"), field="frozen_at")
    solver = manifest.get("solver")
    if not isinstance(solver, dict):
        _fail("frozen manifest solver must be an object")
    _strict_fields(solver, _SOLVER_FIELDS, label="frozen manifest solver")
    for field in _SOLVER_FIELDS:
        _require_nonempty_string(solver.get(field), field=f"solver.{field}")
    isolation = manifest.get("isolation")
    if not isinstance(isolation, dict):
        _fail("frozen manifest isolation must be an object")
    _strict_fields(isolation, _ISOLATION_FIELDS, label="frozen manifest isolation")
    if isolation != {
        "filesystem_answer_blind": True,
        "network_answer_blind": False,
    }:
        _fail("frozen manifest lacks filesystem answer-blind isolation")
    binding = manifest.get("controller_binding")
    if not isinstance(binding, dict):
        _fail("frozen manifest controller_binding must be an object")
    _strict_fields(binding, _FROZEN_CONTROLLER_FIELDS, label="controller_binding")
    for field in _FROZEN_CONTROLLER_FIELDS - {"scope_kind", "scope_ids", "bundle_row_count"}:
        _require_sha256(binding.get(field), field=f"controller_binding.{field}")
    if binding.get("scope_kind") not in {"full", "pilot"}:
        _fail("controller_binding.scope_kind must be full or pilot")
    scope_ids = _strict_id_list(binding.get("scope_ids"), label="controller_binding.scope_ids")
    row_count = binding.get("bundle_row_count")
    if not isinstance(row_count, int) or isinstance(row_count, bool) or row_count < len(scope_ids):
        _fail("controller_binding.bundle_row_count is invalid")
    if binding.get("scope_kind") == "full" and row_count != len(scope_ids):
        _fail("full frozen manifest scope does not cover the complete bundle")
    records = manifest.get("records")
    if not isinstance(records, list) or not records:
        _fail("frozen manifest contains no records")
    if manifest.get("record_count") != len(records):
        _fail("frozen manifest record_count is inconsistent")
    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        _fail("frozen manifest contains no artifact inventory")
    seen_ids: set[str] = set()
    for record in records:
        if not isinstance(record, dict):
            _fail("frozen manifest record is not an object")
        _strict_fields(record, _FROZEN_RECORD_FIELDS, label="frozen manifest record")
        record_id = _require_nonempty_string(record.get("id"), field="manifest record id")
        if record_id in seen_ids:
            _fail(f"duplicate frozen record id: {record_id}")
        seen_ids.add(record_id)
        blind_hash = _require_sha256(
            record.get("blind_record_sha256"), field=f"frozen record {record_id} blind hash"
        )
        candidate = record.get("candidate")
        if not isinstance(candidate, dict):
            _fail(f"frozen record {record_id} has no candidate object")
        _validate_candidate(candidate, expected_id=record_id, expected_blind_hash=blind_hash)
        if record.get("formalization_gate_status") != "passed" or record.get(
            "proof_gate_status"
        ) != "solved":
            _fail(f"frozen record gates are not passing: {record_id}")
        if not isinstance(record.get("source_contract"), dict):
            _fail(f"frozen record source_contract is missing: {record_id}")
        if not isinstance(record.get("lean_verifier_record"), dict):
            _fail(f"frozen record Lean verifier evidence is missing: {record_id}")
    if [record["id"] for record in records] != scope_ids:
        _fail("frozen manifest records do not exactly follow controller scope IDs")
    for index, artifact in enumerate(artifacts, start=1):
        if not isinstance(artifact, dict):
            _fail(f"frozen artifact {index} is not an object")
        _strict_fields(artifact, _ARTIFACT_FIELDS, label=f"frozen artifact {index}")
    return records


def _verify_frozen_artifacts(
    *,
    project: Path,
    manifest: dict[str, Any],
) -> dict[str, bytes]:
    verified: dict[str, bytes] = {}
    by_path: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(manifest.get("artifacts", []), start=1):
        if not isinstance(raw, dict):
            _fail(f"frozen artifact {index} is not an object")
        path = _resolve_project_locator(
            project, raw.get("path"), label=f"frozen artifact {index}"
        )
        relative = path.relative_to(project).as_posix()
        if relative in verified:
            _fail(f"duplicate path in frozen artifact inventory: {relative}")
        expected = _require_sha256(
            raw.get("sha256"), field=f"frozen artifact {relative}.sha256"
        )
        payload = _read_plain_bytes(path, label=f"frozen artifact {relative}")
        actual = _sha256_bytes(payload)
        if actual != expected:
            _fail(f"frozen artifact hash drift detected: {relative}")
        verified[relative] = payload
        by_path[relative] = raw

    for record in manifest["records"]:
        record_id = record["id"]
        expected_refs = {
            "candidate_artifact": "blind_candidate",
            "target_artifact": "lean_target",
            "blueprint_artifact": "blueprint",
            "source_report_artifact": "source_report",
        }
        for field, expected_kind in expected_refs.items():
            artifact = record.get(field)
            if not isinstance(artifact, dict):
                _fail(f"frozen record {record_id} lacks {field}")
            _strict_fields(artifact, _ARTIFACT_FIELDS, label=f"record {record_id}.{field}")
            path = str(artifact.get("path") or "")
            expected = _require_sha256(
                artifact.get("sha256"), field=f"record {record_id}.{field}.sha256"
            )
            payload = verified.get(path)
            if (
                payload is None
                or _sha256_bytes(payload) != expected
                or by_path.get(path) != artifact
                or artifact.get("kind") != expected_kind
            ):
                _fail(f"{field} is absent/mismatched in frozen inventory: {record_id}")
        candidate_artifact = record["candidate_artifact"]
        path = str(candidate_artifact["path"])
        payload = verified[path]
        try:
            candidate_on_disk = json.loads(payload.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            _fail(f"frozen candidate became invalid JSON for {record_id}: {exc}")
        if candidate_on_disk != record.get("candidate"):
            _fail(f"embedded and on-disk frozen candidates disagree: {record_id}")
        images = record.get("problem_image_artifacts")
        if not isinstance(images, list) or not images:
            _fail(f"frozen record {record_id} has no problem image artifacts")
        for artifact in images:
            if not isinstance(artifact, dict):
                _fail(f"frozen record {record_id} has an invalid problem image artifact")
            path = str(artifact.get("path") or "")
            if by_path.get(path) != artifact or artifact.get("kind") != "problem_image":
                _fail(f"problem image is absent from frozen inventory: {record_id}")
    return verified


def _read_grader_jsonl(
    path: Path, *, expected_sha256: str | None = None
) -> tuple[list[dict[str, Any]], bytes]:
    payload = _read_plain_bytes(path, label="external grader JSONL")
    if expected_sha256 is not None and _sha256_bytes(payload) != expected_sha256:
        _fail("external grader SHA-256 does not match controller expectation")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(f"external grader JSONL is not UTF-8: {exc}")
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            _fail(f"invalid grader JSON at {path}:{line_number}: {exc}")
        if not isinstance(row, dict):
            _fail(f"grader row at {path}:{line_number} must be an object")
        rows.append(row)
    if not rows:
        _fail("external grader JSONL contains no rows")
    return rows, payload


def _normalize_text(value: object) -> str:
    text = unicodedata.normalize("NFKC", str(value)).strip().casefold()
    text = text.replace("−", "-").replace("–", "-").replace("—", "-")
    text = re.sub(r"\s+", " ", text)
    return text.strip(" .;,")


def _validated_grading_override(
    value: object,
    *,
    official_answer: str,
    candidate: Mapping[str, Any],
    record_id: str,
) -> dict[str, Any]:
    """Validate one controller-owned, exact-display grading override."""
    label = f"grader {record_id}.grading_override"
    if not isinstance(value, Mapping):
        _fail(f"{label} must be an object")
    _strict_fields(value, _GRADING_OVERRIDE_FIELDS, label=label)

    schema_version = value.get("schema_version")
    if type(schema_version) is not int or schema_version != 1:
        _fail(f"{label}.schema_version must equal 1")

    bound_hash = _require_sha256(
        value.get("official_answer_sha256"),
        field=f"{label}.official_answer_sha256",
    )
    actual_hash = _sha256_bytes(official_answer.encode("utf-8"))
    if bound_hash != actual_hash:
        _fail(f"{label}.official_answer_sha256 does not bind official_answer")

    reason_code = _require_nonempty_string(
        value.get("reason_code"), field=f"{label}.reason_code"
    )
    if (
        len(reason_code) > _MAX_GRADING_OVERRIDE_REASON_CODE_LENGTH
        or _SAFE_ID_RE.fullmatch(reason_code) is None
    ):
        _fail(f"{label}.reason_code must be a bounded safe identifier")

    canonical_answer = _require_nonempty_string(
        value.get("canonical_answer"), field=f"{label}.canonical_answer"
    )
    if len(canonical_answer) > _MAX_NUMERIC_TEXT_LENGTH:
        _fail(f"{label}.canonical_answer exceeds the text limit")
    canonical_normalized = _normalize_text(canonical_answer)
    if not canonical_normalized:
        _fail(f"{label}.canonical_answer is empty after normalization")

    raw_aliases = value.get("accepted_legacy_answers")
    if not isinstance(raw_aliases, list) or not raw_aliases:
        _fail(f"{label}.accepted_legacy_answers must be a non-empty list")
    if len(raw_aliases) > _MAX_GRADING_OVERRIDE_ALIASES:
        _fail(
            f"{label}.accepted_legacy_answers exceeds "
            f"{_MAX_GRADING_OVERRIDE_ALIASES} aliases"
        )

    aliases: list[str] = []
    normalized_answers = {canonical_normalized}
    for index, raw_alias in enumerate(raw_aliases):
        alias = _require_nonempty_string(
            raw_alias,
            field=f"{label}.accepted_legacy_answers[{index}]",
        )
        if len(alias) > _MAX_NUMERIC_TEXT_LENGTH:
            _fail(
                f"{label}.accepted_legacy_answers[{index}] exceeds the text limit"
            )
        normalized = _normalize_text(alias)
        if not normalized:
            _fail(
                f"{label}.accepted_legacy_answers[{index}] is empty after normalization"
            )
        if normalized in normalized_answers:
            _fail(f"{label}.accepted_legacy_answers contains a duplicate alias")
        normalized_answers.add(normalized)
        aliases.append(alias)

    if candidate.get("result_kind") != "numeric":
        _fail(f"{label} is only valid for a numeric candidate")

    return {
        "schema_version": 1,
        "official_answer_sha256": bound_hash,
        "reason_code": reason_code,
        "canonical_answer": canonical_answer,
        "accepted_legacy_answers": aliases,
    }


def _display_variants(candidate: Mapping[str, Any]) -> set[str]:
    reported = candidate.get("reported_result")
    if not isinstance(reported, Mapping):
        return set()
    variants: set[str] = set()
    text = reported.get("text")
    if isinstance(text, str) and text.strip():
        variants.add(_normalize_text(text))
    value = reported.get("value")
    if value is not None and str(value).strip():
        variants.add(_normalize_text(value))
        unit = reported.get("unit")
        if isinstance(unit, str) and unit.strip():
            variants.add(_normalize_text(f"{value} {unit}"))
    return {item for item in variants if item}


def _structured_display_variants(candidate: Mapping[str, Any]) -> set[str]:
    """Return only value/unit displays; never trust free-form reported text."""
    reported = candidate.get("reported_result")
    if not isinstance(reported, Mapping):
        return set()
    value = reported.get("value")
    if value is None or not str(value).strip():
        return set()
    variants = {_normalize_text(value)}
    unit = reported.get("unit")
    if isinstance(unit, str) and unit.strip():
        variants.add(_normalize_text(f"{value} {unit}"))
    return variants


def _scientific_text(text: str) -> str:
    return _SCI_TIMES_TEN_RE.sub(lambda match: f"{match.group(1)}e{match.group(2)}", text)


def _one_decimal(value: object) -> Decimal | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float, Decimal)):
        try:
            return Decimal(str(value))
        except InvalidOperation:
            return None
    text = _scientific_text(unicodedata.normalize("NFKC", str(value)))
    matches = _NUMBER_RE.findall(text)
    if len(matches) != 1:
        return None
    try:
        return Decimal(matches[0])
    except InvalidOperation:
        return None


def _official_display_decimal(value: object) -> tuple[Decimal, Decimal] | None:
    """Parse one displayed answer number, ignoring exponents inside its unit."""
    text = _scientific_text(unicodedata.normalize("NFKC", str(value)))
    if len(text) > _MAX_NUMERIC_TEXT_LENGTH:
        return None
    matches = []
    for match in _NUMBER_RE.finditer(text):
        prefix = text[: match.start()].rstrip()
        if re.search(r"[A-Za-zα-ω)]\s*(?:\^|\*\*)$", prefix):
            continue
        matches.append(match.group())
    if len(matches) != 1:
        return None
    try:
        parsed = Decimal(matches[0])
        if not parsed.is_finite():
            return None
        exponent = parsed.as_tuple().exponent
        if (
            not isinstance(exponent, int)
            or abs(exponent) > _MAX_NUMERIC_EXPONENT_ABS
        ):
            return None
        quantum = Decimal(1).scaleb(exponent)
    except (InvalidOperation, OverflowError, ValueError):
        return None
    if not quantum.is_finite() or quantum <= 0:
        return None
    return parsed, quantum


def _unit_compatible(candidate_unit: object, official: str) -> bool | None:
    if candidate_unit is None or not str(candidate_unit).strip():
        return True
    expected = _normalize_text(candidate_unit).replace(" ", "")
    normalized_official = _normalize_text(official).replace(" ", "")
    unit_pattern = rf"(?<![a-zα-ω]){re.escape(expected)}(?![a-zα-ω])"
    if re.search(unit_pattern, normalized_official):
        return True
    # A bare official number has no evidence either way; keep it manual rather
    # than declaring a dimensional conflict.
    without_numbers = _NUMBER_RE.sub("", _scientific_text(normalized_official))
    if not re.search(r"[a-zα-ω]", without_numbers):
        return None
    return False


def _rounding_quantum(precision: object, reported: Decimal) -> Decimal | None:
    kind = ""
    digits: int | None = None
    if isinstance(precision, bool) or precision is None:
        return None
    if isinstance(precision, int):
        kind, digits = "significant_figures", precision
    elif isinstance(precision, Mapping):
        kind = str(precision.get("kind") or precision.get("type") or "").lower()
        raw_digits = precision.get("digits", precision.get("places"))
        try:
            digits = int(raw_digits)
        except (TypeError, ValueError):
            return None
    else:
        text = str(precision).strip().lower().replace("-", "_")
        match = re.search(r"(\d+)", text)
        if match:
            digits = int(match.group(1))
        if any(token in text for token in ("significant", "sig", "sf")):
            kind = "significant_figures"
        elif any(token in text for token in ("decimal", "dp", "places")):
            kind = "decimal_places"
        else:
            try:
                quantum = Decimal(text)
            except InvalidOperation:
                return None
            return quantum.copy_abs() if quantum != 0 else None
    if digits is None or digits < 0:
        return None
    if kind in {"decimal", "decimal_place", "decimal_places", "dp"}:
        return Decimal(1).scaleb(-digits)
    if kind in {"significant", "significant_figure", "significant_figures", "sigfig", "sf"}:
        if digits < 1:
            return None
        if reported == 0:
            return Decimal(1).scaleb(-(digits - 1))
        return Decimal(1).scaleb(reported.copy_abs().adjusted() - digits + 1)
    return None


def _rounding_sensitive_numeric_match(
    candidate: Mapping[str, Any], official_answer: str
) -> bool:
    """Detect compatible numeric displays whose rounding cells touch or overlap."""
    reported = candidate.get("reported_result")
    if not isinstance(reported, Mapping):
        return False
    candidate_value = _one_decimal(reported.get("value"))
    official_display = _official_display_decimal(official_answer)
    if (
        candidate_value is None
        or not candidate_value.is_finite()
        or official_display is None
    ):
        return False
    official_value, official_quantum = official_display
    if candidate_value == official_value:
        return False
    if _unit_compatible(reported.get("unit"), official_answer) is not True:
        return False

    try:
        candidate_quantum = _rounding_quantum(
            reported.get("precision"), candidate_value
        )
    except (InvalidOperation, OverflowError, ValueError):
        return False
    if (
        candidate_quantum is None
        or not candidate_quantum.is_finite()
        or candidate_quantum <= 0
        or not official_quantum.is_finite()
        or official_quantum <= 0
    ):
        return False

    delta = abs(candidate_value - official_value)
    return 2 * delta <= candidate_quantum + official_quantum


def _grade_one(
    candidate: Mapping[str, Any],
    official_answer: str,
    *,
    grading_override: Mapping[str, Any] | None = None,
) -> tuple[str, str]:
    if candidate.get("result_kind") == "underdetermined":
        return "underdetermined", "solver froze a proved underdetermined result"

    if candidate.get("result_kind") == "numeric" and grading_override is not None:
        display_variants = _structured_display_variants(candidate)
        canonical = _normalize_text(grading_override["canonical_answer"])
        reason_code = grading_override["reason_code"]
        if canonical in display_variants:
            return (
                "exact_match",
                "grading_override canonical_answer matches the normalized "
                f"reported value and unit ({reason_code})",
            )
        legacy = {
            _normalize_text(answer)
            for answer in grading_override["accepted_legacy_answers"]
        }
        if display_variants & legacy:
            return (
                "exact_match",
                "grading_override accepted_legacy_answer matches the normalized "
                f"reported value and unit ({reason_code})",
            )

    official_normalized = _normalize_text(official_answer)
    if (
        grading_override is None
        and official_normalized in _display_variants(candidate)
    ):
        return "exact_match", "normalized reported result matches the official answer"

    if candidate.get("result_kind") == "numeric":
        if _rounding_sensitive_numeric_match(candidate, official_answer):
            return (
                "manual_review",
                "rounding_sensitive: compatible-unit numeric reports have adjacent "
                "or overlapping reporting cells; this is consistent with a "
                "scientifically equivalent rounding-path difference, pending "
                "independent review",
            )
        return (
            "manual_review",
            "the grader has no precommitted structured numeric key; only a whole-string exact match is automatic",
        )

    return "manual_review", "non-exact official prose requires independent human review"


def grade_blind_evaluation(
    *,
    project: Path | str,
    manifest: Path | str,
    grader: Path | str,
    output: Path | str,
    controller_seal: Path | str,
    expected_controller_seal_sha256: str,
    expected_freeze_sha256: str,
    expected_grader_sha256: str,
) -> dict[str, Any]:
    """Rebuild a controller-authorized freeze, then open the external key."""
    project_path = _project_path(project)
    _require_trusted_controller_runtime(project_path)
    manifest_path = Path(manifest)
    if not manifest_path.is_absolute():
        manifest_path = Path.cwd() / manifest_path
    manifest_path = _outside_project(
        manifest_path, project_path, label="freeze manifest"
    )
    _require_controller_owned_readonly(manifest_path, label="freeze manifest")
    frozen, manifest_payload = _read_json(manifest_path, label="freeze manifest")
    expected_manifest_hash = _require_sha256(
        expected_freeze_sha256, field="expected_freeze_sha256"
    )
    if _sha256_bytes(manifest_payload) != expected_manifest_hash:
        _fail("freeze manifest SHA-256 does not match controller expectation")
    records = _validate_frozen_manifest(frozen)
    candidate_dirs = {
        Path(str(record["candidate_artifact"]["path"])).parent.as_posix()
        for record in records
    }
    if len(candidate_dirs) != 1:
        _fail("frozen candidates do not share one bound project directory")
    frozen_candidate_dir = next(iter(candidate_dirs))

    # Rebuild controller bindings, current gates, source contracts, bundle
    # projections, candidate policies and all inventories before even resolving
    # the grader path.  A self-consistent solver-written manifest is insufficient.
    rebuilt = _build_current_freeze_manifest(
        project=project_path,
        candidate_dir=frozen_candidate_dir,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
        frozen_at=str(frozen.get("frozen_at") or ""),
    )
    if rebuilt != frozen:
        _fail("freeze manifest does not match reconstructed controller/current state")
    verified = _verify_frozen_artifacts(project=project_path, manifest=frozen)

    grader_path = Path(grader)
    if not grader_path.is_absolute():
        grader_path = Path.cwd() / grader_path
    grader_path = _outside_project(grader_path, project_path, label="external grader")
    _require_controller_owned_readonly(grader_path, label="external grader")
    output_path = _controller_output_path(
        output, project=project_path, label="grade output"
    )

    protected_paths = {manifest_path, grader_path}
    protected_paths.update((project_path / rel).resolve() for rel in verified)
    if output_path in protected_paths:
        _fail("grade output may not overwrite the manifest, grader, or a frozen artifact")

    expected_grader_hash = _require_sha256(
        expected_grader_sha256, field="expected_grader_sha256"
    )
    grader_rows, grader_payload = _read_grader_jsonl(
        grader_path, expected_sha256=expected_grader_hash
    )
    expected_by_id = {record["id"]: record for record in records}
    grader_by_id: dict[str, dict[str, Any]] = {}
    grading_overrides: dict[str, dict[str, Any]] = {}
    for row in grader_rows:
        record_id = _require_nonempty_string(row.get("id"), field="grader row id")
        if record_id in grader_by_id:
            _fail(f"duplicate grader id: {record_id}")
        if record_id not in expected_by_id:
            _fail(f"grader contains an id absent from the freeze: {record_id}")
        blind_hash = _require_sha256(
            row.get("blind_record_sha256"), field=f"grader {record_id}.blind_record_sha256"
        )
        if blind_hash != expected_by_id[record_id]["blind_record_sha256"]:
            _fail(f"grader blind_record_sha256 does not bind to the freeze: {record_id}")
        _require_nonempty_string(
            row.get("official_answer"), field=f"grader {record_id}.official_answer"
        )
        official_answer = str(row["official_answer"])
        if "grading_override" in row:
            grading_overrides[record_id] = _validated_grading_override(
                row["grading_override"],
                official_answer=official_answer,
                candidate=expected_by_id[record_id]["candidate"],
                record_id=record_id,
            )
        grader_by_id[record_id] = row
    missing = sorted(set(expected_by_id) - set(grader_by_id))
    if missing:
        _fail("grader is missing frozen id(s): " + ", ".join(missing))

    results: list[dict[str, Any]] = []
    for record_id in sorted(expected_by_id):
        record = expected_by_id[record_id]
        row = grader_by_id[record_id]
        official_answer = str(row["official_answer"])
        result, reason = _grade_one(
            record["candidate"],
            official_answer,
            grading_override=grading_overrides.get(record_id),
        )
        if result not in GRADE_RESULTS:  # pragma: no cover - internal invariant
            _fail(f"internal unsupported grade result: {result}")
        results.append(
            {
                "id": record_id,
                "blind_record_sha256": record["blind_record_sha256"],
                "candidate_sha256": record["candidate_artifact"]["sha256"],
                "official_answer_sha256": _sha256_bytes(official_answer.encode("utf-8")),
                "result": result,
                "reason": reason,
            }
        )

    # Repeat the full semantic reconstruction after opening the key.  This
    # closes verify-then-mutate windows without executing solver code as root.
    rebuilt_after = _build_current_freeze_manifest(
        project=project_path,
        candidate_dir=frozen_candidate_dir,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
        frozen_at=str(frozen.get("frozen_at") or ""),
    )
    if rebuilt_after != frozen:
        _fail("frozen controller/current state changed during grading")
    _verify_frozen_artifacts(project=project_path, manifest=frozen)
    if _sha256_bytes(_read_plain_bytes(manifest_path, label="freeze manifest")) != _sha256_bytes(manifest_payload):
        _fail("freeze manifest changed during grading")

    counts = Counter(item["result"] for item in results)
    grade_report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": GRADE_PHASE,
        "freeze_manifest_sha256": _sha256_bytes(manifest_payload),
        "grader_sha256": _sha256_bytes(grader_payload),
        "record_count": len(results),
        "summary": {name: counts.get(name, 0) for name in sorted(GRADE_RESULTS)},
        "results": results,
    }
    _atomic_write_new(output_path, _json_bytes(grade_report))
    return grade_report


def _run_cli(action: Any, **kwargs: Any) -> None:
    try:
        result = action(**kwargs)
    except BlindEvaluationError as exc:
        typer.echo(f"error: {exc}", err=True)
        raise typer.Exit(code=1) from exc
    typer.echo(json.dumps(result, ensure_ascii=False, sort_keys=True))


def blind_create_seal(
    project: Path = typer.Option(Path("."), "--project"),
    bundle: Path = typer.Option(..., "--bundle"),
    structured_solver_receipt: Path = typer.Option(
        ..., "--structured-solver-receipt"
    ),
    source_first_precommit: Path = typer.Option(
        ..., "--source-first-precommit"
    ),
    independent_review_receipt: Path = typer.Option(
        ..., "--independent-review-receipt"
    ),
    verifier_receipt: Path = typer.Option(..., "--verifier-receipt"),
    dependency_root: Path = typer.Option(..., "--dependency-root"),
    runtime_root: Path = typer.Option(..., "--runtime-root"),
    verifier_snapshot: Path = typer.Option(..., "--verifier-snapshot"),
    output: Path = typer.Option(..., "--output"),
    scope_kind: str = typer.Option("full", "--scope-kind"),
    scope_id: list[str] = typer.Option([], "--scope-id"),
) -> None:
    """Build a root-owned structured-run freeze authorization."""
    _run_cli(
        create_blind_controller_seal,
        project=project,
        bundle=bundle,
        structured_solver_receipt=structured_solver_receipt,
        source_first_precommit=source_first_precommit,
        independent_review_receipt=independent_review_receipt,
        verifier_receipt=verifier_receipt,
        dependency_root=dependency_root,
        runtime_root=runtime_root,
        verifier_snapshot=verifier_snapshot,
        output=output,
        scope_kind=scope_kind,
        scope_ids=scope_id or None,
    )


def blind_create_verifier_snapshot(
    project: Path = typer.Option(Path("."), "--project"),
    dependency_root: Path = typer.Option(..., "--dependency-root"),
    output: Path = typer.Option(..., "--output"),
) -> None:
    """Publish a clean, traversable source snapshot for the verifier UID."""
    _run_cli(
        create_blind_verifier_snapshot,
        project=project,
        dependency_root=dependency_root,
        output=output,
    )


def blind_freeze(
    project: Path = typer.Option(Path("."), "--project", help="Answer-blind Archon project."),
    candidate_dir: Path = typer.Option(
        Path("blind_candidates"),
        "--candidate-dir",
        help="Project-local directory containing exactly <id>.json candidates.",
    ),
    output: Path = typer.Option(..., "--output", help="New atomic freeze-manifest path."),
    controller_seal: Path = typer.Option(
        ..., "--controller-seal", help="External controller-owned freeze authorization."
    ),
    expected_controller_seal_sha256: str = typer.Option(
        ..., "--expected-controller-seal-sha256",
        help="Controller-held SHA-256 of the authorization file.",
    ),
) -> None:
    """Freeze hash-bound answer-blind candidates without reading a grader key."""
    _run_cli(
        freeze_blind_evaluation,
        project=project,
        candidate_dir=candidate_dir,
        output=output,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
    )


def blind_verify_lean(
    project: Path = typer.Option(..., "--project"),
    candidate_dir: Path = typer.Option(Path("blind_candidates"), "--candidate-dir"),
    output: Path = typer.Option(..., "--output"),
    runtime_executable: Path = typer.Option(..., "--runtime-executable"),
    runtime_root: Path = typer.Option(..., "--runtime-root"),
    dependency_root: Path = typer.Option(..., "--dependency-root"),
    expected_dependency_inventory_sha256: str = typer.Option(
        ..., "--expected-dependency-inventory-sha256"
    ),
    expected_snapshot_inventory_sha256: str = typer.Option(
        ..., "--expected-snapshot-inventory-sha256"
    ),
    expected_runtime_inventory_sha256: str = typer.Option(
        ..., "--expected-runtime-inventory-sha256"
    ),
    scope_id: list[str] = typer.Option(..., "--scope-id"),
    timeout_s: int = typer.Option(300, "--timeout-s"),
) -> None:
    """Compile exact result contracts as a dedicated non-root verifier UID."""
    _run_cli(
        verify_blind_lean,
        project=project,
        candidate_dir=candidate_dir,
        output=output,
        runtime_executable=runtime_executable,
        runtime_root=runtime_root,
        dependency_root=dependency_root,
        expected_dependency_inventory_sha256=expected_dependency_inventory_sha256,
        expected_runtime_inventory_sha256=expected_runtime_inventory_sha256,
        expected_snapshot_inventory_sha256=expected_snapshot_inventory_sha256,
        scope_ids=scope_id,
        timeout_s=timeout_s,
    )


def blind_grade(
    project: Path = typer.Option(Path("."), "--project", help="Frozen Archon project."),
    manifest: Path = typer.Option(
        ..., "--manifest", "--freeze-manifest", help="Answer-blind freeze manifest."
    ),
    grader: Path = typer.Option(..., "--grader", help="External post-freeze grader JSONL."),
    output: Path = typer.Option(..., "--output", help="New atomic grade-report path."),
    controller_seal: Path = typer.Option(..., "--controller-seal"),
    expected_controller_seal_sha256: str = typer.Option(
        ..., "--expected-controller-seal-sha256"
    ),
    expected_freeze_sha256: str = typer.Option(..., "--expected-freeze-sha256"),
    expected_grader_sha256: str = typer.Option(..., "--expected-grader-sha256"),
) -> None:
    """Verify a freeze and perform read-only post-freeze grading."""
    _run_cli(
        grade_blind_evaluation,
        project=project,
        manifest=manifest,
        grader=grader,
        output=output,
        controller_seal=controller_seal,
        expected_controller_seal_sha256=expected_controller_seal_sha256,
        expected_freeze_sha256=expected_freeze_sha256,
        expected_grader_sha256=expected_grader_sha256,
    )


__all__ = [
    "BlindEvaluationError",
    "SCHEMA_VERSION",
    "PROTOCOL",
    "create_blind_controller_seal",
    "create_blind_verifier_snapshot",
    "construct_structured_review_records",
    "construct_structured_source_records_commitment",
    "construct_structured_review_envelope",
    "construct_structured_review_semantic",
    "validate_structured_source_records",
    "freeze_blind_evaluation",
    "verify_blind_lean",
    "grade_blind_evaluation",
    "blind_create_seal",
    "blind_create_verifier_snapshot",
    "blind_freeze",
    "blind_verify_lean",
    "blind_grade",
]
