"""Fail-closed problem-input-only contracts for native target Review.

The native answer-blind campaign deliberately removes the blueprint source
marker used by the older candidate/seal workflow.  An explicit answer-blind
workspace must therefore never fall through to the visible-answer Review
contract.  This module binds one questions-only record, its unique generated
source report, problem images, the current Lean candidate, and deterministic
preflight without adding a new runtime state artifact.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import stat
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from ..chemistry_constant import (
    BASELINE_EMPIRICAL_RULE_IDS,
    CONTEST_INTERPRETATION_IDS,
    DORMANT_RUNTIME_BRIDGE_IDS,
    DATASET_SHA256,
    DATASET_VERSION,
    REACTION_TEMPLATE_IDS,
    REFERENCE_ONLY_EMPIRICAL_RULE_IDS,
)
from .answer_submission import (
    AnswerSubmissionError,
    answer_submission_relative_path,
    validate_answer_submission,
    validate_resolved_answer_submission,
)
from .certified_prior_result_context import (
    CertifiedPriorResultContextError,
    load_certified_prior_result_context,
    render_certified_prior_result_prompt,
)
from .numeric_reporting_guard import (
    MAX_NUMERIC_REPORTING_CERTIFICATE_BYTES,
    MAX_NUMERIC_REPORTING_REASON_LENGTH,
)
from .review_source_contract import (
    build_review_source_contract,
    is_answer_blind_contract,
    render_source_contract_prompt,
    source_contract_provenance,
    stored_provenance_matches_current,
    validate_review_source_certificate,
)
from .semantic_dag import (
    SemanticDagError,
    build_semantic_dag,
    render_solver_semantic_dag_prompt,
    semantic_dag_provenance,
)


NATIVE_CONTRACT_KIND = "native_problem_input_only"
NATIVE_CONTRACT_SCHEMA_VERSION = 1
_IMAGE_COMPONENT_ACCOUNTING = "image_component_accounting"
_ALLOWED_AUDIT_REQUIREMENTS = {_IMAGE_COMPONENT_ACCOUNTING}
_COMPOSITION_ACCOUNTING_FIELDS = {
    "source_images",
    "product_nodes",
    "assembly_edges",
    "boundary_checks",
    "components",
    "assembly_expression",
    "combined_formula_or_quantity",
    "lean_carrier",
    "status",
    "evidence",
}
_COMPOSITION_SOURCE_IMAGE_FIELDS = {"path", "sha256"}
_COMPOSITION_PRODUCT_NODE_FIELDS = {
    "node_id",
    "node_kind",
    "formula_or_descriptor",
    "source_path",
    "source_locator",
    "multiplicity",
}
_COMPOSITION_PRODUCT_NODE_KINDS = {
    "repeat_unit",
    "terminal_fragment",
    "cap",
    "adduct",
}
_COMPOSITION_ASSEMBLY_EDGE_FIELDS = {
    "edge_id",
    "from_node_id",
    "to_node_id",
    "relation",
    "multiplicity",
}
_COMPOSITION_ASSEMBLY_RELATIONS = {
    "covalent_bond",
    "repeat_link",
    "terminal_attachment",
    "adduct_association",
}
_COMPOSITION_BOUNDARY_CHECK_FIELDS = {
    "boundary_id",
    "boundary_kind",
    "source_path",
    "source_locator",
    "disposition",
    "assembly_edge_id",
    "status",
}
_COMPOSITION_BOUNDARY_KINDS = {
    "bracket",
    "connector",
    "cross_boundary_bond",
}
_COMPOSITION_BOUNDARY_DISPOSITIONS = {
    "included_in_node",
    "represented_by_edge",
    "product_terminus",
    "excluded_with_source_basis",
    "ambiguous",
}
_COMPOSITION_COMPONENT_FIELDS = {
    "product_node_id",
    "label", "formula_or_descriptor", "multiplicity", "role",
}
_COMPOSITION_COMPONENT_ROLES = {
    "core", "repeat_unit", "linker", "substituent", "terminal_group",
    "guest", "adduct", "leaving_group", "product_fragment",
}
_BLIND_PROTOCOL = "icho-answer-blind-v1"
_SEED_PROTOCOL = "icho-problem-only-solver-seed-v1"
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_COMPOSITION_ID_RE = re.compile(r"^[a-z][a-z0-9_-]{0,63}$")
_MAX_ANSWER_SUBMISSION_BYTES = 1024 * 1024
_MAX_NUMERIC_REPORTING_CERTIFICATES = 256
_PREFLIGHT_FIELDS = {
    "file",
    "status",
    "compiles",
    "returncode",
    "sorry_count",
    "duration_secs",
    "diagnostics",
    "numeric_reporting",
}
_OPTIONAL_PREFLIGHT_FIELDS = {"exhaustiveness_basis"}
_EXHAUSTIVENESS_PREFLIGHT_FIELDS = {
    "status",
    "reason",
    "candidate_declaration",
    "source_admissible_declaration",
    "frozen_domain_declaration",
    "theorem_declaration",
    "expected_type",
    "normalized_type_sha256",
    "candidate_sha256",
    "lean_probe_passed",
    "axioms",
}
_EXHAUSTIVENESS_PREFLIGHT_STATUSES = {"verified", "unavailable"}
_ALLOWED_EXHAUSTIVENESS_AXIOMS = {
    "propext", "Classical.choice", "Quot.sound", "sorryAx",
}
_PREFLIGHT_STATUSES = {"passed", "failed", "timeout", "error", "missing"}
_NUMERIC_REPORTING_CORE_FIELDS = {"active", "status", "reason"}
_NUMERIC_REPORTING_EVIDENCE_FIELDS = _NUMERIC_REPORTING_CORE_FIELDS | {
    "numeric_outputs",
    "lean_source_sha256",
    "bundle_sha256",
    "certificates",
}
_NUMERIC_REPORTING_FINAL_FIELDS = _NUMERIC_REPORTING_EVIDENCE_FIELDS | {
    "lean_probe_passed",
}
_NUMERIC_REPORTING_STATUSES = {
    "passed", "failed", "blocked", "not_applicable", "error",
}
_GENERATED_ENTRY_FIELDS = {
    "blind_record_sha256",
    "image_path",
    "image_paths",
}
_SOURCE_REPORT_KEYS = {
    "blind_record_sha256",
    "command",
    "domain",
    "entry",
    "evaluation_mode",
    "lean_search_packages",
    "next_stage",
    "official_answer_seen",
    "output_lean",
    "part_id",
    "path_base",
    "phase",
    "previous_parts",
    "problem_id",
    "project_path",
    "proof_mode",
    "prover_mode",
    "schema_version",
    "source_report",
    "status",
}
_FORBIDDEN_KEY_PARTS = {
    "answer",
    "explanation",
    "grader",
    "marking",
    "reasoning",
    "rubric",
    "solution",
}


class ProblemOnlyReviewContractError(ValueError):
    """Raised before a model worker when native evidence is not unambiguous."""


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _value_sha256(value: Any) -> str:
    return _sha256_bytes(_canonical_json_bytes(value))


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant {value!r}")


def _strict_json_bytes(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            payload.decode("utf-8", errors="strict"),
            object_pairs_hook=_strict_pairs,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ProblemOnlyReviewContractError(
            f"{label} is not strict UTF-8 JSON: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise ProblemOnlyReviewContractError(f"{label} is not a JSON object")
    return value


def _safe_project_file(project_path: Path, raw: str, *, label: str) -> Path:
    if not isinstance(raw, str) or not raw.strip() or "\\" in raw:
        raise ProblemOnlyReviewContractError(
            f"{label} must be a non-empty POSIX project-relative path"
        )
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise ProblemOnlyReviewContractError(f"{label} escapes the project")
    root = project_path.resolve()
    cursor = root
    for part in relative.parts:
        if part in {"", "."}:
            continue
        cursor = cursor / part
        if cursor.is_symlink():
            raise ProblemOnlyReviewContractError(
                f"{label} may not traverse a symlink: {relative.as_posix()}"
            )
    try:
        resolved = cursor.resolve(strict=True)
        resolved.relative_to(root)
    except (OSError, ValueError) as exc:
        raise ProblemOnlyReviewContractError(
            f"{label} is missing or outside the project: {relative.as_posix()}"
        ) from exc
    if not resolved.is_file():
        raise ProblemOnlyReviewContractError(f"{label} is not a regular file")
    return resolved


def _target_locator(project_path: Path, target: Path) -> tuple[Path, str]:
    root = project_path.resolve()
    lexical = Path(target).absolute()
    try:
        rel = lexical.relative_to(root).as_posix()
    except ValueError as exc:
        raise ProblemOnlyReviewContractError(
            "Lean candidate is outside the project"
        ) from exc
    relative = Path(rel)
    if relative.suffix != ".lean" or relative.name in {"", ".", ".."}:
        raise ProblemOnlyReviewContractError(
            "Lean candidate must be a project-relative .lean target"
        )
    cursor = root
    for part in relative.parts[:-1]:
        cursor = cursor / part
        if cursor.is_symlink():
            raise ProblemOnlyReviewContractError(
                f"Lean candidate may not traverse a symlink: {rel}"
            )
    try:
        cursor.resolve(strict=True).relative_to(root)
    except (OSError, ValueError) as exc:
        raise ProblemOnlyReviewContractError(
            f"Lean candidate parent is missing or outside the project: {rel}"
        ) from exc
    if lexical.is_symlink():
        raise ProblemOnlyReviewContractError(
            f"Lean candidate may not be a symlink: {rel}"
        )
    return lexical, rel


def _target_file(project_path: Path, target: Path) -> tuple[Path, str]:
    root = project_path.resolve()
    _lexical, rel = _target_locator(root, target)
    return _safe_project_file(root, rel, label="Lean candidate"), rel


def _forbidden_paths(value: Any, path: str = "source") -> list[str]:
    found: list[str] = []
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key)
            snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", key)
            normalized = re.sub(r"[^a-z0-9]+", "_", snake.lower()).strip("_")
            parts = [part for part in normalized.split("_") if part]
            child_path = f"{path}.{key}"
            if normalized == "official_answer_seen":
                if child is not False:
                    found.append(child_path)
            elif normalized.startswith("official_") or (
                normalized == "reusable_conclusions"
            ) or any(
                part == stem or part == stem + "s"
                for part in parts
                for stem in _FORBIDDEN_KEY_PARTS
            ):
                found.append(child_path)
            found.extend(_forbidden_paths(child, child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(_forbidden_paths(child, f"{path}[{index}]"))
    return found


def _explicit_answer_blind_mode(project_path: Path) -> str | None:
    config_path = project_path / ".archon" / "config.json"
    if not config_path.exists() and not config_path.is_symlink():
        return None
    config_path = _safe_project_file(
        project_path, ".archon/config.json", label="Archon config",
    )
    config = _strict_json_bytes(
        config_path.read_bytes(), label="Archon config",
    )
    loop = config.get("loop")
    profile = loop.get("domain_profile") if isinstance(loop, Mapping) else None
    profile_name = (
        str(profile.get("name") or "")
        if isinstance(profile, Mapping)
        else ""
    )
    if "answer_blind" not in config:
        if profile_name == "chemistry-native":
            raise ProblemOnlyReviewContractError(
                "chemistry-native config requires explicit answer_blind"
            )
        return None
    blind = config.get("answer_blind")
    if not isinstance(blind, Mapping):
        raise ProblemOnlyReviewContractError(
            "explicit answer_blind config is not an object"
        )
    expected = {
        "authority": "problem-only",
        "official_answer_seen": False,
        "phase": "solve",
        "protocol": _BLIND_PROTOCOL,
    }
    for key, value in expected.items():
        if blind.get(key) != value:
            raise ProblemOnlyReviewContractError(
                f"explicit answer_blind config has invalid {key}"
            )
    isolation = blind.get("isolation")
    if not isinstance(isolation, Mapping) or (
        isolation.get("filesystem_answer_blind") is not True
        or isolation.get("network_answer_blind") is not False
    ):
        raise ProblemOnlyReviewContractError(
            "explicit answer_blind config has invalid isolation claims"
        )
    if not profile_name:
        raise ProblemOnlyReviewContractError(
            "explicit answer_blind config has no domain profile"
        )
    return "native" if profile_name == "chemistry-native" else "strict"


def _validate_numeric_reporting(
    value: Any,
    *,
    expected_lean_sha256: str | None,
    expected_bundle_sha256: str | None,
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting is missing"
        )
    fields = set(value)
    if fields not in (
        _NUMERIC_REPORTING_CORE_FIELDS,
        _NUMERIC_REPORTING_EVIDENCE_FIELDS,
        _NUMERIC_REPORTING_FINAL_FIELDS,
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting fields are ambiguous"
        )
    result = dict(value)
    active = result.get("active")
    status = result.get("status")
    reason = result.get("reason")
    if (
        not isinstance(active, bool)
        or status not in _NUMERIC_REPORTING_STATUSES
        or not isinstance(reason, str)
        or not reason.strip()
        or len(reason) > MAX_NUMERIC_REPORTING_REASON_LENGTH
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting status is invalid"
        )
    if fields == _NUMERIC_REPORTING_CORE_FIELDS:
        if (
            (active is False and status in {"error", "not_applicable"})
            or (active is True and status == "failed")
        ):
            return result
        raise ProblemOnlyReviewContractError(
            "compact numeric_reporting evidence is contradictory"
        )

    count = result.get("numeric_outputs")
    certificates = result.get("certificates")
    lean_sha = result.get("lean_source_sha256")
    bundle_sha = result.get("bundle_sha256")
    try:
        certificate_payloads = [
            _canonical_json_bytes(dict(item))
            for item in certificates
            if isinstance(item, Mapping)
        ] if isinstance(certificates, list) else []
    except (TypeError, ValueError, OverflowError) as exc:
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting certificate is invalid"
        ) from exc
    for index, payload in enumerate(certificate_payloads, start=1):
        _strict_json_bytes(
            payload, label=f"numeric_reporting certificate {index}",
        )
    if (
        isinstance(count, bool)
        or not isinstance(count, int)
        or not 0 <= count <= _MAX_NUMERIC_REPORTING_CERTIFICATES
        or not isinstance(certificates, list)
        or len(certificates) > count
        or len(certificate_payloads) != len(certificates)
        or any(
            len(payload) > MAX_NUMERIC_REPORTING_CERTIFICATE_BYTES
            for payload in certificate_payloads
        )
        or not isinstance(lean_sha, str)
        or bool(lean_sha) != bool(_SHA256_RE.fullmatch(lean_sha))
        or not isinstance(bundle_sha, str)
        or bool(bundle_sha) != bool(_SHA256_RE.fullmatch(bundle_sha))
        or (
            lean_sha
            and expected_lean_sha256 is not None
            and lean_sha != expected_lean_sha256
        )
        or (
            bundle_sha
            and expected_bundle_sha256 is not None
            and bundle_sha != expected_bundle_sha256
        )
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting evidence is invalid"
        )
    probe_present = "lean_probe_passed" in result
    probe = result.get("lean_probe_passed")
    bound = bool(lean_sha and bundle_sha)
    complete = count > 0 and len(certificates) == count
    valid = (
        (
            active is False
            and status == "not_applicable"
            and count == 0
            and not certificates
            and not probe_present
            and not lean_sha
            and not bundle_sha
        )
        or (
            active is True
            and status == "not_applicable"
            and count == 0
            and not certificates
            and not probe_present
            and bound
        )
        or (
            active is True
            and status == "passed"
            and complete
            and probe_present
            and probe is True
            and bound
        )
        or (
            active is True
            and status == "blocked"
            and complete
            and probe_present
            and probe is None
            and bound
        )
        or (
            active is True
            and status == "failed"
            and bound
            and (
                not probe_present
                or (complete and probe is False)
            )
        )
    )
    if not valid:
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight numeric_reporting is contradictory"
        )
    return result


def _validate_exhaustiveness_preflight(
    value: Any,
    *,
    expected_lean_sha256: str | None,
) -> dict[str, Any]:
    """Validate optional audit metadata without requiring fixed declarations."""
    if not isinstance(value, Mapping):
        raise ProblemOnlyReviewContractError(
            "optional deterministic Lean exhaustiveness_basis must be an object"
        )
    if set(value) != _EXHAUSTIVENESS_PREFLIGHT_FIELDS:
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight exhaustiveness_basis fields are invalid"
        )
    result = dict(value)
    status = str(result.get("status") or "").strip().lower()
    reason = str(result.get("reason") or "").strip()
    probe = result.get("lean_probe_passed")
    axioms = result.get("axioms")
    text_fields = (
        "candidate_declaration",
        "source_admissible_declaration",
        "frozen_domain_declaration",
        "theorem_declaration",
        "expected_type",
    )
    if any(
        not isinstance(result.get(key), str)
        or len(result[key]) > 4096
        for key in text_fields
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean exhaustiveness declaration audit is invalid"
        )
    candidate_sha256 = str(result.get("candidate_sha256") or "").lower()
    type_sha256 = str(result.get("normalized_type_sha256") or "").lower()
    if (
        not _SHA256_RE.fullmatch(candidate_sha256)
        or not _SHA256_RE.fullmatch(type_sha256)
        or (
            expected_lean_sha256 is not None
            and candidate_sha256 != expected_lean_sha256
        )
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean exhaustiveness audit hash is stale or invalid"
        )
    if (
        status not in _EXHAUSTIVENESS_PREFLIGHT_STATUSES
        or not reason
        or len(reason) > MAX_NUMERIC_REPORTING_REASON_LENGTH
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean exhaustiveness status/reason is invalid"
        )
    if (
        not isinstance(axioms, list)
        or any(not isinstance(axiom, str) or not axiom for axiom in axioms)
        or axioms != sorted(set(axioms))
        or any(
            axiom not in _ALLOWED_EXHAUSTIVENESS_AXIOMS
            for axiom in axioms
        )
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean exhaustiveness axiom evidence is invalid"
        )
    if status == "verified":
        if probe is not True or any(not result[key] for key in text_fields):
            raise ProblemOnlyReviewContractError(
                "verified Lean exhaustiveness audit is incomplete"
            )
    elif (probe is not False and probe is not None) or axioms:
        raise ProblemOnlyReviewContractError(
            "unavailable Lean exhaustiveness evidence is contradictory"
        )
    result["status"] = status
    result["reason"] = reason
    result["candidate_sha256"] = candidate_sha256
    result["normalized_type_sha256"] = type_sha256
    return result


def _validate_preflight(
    preflight: Mapping[str, Any],
    rel: str,
    *,
    expected_lean_sha256: str | None = None,
    expected_bundle_sha256: str | None = None,
) -> dict[str, Any]:
    if not isinstance(preflight, Mapping):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight is missing"
        )
    fields = set(preflight)
    if (
        not _PREFLIGHT_FIELDS.issubset(fields)
        or fields - (_PREFLIGHT_FIELDS | _OPTIONAL_PREFLIGHT_FIELDS)
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight has missing or ambiguous fields"
        )
    result = dict(preflight)
    if result.get("file") != rel:
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight targets a different Lean candidate"
        )
    status = result.get("status")
    compiles = result.get("compiles")
    returncode = result.get("returncode")
    sorry_count = result.get("sorry_count")
    duration = result.get("duration_secs")
    if status not in _PREFLIGHT_STATUSES or not isinstance(compiles, bool):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight status is invalid"
        )
    if returncode is not None and (
        isinstance(returncode, bool) or not isinstance(returncode, int)
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight returncode is invalid"
        )
    if compiles is not (returncode == 0):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight compile result is contradictory"
        )
    if (
        (status == "passed" and compiles is not True)
        or (status == "failed" and returncode is None)
        or (
            status in {"timeout", "error", "missing"}
            and returncode is not None
        )
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight status is contradictory"
        )
    if sorry_count is not None and (
        isinstance(sorry_count, bool)
        or not isinstance(sorry_count, int)
        or sorry_count < 0
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight sorry_count is invalid"
        )
    if (
        isinstance(duration, bool)
        or not isinstance(duration, (int, float))
        or not math.isfinite(duration)
        or duration < 0
        or not isinstance(result.get("diagnostics"), str)
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight diagnostics are invalid"
        )
    result["numeric_reporting"] = _validate_numeric_reporting(
        result.get("numeric_reporting"),
        expected_lean_sha256=expected_lean_sha256,
        expected_bundle_sha256=expected_bundle_sha256,
    )
    if "exhaustiveness_basis" in result:
        result["exhaustiveness_basis"] = _validate_exhaustiveness_preflight(
            result["exhaustiveness_basis"],
            expected_lean_sha256=expected_lean_sha256,
        )
        if (
            sorry_count == 0
            and "sorryAx" in result["exhaustiveness_basis"]["axioms"]
        ):
            raise ProblemOnlyReviewContractError(
                "zero-sorry preflight contains sorryAx"
            )
    reporting = result["numeric_reporting"]
    if status == "passed" and (
        reporting["active"] is not True
        or reporting["status"] not in {"passed", "not_applicable"}
    ):
        raise ProblemOnlyReviewContractError(
            "passing deterministic Lean preflight has invalid numeric_reporting"
        )
    if reporting["status"] == "passed" and status != "passed":
        raise ProblemOnlyReviewContractError(
            "passing numeric_reporting contradicts failed Lean preflight"
        )
    if status != "passed" and compiles is True and (
        status != "failed"
        or reporting["active"] is not True
        or reporting["status"] != "failed"
    ):
        raise ProblemOnlyReviewContractError(
            "numeric-reporting failure preflight is contradictory"
        )
    return result


def native_problem_only_enabled(project_path: Path) -> bool:
    """Return whether the project explicitly selects the native blind mode."""
    return _explicit_answer_blind_mode(project_path.resolve()) == "native"


def _load_bundle(
    project_path: Path,
) -> tuple[Path, bytes, dict[str, Any], dict[str, dict[str, Any]]]:
    manifest_path = _safe_project_file(
        project_path, "isolation_manifest.json", label="isolation manifest",
    )
    manifest = _strict_json_bytes(
        manifest_path.read_bytes(), label="isolation manifest",
    )
    if (
        manifest.get("schema_version") != 1
        or manifest.get("protocol") != _SEED_PROTOCOL
    ):
        raise ProblemOnlyReviewContractError(
            "isolation manifest is not a problem-only solver seed"
        )
    spec = manifest.get("blind_bundle")
    if not isinstance(spec, Mapping):
        raise ProblemOnlyReviewContractError(
            "isolation manifest blind_bundle is missing"
        )
    bundle_path = _safe_project_file(
        project_path, str(spec.get("path") or ""), label="questions-only bundle",
    )
    payload = bundle_path.read_bytes()
    digest = _sha256_bytes(payload)
    if (
        not _SHA256_RE.fullmatch(str(spec.get("sha256") or ""))
        or spec.get("sha256") != digest
        or manifest.get("blind_bundle_sha256") != digest
        or spec.get("size") != len(payload)
    ):
        raise ProblemOnlyReviewContractError(
            "questions-only bundle does not match the isolation manifest"
        )
    rows: dict[str, dict[str, Any]] = {}
    for line_number, raw_line in enumerate(payload.splitlines(), start=1):
        if not raw_line.strip():
            continue
        row = _strict_json_bytes(
            raw_line, label=f"questions-only row {line_number}",
        )
        record_id = str(row.get("id") or "")
        if not record_id or record_id in rows:
            raise ProblemOnlyReviewContractError(
                "questions-only bundle has a missing or duplicate id"
            )
        rows[record_id] = row
    if spec.get("row_count") != len(rows) or not rows:
        raise ProblemOnlyReviewContractError(
            "questions-only bundle row_count is stale"
        )
    return bundle_path, payload, manifest, rows


def _validate_problem_row(row: Mapping[str, Any], record_id: str) -> None:
    expected = {
        "schema_version": 1,
        "protocol": _BLIND_PROTOCOL,
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "phase": "solve",
        "id": record_id,
        "index": record_id,
    }
    for key, value in expected.items():
        if row.get(key) != value:
            raise ProblemOnlyReviewContractError(
                f"questions-only record has invalid {key}"
            )
    for key in ("question", "current_question"):
        if not isinstance(row.get(key), str) or not str(row.get(key)).strip():
            raise ProblemOnlyReviewContractError(
                f"questions-only record has no {key}"
            )
    for key in ("previous_parts", "requested_outputs", "problem_assets"):
        value = row.get(key)
        if not isinstance(value, list) or (
            key in {"requested_outputs", "problem_assets"} and not value
        ):
            raise ProblemOnlyReviewContractError(
                f"questions-only record has invalid {key}"
            )
    requested_ids: set[str] = set()
    requested_requirements: set[str] = set()
    for index, item in enumerate(row["requested_outputs"], start=1):
        if not isinstance(item, Mapping):
            raise ProblemOnlyReviewContractError(
                f"questions-only requested output {index} is not an object"
            )
        output_id = item.get("id")
        requirement = item.get("source_requirement")
        audit_requirements = item.get("audit_requirements")
        if audit_requirements is not None and (
            not isinstance(audit_requirements, list)
            or not audit_requirements
            or not all(isinstance(value, str) for value in audit_requirements)
            or len(set(audit_requirements)) != len(audit_requirements)
            or any(
                value not in _ALLOWED_AUDIT_REQUIREMENTS
                for value in audit_requirements
            )
        ):
            raise ProblemOnlyReviewContractError(
                f"questions-only requested output {index} has invalid audit_requirements"
            )
        if (
            not isinstance(output_id, str)
            or not output_id
            or output_id in requested_ids
            or not isinstance(requirement, str)
            or not requirement
            or requirement in requested_requirements
        ):
            raise ProblemOnlyReviewContractError(
                "questions-only requested outputs are missing or ambiguous"
            )
        requested_ids.add(output_id)
        requested_requirements.add(requirement)
    for key in (
        "candidate_domain_policy",
        "measurement_policy",
        "reporting_policy",
    ):
        if not isinstance(row.get(key), Mapping) or not row.get(key):
            raise ProblemOnlyReviewContractError(
                f"questions-only record has invalid {key}"
            )
    forbidden = _forbidden_paths(row, path="questions_only")
    if forbidden:
        raise ProblemOnlyReviewContractError(
            "questions-only record contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )


def _validated_answer_submission_binding(
    project_path: Path,
    *,
    row: Mapping[str, Any],
    record_id: str,
    require_resolved: bool = False,
) -> tuple[str, str]:
    """Validate one generated answer artifact, retaining no answer values."""

    rel = answer_submission_relative_path(record_id).as_posix()
    path = _safe_project_file(
        project_path, rel, label="target answer submission",
    )
    metadata = path.stat()
    if metadata.st_nlink != 1 or metadata.st_size > _MAX_ANSWER_SUBMISSION_BYTES:
        raise ProblemOnlyReviewContractError(
            "target answer submission must be a bounded single-linked file"
        )
    payload = path.read_bytes()
    if len(payload) > _MAX_ANSWER_SUBMISSION_BYTES:
        raise ProblemOnlyReviewContractError(
            "target answer submission exceeds the size limit"
        )
    submission = _strict_json_bytes(
        payload, label="target answer submission",
    )
    try:
        validator = (
            validate_resolved_answer_submission
            if require_resolved
            else validate_answer_submission
        )
        validator(submission, row=row, target_id=record_id)
    except AnswerSubmissionError as exc:
        raise ProblemOnlyReviewContractError(
            f"target answer submission is invalid: {exc}"
        ) from exc
    return rel, _sha256_bytes(payload)


def _validate_native_answer_submission_current(
    *, project_path: Path, target: Path, require_resolved: bool,
) -> tuple[dict[str, str] | None, str]:
    """Validate a worker sidecar while retaining no generated answer values."""

    root = project_path.resolve()
    try:
        if _explicit_answer_blind_mode(root) != "native":
            raise ProblemOnlyReviewContractError(
                "answer submission validation requires native blind mode"
            )
        target_path, _rel = _target_locator(root, target)
        if not target_path.stem.startswith("problem_"):
            raise ProblemOnlyReviewContractError(
                "native Lean candidate name does not identify a problem record"
            )
        record_id = target_path.stem.removeprefix("problem_")
        _bundle_path, _bundle_payload, _manifest, rows = _load_bundle(root)
        row = rows.get(record_id)
        if row is None:
            raise ProblemOnlyReviewContractError(
                "Lean candidate has no unique questions-only record"
            )
        _validate_problem_row(row, record_id)
        rel, digest = _validated_answer_submission_binding(
            root, row=row, record_id=record_id,
            require_resolved=require_resolved,
        )
        return {"path": rel, "sha256": digest}, ""
    except (ProblemOnlyReviewContractError, AnswerSubmissionError) as exc:
        return None, str(exc)


def validate_native_answer_submission_current(
    *, project_path: Path, target: Path,
) -> tuple[dict[str, str] | None, str]:
    """Validate a worker sidecar, allowing a fail-closed diagnostic value."""

    return _validate_native_answer_submission_current(
        project_path=project_path,
        target=target,
        require_resolved=False,
    )


def validate_native_resolved_answer_submission_current(
    *, project_path: Path, target: Path,
) -> tuple[dict[str, str] | None, str]:
    """Validate that a worker sidecar contains a resolved requested output."""

    return _validate_native_answer_submission_current(
        project_path=project_path,
        target=target,
        require_resolved=True,
    )


def _matching_source_report(
    project_path: Path, target_stem: str,
) -> tuple[Path, dict[str, Any], bytes]:
    reports_root = project_path / "reports"
    matches = sorted(reports_root.rglob(f"{target_stem}.source.json")) if (
        reports_root.is_dir()
    ) else []
    if len(matches) != 1:
        raise ProblemOnlyReviewContractError(
            "expected exactly one matching problem-side source report; "
            f"found {len(matches)}"
        )
    try:
        rel = matches[0].relative_to(project_path).as_posix()
    except ValueError as exc:
        raise ProblemOnlyReviewContractError(
            "matching source report escapes the project"
        ) from exc
    path = _safe_project_file(
        project_path, rel, label="problem-side source report",
    )
    payload = path.read_bytes()
    return path, _strict_json_bytes(payload, label="problem-side source report"), payload


def _normalized_bundle_row(row: Mapping[str, Any]) -> dict[str, Any]:
    normalized = dict(row)
    normalized["question"] = str(normalized.get("question") or "").strip()
    normalized["index"] = str(normalized.get("index") or normalized.get("id"))
    if "category" in normalized:
        normalized["category"] = str(normalized["category"])
    return normalized


def _validate_source_report(
    *,
    project_path: Path,
    report_path: Path,
    report: Mapping[str, Any],
    rel: str,
    row: Mapping[str, Any],
    record_sha256: str,
) -> list[dict[str, str]]:
    report_rel = report_path.relative_to(project_path).as_posix()
    if set(report) != _SOURCE_REPORT_KEYS:
        raise ProblemOnlyReviewContractError(
            "problem-side source report has unexpected or missing fields"
        )
    expected = {
        "schema_version": 3,
        "command": "physics-formalize",
        "domain": "chemistry",
        "evaluation_mode": "answer_blind",
        "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
        "next_stage": "autoformalize",
        "official_answer_seen": False,
        "phase": "solve",
        "proof_mode": "chemistry",
        "prover_mode": "chemistry-formalize",
        "status": "prepared",
        "path_base": "project",
        "project_path": ".",
        "output_lean": rel,
        "source_report": report_rel,
        "blind_record_sha256": record_sha256,
    }
    for key, value in expected.items():
        if report.get(key) != value:
            raise ProblemOnlyReviewContractError(
                f"problem-side source report has invalid {key}"
            )
    forbidden = _forbidden_paths(report, path="source_report")
    if forbidden:
        raise ProblemOnlyReviewContractError(
            "problem-side source report contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )
    entry = report.get("entry")
    if not isinstance(entry, Mapping):
        raise ProblemOnlyReviewContractError(
            "problem-side source report entry is missing"
        )
    base_entry = {
        key: value
        for key, value in entry.items()
        if key not in _GENERATED_ENTRY_FIELDS
    }
    if base_entry != _normalized_bundle_row(row):
        raise ProblemOnlyReviewContractError(
            "problem-side source report entry differs from questions-only record"
        )
    if entry.get("blind_record_sha256") != record_sha256:
        raise ProblemOnlyReviewContractError(
            "problem-side source report entry has a stale record hash"
        )
    previous_parts = row.get("previous_parts")
    if (
        report.get("previous_parts") != previous_parts
        or report.get("problem_id") != row.get("problem_id")
        or report.get("part_id") != row.get("part_id")
    ):
        raise ProblemOnlyReviewContractError(
            "problem-side source report identity fields disagree with the bundle"
        )
    raw_image_paths = entry.get("image_paths")
    if (
        not isinstance(raw_image_paths, list)
        or not raw_image_paths
        or len(raw_image_paths) != len(set(raw_image_paths))
        or entry.get("image_path") != raw_image_paths[0]
    ):
        raise ProblemOnlyReviewContractError(
            "problem-side source report image paths are missing or ambiguous"
        )
    page_assets = row.get("problem_assets")
    expected_pages = {
        str(item.get("path") or ""): str(item.get("sha256") or "")
        for item in page_assets
        if isinstance(item, Mapping) and item.get("kind") == "problem_page"
    }
    images: list[dict[str, str]] = []
    for raw_path in raw_image_paths:
        path = _safe_project_file(
            project_path, raw_path, label="problem image",
        )
        locator = path.relative_to(project_path).as_posix()
        digest = _sha256_bytes(path.read_bytes())
        if expected_pages.get(path.name) != digest:
            raise ProblemOnlyReviewContractError(
                "problem image does not match questions-only problem_assets"
            )
        images.append({"path": locator, "sha256": digest})
    if {Path(item["path"]).name for item in images} != set(expected_pages):
        raise ProblemOnlyReviewContractError(
            "problem-side source report does not cover every problem image"
        )
    return images


def _build_native_contract(
    *,
    project_path: Path,
    target: Path,
    preflight: Mapping[str, Any] | None,
    require_candidate: bool = True,
    include_answer_submission: bool = True,
) -> dict[str, Any]:
    project_path = project_path.resolve()
    if require_candidate:
        target_path, rel = _target_file(project_path, target)
    else:
        target_path, rel = _target_locator(project_path, target)
    if not target_path.stem.startswith("problem_"):
        raise ProblemOnlyReviewContractError(
            "native Lean candidate name does not identify a problem record"
        )
    record_id = target_path.stem.removeprefix("problem_")
    candidate_sha256 = (
        _sha256_bytes(target_path.read_bytes()) if require_candidate else None
    )
    bundle_path, bundle_payload, manifest, rows = _load_bundle(project_path)
    bundle_sha256 = _sha256_bytes(bundle_payload)
    preflight_row = (
        _validate_preflight(
            preflight,
            rel,
            expected_lean_sha256=candidate_sha256,
            expected_bundle_sha256=bundle_sha256,
        )
        if preflight is not None else None
    )
    row = rows.get(record_id)
    if row is None:
        raise ProblemOnlyReviewContractError(
            "Lean candidate has no unique questions-only record"
        )
    _validate_problem_row(row, record_id)
    record_sha256 = _sha256_bytes(_canonical_json_bytes(row))
    submission_binding: dict[str, str] = {}
    if include_answer_submission:
        submission_rel, submission_sha256 = _validated_answer_submission_binding(
            project_path, row=row, record_id=record_id,
        )
        submission_binding = {
            "answer_submission": submission_rel,
            "answer_submission_sha256": submission_sha256,
        }
    report_path, report, report_payload = _matching_source_report(
        project_path, target_path.stem,
    )
    images = _validate_source_report(
        project_path=project_path,
        report_path=report_path,
        report=report,
        rel=rel,
        row=row,
        record_sha256=record_sha256,
    )
    manifest_assets = manifest.get("assets")
    if not isinstance(manifest_assets, Mapping):
        raise ProblemOnlyReviewContractError(
            "isolation manifest assets are missing"
        )
    for image in images:
        if manifest_assets.get(image["path"]) != image["sha256"]:
            raise ProblemOnlyReviewContractError(
                "problem image does not match the isolation manifest"
            )
    evidence = {
        "question": str(row["question"]).strip(),
        "current_question": str(row["current_question"]).strip(),
        "shared_context": str(row.get("shared_context") or "").strip(),
        "previous_parts": row["previous_parts"],
        "requested_outputs": row["requested_outputs"],
        "reporting_policy": row["reporting_policy"],
        "measurement_policy": row["measurement_policy"],
        "candidate_domain_policy": row["candidate_domain_policy"],
    }
    try:
        certified_prior_result = load_certified_prior_result_context(
            project_path=project_path,
            consumer_record_id=record_id,
            consumer_target_rel=rel,
            source_bundle_sha256=bundle_sha256,
            source_record_sha256=record_sha256,
            previous_parts=row["previous_parts"],
            trusted_controller_uid=0,
        )
    except CertifiedPriorResultContextError as exc:
        raise ProblemOnlyReviewContractError(str(exc)) from exc
    try:
        semantic_dag = build_semantic_dag(
            record_id=record_id,
            problem_evidence=evidence,
        )
        semantic_provenance = semantic_dag_provenance(semantic_dag)
    except SemanticDagError as exc:
        raise ProblemOnlyReviewContractError(
            f"problem-side semantic DAG is invalid: {exc}"
        ) from exc
    contract = {
        "schema_version": NATIVE_CONTRACT_SCHEMA_VERSION,
        "contract_kind": NATIVE_CONTRACT_KIND,
        "required": True,
        "available": True,
        "valid": True,
        "domain": "chemistry-native",
        "evaluation_mode": "answer_blind",
        "authority": "problem-only",
        "target": rel,
        "source_bundle": bundle_path.relative_to(project_path).as_posix(),
        "source_bundle_sha256": bundle_sha256,
        "source_record_id": record_id,
        "source_record_sha256": record_sha256,
        **submission_binding,
        "chemistry_constant_dataset": {
            "version": DATASET_VERSION,
            "sha256": DATASET_SHA256,
        },
        "source_report": report_path.relative_to(project_path).as_posix(),
        "source_report_sha256": _sha256_bytes(report_payload),
        "candidate": rel,
        "candidate_sha256": candidate_sha256,
        "preflight_sha256": (
            _value_sha256(preflight_row) if preflight_row is not None else None
        ),
        "question_sha256": _value_sha256(evidence["question"]),
        "shared_context_sha256": _value_sha256(evidence["shared_context"]),
        "previous_parts_sha256": _value_sha256(evidence["previous_parts"]),
        "requested_outputs_sha256": _value_sha256(
            evidence["requested_outputs"]
        ),
        "reporting_policy_sha256": _value_sha256(
            evidence["reporting_policy"]
        ),
        "measurement_policy_sha256": _value_sha256(
            evidence["measurement_policy"]
        ),
        "candidate_domain_policy_sha256": _value_sha256(
            evidence["candidate_domain_policy"]
        ),
        "certified_prior_result_path": certified_prior_result.get("path"),
        "certified_prior_result_sha256": certified_prior_result.get("sha256"),
        "certified_prior_result_context_receipt_sha256": (
            certified_prior_result.get("context_receipt_sha256")
        ),
        "certified_prior_result": certified_prior_result,
        "images": images,
        "problem_evidence": evidence,
        "semantic_dag": semantic_dag,
        "semantic_dag_provenance": semantic_provenance,
        "preflight": preflight_row,
        "errors": [],
    }
    return contract


def native_problem_image_args(
    *,
    project_path: Path,
    target: Path,
    harness: Any,
    source_contract: Mapping[str, Any] | None = None,
) -> list[str]:
    """Return hash-verified Codex ``--image`` arguments for one target.

    Native problem-only prompts must receive pixels, not merely image path and
    digest text. Image inventory is rebuilt from the sealed questions-only
    bundle before a candidate exists, or reused from a fully validated Review
    contract. A native campaign fails before model launch when its selected
    harness cannot attach images.
    """
    root = project_path.resolve()
    mode = _explicit_answer_blind_mode(root)
    if source_contract is not None:
        if not is_native_problem_only_contract(source_contract):
            if mode == "native":
                raise ProblemOnlyReviewContractError(
                    "native problem image attachment has no valid source contract"
                )
            return []
        images = source_contract.get("images")
    elif mode == "native":
        images = _build_native_contract(
            project_path=root,
            target=target,
            preflight=None,
            require_candidate=False,
            include_answer_submission=False,
        ).get("images")
    else:
        return []
    if not isinstance(images, list) or not images:
        raise ProblemOnlyReviewContractError(
            "native problem image inventory is missing"
        )
    if getattr(harness, "runner", None) != "codex":
        raise ProblemOnlyReviewContractError(
            "native problem images require a Codex --image capable harness"
        )
    args: list[str] = []
    seen: set[str] = set()
    for index, item in enumerate(images, start=1):
        if not isinstance(item, Mapping):
            raise ProblemOnlyReviewContractError(
                f"native problem image {index} is not an object"
            )
        path = _safe_project_file(
            root,
            item.get("path"),
            label=f"native problem image {index}",
        )
        digest = _sha256_bytes(path.read_bytes())
        if item.get("sha256") != digest or str(path) in seen:
            raise ProblemOnlyReviewContractError(
                f"native problem image {index} is stale or duplicated"
            )
        seen.add(str(path))
        args.extend(("--image", str(path)))
    # Codex 0.147 declares ``--image <FILE>...`` as variadic. Without an
    # explicit option terminator, Codex consumes Archon's final positional
    # prompt as one more image and exits with "No prompt provided via stdin".
    # CodexAgent appends the prompt after these extra args, so terminate image
    # option parsing here while keeping the prompt as the final argv item.
    args.append("--")
    return args


def is_native_problem_only_contract(contract: Mapping[str, Any] | None) -> bool:
    return bool(contract) and contract.get("contract_kind") == NATIVE_CONTRACT_KIND


def resolve_native_formalizer_source_contract(
    *, project_path: Path, target: Path,
) -> dict[str, Any]:
    """Build source/DAG input before a Formalizer has written its answer."""

    if _explicit_answer_blind_mode(project_path.resolve()) != "native":
        raise ProblemOnlyReviewContractError(
            "native Formalizer contract requires chemistry-native blind mode"
        )
    return _build_native_contract(
        project_path=project_path,
        target=target,
        preflight=None,
        require_candidate=False,
        include_answer_submission=False,
    )


def resolve_target_review_source_contract(
    *,
    project_path: Path,
    target: Path,
    preflight: Mapping[str, Any] | None = None,
    supplied_contract: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Resolve the right contract without blind-to-visible fallback."""
    mode = _explicit_answer_blind_mode(project_path.resolve())
    if mode == "native":
        fresh = _build_native_contract(
            project_path=project_path, target=target, preflight=preflight,
        )
        if supplied_contract is not None:
            if (
                not is_native_problem_only_contract(supplied_contract)
                or supplied_contract != fresh
            ):
                raise ProblemOnlyReviewContractError(
                    "supplied native Review contract is stale or inconsistent"
                )
            return supplied_contract
        return fresh
    if mode == "strict":
        contract = build_review_source_contract(
            project_path=project_path, target=target,
        )
        if (
            not is_answer_blind_contract(contract)
            or contract.get("authority") != "problem-only"
            or contract.get("valid") is not True
            or contract.get("errors")
        ):
            raise ProblemOnlyReviewContractError(
                "explicit answer_blind workspace has no valid blind source contract"
            )
        return contract
    if supplied_contract:
        return supplied_contract
    return build_review_source_contract(
        project_path=project_path, target=target,
    )


def native_source_contract_provenance(
    contract: Mapping[str, Any],
) -> dict[str, Any]:
    if not is_native_problem_only_contract(contract):
        return source_contract_provenance(contract)
    keys = (
        "schema_version",
        "contract_kind",
        "authority",
        "evaluation_mode",
        "target",
        "source_bundle",
        "source_bundle_sha256",
        "source_record_id",
        "source_record_sha256",
        "answer_submission",
        "answer_submission_sha256",
        "chemistry_constant_dataset",
        "source_report",
        "source_report_sha256",
        "candidate",
        "preflight_sha256",
        "candidate_sha256",
        "question_sha256",
        "shared_context_sha256",
        "previous_parts_sha256",
        "requested_outputs_sha256",
        "reporting_policy_sha256",
        "measurement_policy_sha256",
        "candidate_domain_policy_sha256",
        "certified_prior_result_path",
        "certified_prior_result_sha256",
        "certified_prior_result_context_receipt_sha256",
        "images",
    )
    provenance = {key: contract.get(key) for key in keys}
    provenance["semantic_dag"] = contract.get("semantic_dag_provenance")
    return provenance


def materialize_controller_review_provenance(
    *,
    path: Path,
    expected_rel: str,
    expected_contract: Mapping[str, Any] | None,
    review_field: str,
) -> str:
    """Persist the native source binding without changing Review semantics.

    Source provenance is wholly controller-derived. Asking a model to
    reproduce long digests made an otherwise valid certificate vulnerable to
    transcription errors. Keep every verdict and audit field model-owned, but
    replace this one deterministic object before the sealed loader runs.
    Malformed or out-of-scope milestones are deliberately left untouched so
    the existing validator still rejects them.
    """
    if not is_native_problem_only_contract(expected_contract):
        return ""
    if review_field not in {"proof_review", "formalization_review"}:
        return f"unsupported Review provenance field {review_field!r}"
    try:
        original_lstat = path.lstat()
    except FileNotFoundError:
        return ""
    except OSError as exc:
        return f"cannot bind controller-owned Review provenance: {exc}"
    if not stat.S_ISREG(original_lstat.st_mode):
        return "Review milestone must be a regular file, not a symlink"
    source_fd = -1
    try:
        source_fd = os.open(
            path,
            os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        source_stat = os.fstat(source_fd)
        if (
            source_stat.st_dev != original_lstat.st_dev
            or source_stat.st_ino != original_lstat.st_ino
            or not stat.S_ISREG(source_stat.st_mode)
        ):
            return "Review milestone changed while binding provenance"
        with os.fdopen(source_fd, "rb") as source:
            source_fd = -1
            source_bytes = source.read()
        lines = source_bytes.decode("utf-8", errors="strict").splitlines()
    except UnicodeDecodeError as exc:
        return f"cannot bind controller-owned Review provenance: {exc}"
    except OSError as exc:
        return f"cannot bind controller-owned Review provenance: {exc}"
    finally:
        if source_fd >= 0:
            os.close(source_fd)
    payloads = [line for line in lines if line.strip()]
    if len(payloads) != 1:
        return ""
    try:
        row = json.loads(
            payloads[0],
            object_pairs_hook=_strict_pairs,
            parse_constant=_reject_json_constant,
        )
    except (json.JSONDecodeError, ValueError):
        return ""
    if not isinstance(row, dict):
        return ""
    target = row.get("target")
    review = row.get(review_field)
    if (
        not isinstance(target, Mapping)
        or str(target.get("file") or "").lstrip("./") != expected_rel
        or not isinstance(review, Mapping)
    ):
        return ""
    expected = native_source_contract_provenance(expected_contract)
    if review.get("source_contract") == expected:
        return ""
    bound_review = dict(review)
    bound_review["source_contract"] = expected
    bound_row = dict(row)
    bound_row[review_field] = bound_review
    tmp = path.with_suffix(path.suffix + ".controller.tmp")
    replacement = (
        json.dumps(bound_row, ensure_ascii=False, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")
    tmp_fd = -1
    tmp_created = False
    try:
        tmp_fd = os.open(
            tmp,
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | os.O_CLOEXEC
            | os.O_NOFOLLOW,
            0o600,
        )
        tmp_created = True
        initial_tmp_stat = os.fstat(tmp_fd)
        if (
            initial_tmp_stat.st_uid != original_lstat.st_uid
            or initial_tmp_stat.st_gid != original_lstat.st_gid
        ):
            os.fchown(tmp_fd, original_lstat.st_uid, original_lstat.st_gid)
        os.fchmod(tmp_fd, stat.S_IMODE(original_lstat.st_mode))
        with os.fdopen(tmp_fd, "wb") as destination:
            tmp_fd = -1
            destination.write(replacement)
            destination.flush()
            os.fsync(destination.fileno())
        replacement_stat = tmp.lstat()
        if (
            not stat.S_ISREG(replacement_stat.st_mode)
            or replacement_stat.st_uid != original_lstat.st_uid
            or replacement_stat.st_gid != original_lstat.st_gid
            or stat.S_IMODE(replacement_stat.st_mode)
            != stat.S_IMODE(original_lstat.st_mode)
        ):
            return "controller-owned Review provenance replacement metadata changed"
        current_lstat = path.lstat()
        if (
            current_lstat.st_dev != original_lstat.st_dev
            or current_lstat.st_ino != original_lstat.st_ino
            or current_lstat.st_uid != original_lstat.st_uid
            or current_lstat.st_gid != original_lstat.st_gid
            or stat.S_IMODE(current_lstat.st_mode)
            != stat.S_IMODE(original_lstat.st_mode)
            or not stat.S_ISREG(current_lstat.st_mode)
        ):
            return "Review milestone changed while binding provenance"
        os.replace(tmp, path)
        tmp_created = False
        directory_fd = os.open(
            path.parent,
            os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except OSError as exc:
        return f"cannot persist controller-owned Review provenance: {exc}"
    finally:
        if tmp_fd >= 0:
            os.close(tmp_fd)
        if tmp_created:
            try:
                tmp.unlink()
            except OSError:
                pass
    return ""


def render_native_formalizer_semantic_dag_prompt(
    contract: Mapping[str, Any],
) -> str:
    """Render only the controller DAG block used by native Formalizers."""
    if not is_native_problem_only_contract(contract):
        return ""
    dag = contract.get("semantic_dag")
    provenance = contract.get("semantic_dag_provenance")
    if not isinstance(dag, Mapping) or not isinstance(provenance, Mapping):
        raise ProblemOnlyReviewContractError(
            "native problem-only contract has no semantic DAG"
        )
    try:
        return render_solver_semantic_dag_prompt(dag, provenance)
    except SemanticDagError as exc:
        raise ProblemOnlyReviewContractError(
            f"native problem-only semantic DAG is stale: {exc}"
        ) from exc


def render_native_composition_accounting_prompt(
    contract: Mapping[str, Any],
) -> str:
    """Render the controller-selected image component ledger obligation."""

    if not is_native_problem_only_contract(contract):
        return ""
    evidence = contract.get("problem_evidence")
    requested_outputs = (
        evidence.get("requested_outputs")
        if isinstance(evidence, Mapping)
        else None
    )
    if not isinstance(requested_outputs, list):
        raise ProblemOnlyReviewContractError(
            "native contract has no requested output inventory"
        )
    output_ids = [
        output.get("id")
        for output in requested_outputs
        if isinstance(output, Mapping)
        and isinstance(output.get("audit_requirements"), list)
        and _IMAGE_COMPONENT_ACCOUNTING
        in output.get("audit_requirements", [])
    ]
    if not output_ids:
        return ""
    if not all(isinstance(output_id, str) and output_id for output_id in output_ids):
        raise ProblemOnlyReviewContractError(
            "native component accounting output id is invalid"
        )
    template = {
        "source_images": [{
            "path": "<exact bound source_contract image path>",
            "sha256": "<its exact bound digest>",
        }],
        "product_nodes": [{
            "node_id": "<stable lowercase id>",
            "node_kind": "<one fixed allowed kind>",
            "formula_or_descriptor": "<whole visual unit/fragment descriptor>",
            "source_path": "<exact bound image path>",
            "source_locator": "<bracket/box/bond/region locator>",
            "multiplicity": "<positive JSON integer>",
        }],
        "assembly_edges": [{
            "edge_id": "<stable lowercase id>",
            "from_node_id": "<existing product node id>",
            "to_node_id": "<different existing product node id>",
            "relation": "<one fixed allowed relation>",
            "multiplicity": "<positive JSON integer>",
        }],
        "boundary_checks": [{
            "boundary_id": "<stable lowercase id>",
            "boundary_kind": "bracket|connector|cross_boundary_bond",
            "source_path": "<exact bound image path>",
            "source_locator": "<precise visual locator>",
            "disposition": "<one fixed allowed disposition>",
            "assembly_edge_id": "<represented edge id or none>",
            "status": "resolved|ambiguous",
        }],
        "components": [{
            "label": "<source-local component label>",
            "formula_or_descriptor": "<formula or visual descriptor>",
            "multiplicity": "<positive JSON integer>",
            "role": "<one fixed allowed role>",
            "product_node_id": "<existing product node id>",
        }],
        "assembly_expression": "<complete component assembly before arithmetic>",
        "combined_formula_or_quantity": "<independently recombined result>",
        "lean_carrier": "<same carrier as the parent requested output>",
        "status": "matched|failed",
        "evidence": "<independent visual recount and consistency audit>",
    }
    return (
        "MANDATORY IMAGE COMPONENT ACCOUNTING (controller-selected):\n"
        "- Exact opt-in output ids: "
        + json.dumps(output_ids, ensure_ascii=False)
        + "\n- For each id, inspect every bound image first and independently "
        "trace the whole product topology before making a component/formula "
        "ledger or doing arithmetic. A printed formula label may denote only "
        "a residue: never assume it is the whole product until every outgoing "
        "bond from its bracket/box, every connector and cross-boundary bond, "
        "and the preceding-page unit pattern have been traced across all "
        "bound images. Record whole visibly repeated units, terminal "
        "fragments, caps, and adducts as product_nodes; then connect them with "
        "assembly_edges. Add one boundary_check for every visible bracket, "
        "connector, and cross-boundary bond. Only after this topology is "
        "complete may components, assembly_expression, and the combined "
        "formula/quantity be recombined. In that requested_outputs certificate "
        "entry include "
        "composition_accounting with exactly this shape: "
        + json.dumps(template, ensure_ascii=False, sort_keys=True)
        + "\n- Allowed product node kinds: "
        + json.dumps(sorted(_COMPOSITION_PRODUCT_NODE_KINDS))
        + "; allowed assembly relations: "
        + json.dumps(sorted(_COMPOSITION_ASSEMBLY_RELATIONS))
        + "; allowed boundary dispositions: "
        + json.dumps(sorted(_COMPOSITION_BOUNDARY_DISPOSITIONS))
        + "\n- Allowed component roles: "
        + json.dumps(sorted(_COMPOSITION_COMPONENT_ROLES))
        + ". source_images must exactly cover all bound path/digest pairs, "
        "and product_nodes must cover all bound image paths. "
        "assembly_expression must contain every product_nodes[].node_id "
        "verbatim as a standalone token; labels or formulas alone do not "
        "satisfy this requirement. IDs must be unique stable lowercase "
        "tokens, references valid, multiplicities "
        "positive JSON integers, and the complete node graph connected. At "
        "least two non-adduct product nodes and an edge between non-adduct "
        "nodes are mandatory. A represented_by_edge boundary must name that "
        "edge; every other resolved disposition must use assembly_edge_id="
        "none. A passing/matched audit may contain no ambiguous boundary. "
        "Use status=matched only after the independent recount, assembly, "
        "combined formula/quantity, submitted output, and Lean carrier all "
        "agree. Otherwise use failed and a failing route. not_applicable is "
        "forbidden. Omit composition_accounting from non-opt-in outputs."
    )


def render_native_formalizer_composition_accounting_prompt(
    contract: Mapping[str, Any],
) -> str:
    """Render the Formalizer obligation without Review-certificate syntax."""

    if not is_native_problem_only_contract(contract):
        return ""
    evidence = contract.get("problem_evidence")
    requested_outputs = (
        evidence.get("requested_outputs")
        if isinstance(evidence, Mapping)
        else None
    )
    if not isinstance(requested_outputs, list):
        raise ProblemOnlyReviewContractError(
            "native contract has no requested output inventory"
        )
    output_ids = [
        output.get("id")
        for output in requested_outputs
        if isinstance(output, Mapping)
        and isinstance(output.get("audit_requirements"), list)
        and _IMAGE_COMPONENT_ACCOUNTING
        in output.get("audit_requirements", [])
    ]
    if not output_ids:
        return ""
    if not all(isinstance(output_id, str) and output_id for output_id in output_ids):
        raise ProblemOnlyReviewContractError(
            "native component accounting output id is invalid"
        )
    return (
        "MANDATORY WHOLE-PRODUCT IMAGE TOPOLOGY (Formalizer obligation):\n"
        "- Exact opt-in output ids: "
        + json.dumps(output_ids, ensure_ascii=False)
        + "\n- Before arithmetic, inspect every bound image and trace the whole "
        "assembled product. Treat printed formula labels as possible residues, "
        "not automatically as complete products. Record product nodes, their "
        "positive integer multiplicities, assembly edges, every visible "
        "bracket/connector/cross-boundary bond, a component-to-node ledger, "
        "and the final recombination in the assigned Lean file and task report. "
        "Every product node must appear exactly once in that ledger with the "
        "same multiplicity. If any boundary or multiplicity is ambiguous, keep "
        "the output blocked instead of using a single-fragment shortcut.\n"
        "- The structured composition_accounting object belongs only to the "
        "Review certificate. NEVER add composition_accounting, topology, nodes, "
        "edges, ledgers, or any other field to the target .answer.json. That "
        "file must retain exactly the separately stated five-field output "
        "schema."
    )


def render_native_formalizer_answer_submission_prompt(
    contract: Mapping[str, Any],
) -> str:
    """Render the exact answer artifact contract without candidate values."""

    if not is_native_problem_only_contract(contract):
        return ""
    record_id = contract.get("source_record_id")
    evidence = contract.get("problem_evidence")
    requested_outputs = (
        evidence.get("requested_outputs")
        if isinstance(evidence, Mapping)
        else None
    )
    if not isinstance(record_id, str) or not isinstance(requested_outputs, list):
        raise ProblemOnlyReviewContractError(
            "native Formalizer contract has no requested output inventory"
        )
    output_contracts: list[dict[str, Any]] = []
    output_template: list[dict[str, Any]] = []
    for index, output in enumerate(requested_outputs, start=1):
        if not isinstance(output, Mapping):
            raise ProblemOnlyReviewContractError(
                f"native requested output {index} is not an object"
            )
        output_id = output.get("id")
        kind = output.get("kind")
        unit = output.get("unit")
        if not (
            isinstance(output_id, str)
            and isinstance(kind, str)
            and isinstance(unit, str)
        ):
            raise ProblemOnlyReviewContractError(
                f"native requested output {index} has an invalid answer contract"
            )
        output_contracts.append({
            "id": output_id,
            "kind": kind,
            "unit": unit,
            "reporting_policy": output.get("reporting_policy"),
        })
        output_template.append({
            "id": output_id,
            "kind": kind,
            "raw_value": "<replace with exact scalar derivation>",
            "display_value": "<replace with final displayed string>",
            "unit": unit,
        })
    answer_path = answer_submission_relative_path(record_id).as_posix()
    template = {
        "schema_version": 1,
        "id": record_id,
        "official_answer_seen": False,
        "outputs": output_template,
    }
    return (
        "TARGET ANSWER SUBMISSION CONTRACT (generated output, not source evidence):\n"
        f"- Exact path: {answer_path}\n"
        "- Exact requested output contracts: "
        + json.dumps(output_contracts, ensure_ascii=False, sort_keys=True)
        + "\n- Required JSON shape: "
        + json.dumps(template, ensure_ascii=False, sort_keys=True)
        + "\nOverwrite this exact file on every formalization/redraft. Preserve output "
        "order/id/kind/unit exactly; raw_value is a finite JSON number or "
        "non-empty exact symbolic string and display_value is always a non-empty "
        "JSON string produced by the bound reporting_policy. For numeric output, "
        "prefer ASCII decimal/e notation such as 7.03e12; a bounded `× 10^n` "
        "display is accepted, but never use Unicode superscript digits or add "
        "fields outside the exact schema. Do not create any other "
        "answer/candidate file.\n"
        "Before deriving any figure-dependent chemical formula, identity, or "
        "count, perform a source-first visual recount: handle every relevant "
        "panel and legend separately; enumerate all distinct building-block "
        "types, node counts, connectivity/degrees, and cross-boundary bonds; "
        "then balance every condensation/addition loss or gain before comparing "
        "with an existing candidate. If the topology remains ambiguous, keep "
        "the result blocked instead of reusing the prior interpretation.\n"
        "For every mass fraction, weight fraction, wt%, or mass loading, state "
        "the numerator and denominator and distinguish total-mixture mass from "
        "component-only or support/base mass. Unless the problem explicitly "
        "defines another basis, use component mass divided by total mixture "
        "mass and solve that mass-balance equation before substitution; do not "
        "inherit a base-mass ratio from an existing candidate."
    )


def render_native_chemistry_constant_policy(
    contract: Mapping[str, Any],
) -> str:
    """Render the closed-world chemistry registry policy bound by the controller."""

    dataset = contract.get("chemistry_constant_dataset")
    expected = {"version": DATASET_VERSION, "sha256": DATASET_SHA256}
    if not is_native_problem_only_contract(contract) or dataset != expected:
        raise ProblemOnlyReviewContractError(
            "native Review contract has no approved chemistry constant dataset"
        )
    empirical_ids = ", ".join(
        f"`{rule_id}`" for rule_id in BASELINE_EMPIRICAL_RULE_IDS
    )
    reference_only_empirical_ids = ", ".join(
        f"`{rule_id}`" for rule_id in REFERENCE_ONLY_EMPIRICAL_RULE_IDS
    )
    dormant_empirical_ids = ", ".join(
        f"`{rule_id}`" for rule_id in DORMANT_RUNTIME_BRIDGE_IDS
    )
    contest_policy_ids = ", ".join(
        f"`{policy_id}`" for policy_id in CONTEST_INTERPRETATION_IDS
    )
    reaction_template_ids = ", ".join(
        f"`{template_id}`" for template_id in REACTION_TEMPLATE_IDS
    )

    baseline_count = len(BASELINE_EMPIRICAL_RULE_IDS)

    return f"""APPROVED OFFLINE CHEMISTRY REGISTRY POLICY:
- The version-pinned structured CLI remains the preferred reproducible lookup.
  Its allowed dataset is version={DATASET_VERSION},
  sha256={DATASET_SHA256}.
- Minimal public literature lookup is also allowed when a chemistry bridge is
  missing. Search only for the generic species, reaction, or property; record
  the source title, DOI or stable URL, exact locator, exact scoped claim, and
  applicability conditions. Never search for an olympiad problem, its wording,
  an official answer, solution, rubric, marking scheme, or a prior run.
- Query grammar (angle-bracket names are placeholders, not literal tokens):
  `"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>`,
  `"$ARCHON_CLI_BIN" chemistry-constant isotope_mass <ISOTOPE>`,
  `"$ARCHON_CLI_BIN" chemistry-constant molar_mass <FORMULA>`,
  `"$ARCHON_CLI_BIN" chemistry-constant reaction_template <TEMPLATE_ID>`,
  `"$ARCHON_CLI_BIN" chemistry-constant contest_interpretation <POLICY_ID>`, or
  `"$ARCHON_CLI_BIN" chemistry-constant empirical_rule <RULE_ID>`.
- For `atomic_weight`, `isotope_mass`, and `molar_mass` only, these grammar
  lines and examples are illustrative, not an allowlist. Any structurally valid
  element, canonical isotope, or chemical formula supported by this dataset is
  permitted. Do not infer that an unshown element or formula is unavailable.
- `reaction_template` has the exact TEMPLATE_ID allowlist:
  {reaction_template_ids}.
- `contest_interpretation` has the exact POLICY_ID allowlist:
  {contest_policy_ids}.
- `empirical_rule` has an exact {baseline_count}-ID allowlist: the exact allowed RULE_ID
  inventory available without runtime activation is:
  {empirical_ids}.
- Reference-only empirical-rule IDs are:
  {reference_only_empirical_ids}. A reference-only lookup is never baseline
  evidence and cannot receive a controller activation receipt. It may be
  inspected as source-scoped literature context for candidate enumeration.
  Its returned claim may be cited only when independent problem evidence
  supplies every exact returned applicability condition; the lookup itself
  proves none of those conditions. Never borrow a missing protocol condition
  from literature. When a condition is absent, the record may nominate a
  candidate for a closed audit but is non-premise context and cannot ground a
  source-to-Lean bridge about the current reaction.
- Dormant Reviewer-requestable bridge IDs are:
  {dormant_empirical_ids}. They may be returned by the sealed CLI but are not
  active evidence in an initial formalization or ordinary lookup. A dormant
  rule may be used only when the current immediate-redraft prompt contains its
  complete controller-built activation receipt bound to this exact target and
  candidate. A bare id, lookup receipt, candidate citation, or Reviewer text
  never activates it. All applicability conditions are conjunctive and
  source-bound: if even one lacks exact evidence, the rule is inapplicable and
  the target must remain blocked. Receipt completeness never establishes
  applicability.
- These are the full supported registries at lookup level: the template,
  policy, baseline, reference-only, and dormant lists form the complete
  inventory. Never guess, enumerate, or probe another registry id. An unlisted
  id fails closed.
- Pass exactly one element, isotope, formula, registered template id,
  registered contest-policy id, or exact allowlisted empirical-rule id. Never
  pass a problem id, question/source text, URL, or search phrase to the
  structured CLI.
- A public literature source may ground only the exact claim and scope it
  states. It may nominate a candidate but cannot invent an omitted problem
  condition, prove applicability to a different substrate, or provide candidate
  uniqueness by itself. The Reviewer must independently check its use.
- A Reviewer must verify each used lookup through the same
  `"$ARCHON_CLI_BIN"` grammar. Check the returned dataset version/hash against
  the controller-bound values above, then check record_sha256 against the
  candidate-cited receipt after rerunning its exact operation and argument.
  The exact TEMPLATE_ID, POLICY_ID, baseline RULE_ID, reference-only RULE_ID,
  and dormant RULE_ID lists above are the full lookup inventory; no other
  identifier may be probed. A dormant lookup is not usable evidence without
  the exact target- and candidate-bound controller activation receipt in the
  current hand-off. A reference-only lookup never becomes active merely
  because it is cited by a candidate or Reviewer.
- A contest_interpretation receipt is a contest-semantics policy, not a paper,
  empirical chemistry fact, or universal inverse-classification theorem.
  Accept it only after binding every required activation cue to an exact
  problem-text locator, confirming there is no problem-stated override, and
  checking the exact dataset_sha256 and record_sha256. Missing, ambiguous, or
  different-substrate cues fail closed. Use only the returned domain, template,
  stoichiometry, and retention scope. The policy does not identify the specific
  reagent; derive that identity from source measurements and pinned constants.
- A baseline empirical_rule receipt, or a dormant rule carried by a complete
  current controller activation receipt, grounds only its returned claim under
  the returned
  `authority_kind`, inside every returned applicability condition, and outside
  every returned exclusion. For `peer_reviewed_literature`, treat it only as a
  source-scoped literature claim, never beyond the cited substrate, reagent, or
  conditions. For `contest_semantics_policy`, treat it as a bounded policy—not
  a paper or universal empirical law—and require the complete source-supplied
  finite candidate set, full structural-feature audit, and explicit interference
  exclusions required by the returned record. `automatic_problem_instantiation`
  must be false. Never turn a literature claim into an inverse classification or
  the bounded policy into an open-world rule. Preserve `dataset_sha256`,
  `record_sha256`, `base_dataset_sha256`, `pinned_rule_record_sha256`,
  `empirical_registry_manifest_sha256`, `source.url`, `source.doi`,
  `source.locator`, `source.content_sha256`, and the approved review metadata.
  A Reviewer must rerun the exact operation and allowed id and compare all those
  values. A missing or mismatched hash, source locator, approval, applicability
  condition, or scope—or a different substrate or reagent—fails closed.

- A reference-only empirical_rule receipt is not covered by the baseline or
  dormant grounding permission above. Its exact returned claim may be cited
  only after independent problem evidence establishes every returned
  applicability condition. Otherwise it may provide literature context for
  enumerating a candidate, but it cannot fill an omitted condition or ground a
  source-to-Lean bridge about the current reaction.

- STAGED-TRANSFORMATION CLASSIFICATION: before auditing a depicted or stated
  transformation, classify how the requested output uses it as either
  `quantitative_material_stage` or `qualitative_named_transform_only`.
- Use `quantitative_material_stage` whenever the conclusion depends on yield,
  completeness, sole-product or absence claims, stage coefficients or phase
  amounts, cross-stage atom/mass balance, loss/residue amount, or an omitted
  stream being empty. For this class, establish a finite, source-derived
  species domain and enumerate every permitted solid input/output, volatile
  output, and external input by identity/formula and phase. Every atom or mass
  flow must be species-typed; anonymous `other`, `residual`, `ejected`,
  `untracked`, or catch-all streams are forbidden. Give every admitted element
  an exact problem locator, independently rederived prior carrier, or valid
  pinned/activated authority.
- Use `qualitative_named_transform_only` only when an explicit source arrow or
  named-final cue is a non-exclusive compatibility constraint for an
  identify/draw/give-structure output. Bind the named reactant, reagent,
  product role, direction, exact source locator, and every applicable trusted
  rule. Keep omitted protocol details, coefficients, phases, byproducts, and
  streams unknown. This class may check the candidate's own formula, charge,
  valence, structure, primitive stoichiometry, pinned-weight interval, and
  compatibility, but it may not claim yield, completeness, sole-product
  status, absence of material, or a quantitative stage balance. It does not
  require inventing or exhaustively enumerating omitted streams and byproducts.
- For source verbs identify, draw, or give a structure without `unique`, `all`,
  `every`, or equivalent exhaustive wording, a concrete evidence-supported
  witness is the requested output; do not require a proof that the open-world
  chemical universe is finite or globally exhaustive. Audit the provenance of
  every finite candidate domain actually used, apply all decisive constraints
  uniformly, and reject answer smuggling. A named output carrier is not
  smuggling merely because it names the candidate; reject candidates injected
  into a premise, singleton/answer-shaped domain, opaque predicate, or reflexive
  theorem. Do not fail solely because no global
  candidate universe was asserted.
- Do not encode source qualitative or empirical facts as unconstrained
  `Bool`/`Prop` fields (for example identity, industrial use, symmetry,
  stability, or reaction completion) that a witness can set arbitrarily. Each
  decisive predicate needs a source locator/receipt and a nontrivial carrier,
  or must be eliminated by an actually used, provenance-bound candidate audit.
- For every `quantitative_material_stage`, expose named Lean carriers for the
  complete atom, charge, mass, and measured-interval ledgers, including every
  admitted species and external input. Scalar mass equality alone is not
  chemical feasibility.
  Apply a terminal-residue or terminal-candidate rule only after the species
  domain is closed and every stage ledger passes. A claimed countermodel or
  underdetermination result requires at least two fully species-typed,
  source-grounded, balanced models; numerical slack and freely chosen flags
  are not countermodels.
- Every Review certificate must include
  `chemistry_checks.staged_species_domain`, with `passed` or `failed` status
  and evidence naming the selected classification. Quantitative evidence names
  the domain, stages, and ledger carriers. A qualitative pass must include the
  exact token `qualitative_named_transform_only` and name the source-arrow and
  compatibility carriers. Use `not_applicable` only when the target has no
  staged material transformation; that evidence must include the exact token
  `not_staged_transformation`.

- Problem-stipulated values override the dataset. A pinned nominal value may be
  used for an olympiad-style central answer when the problem asks for one, but
  still check whether source uncertainty could change the required reported
  digits or classification. A generic reaction template is not evidence that
  this problem instantiates it; require separate classification from bound
  problem evidence, trusted general chemistry, or a qualifying exact
  contest_interpretation receipt."""


def render_native_certified_prior_result_prompt(
    contract: Mapping[str, Any],
) -> str:
    """Render only a self-valid controller-certified typed dependency context."""

    if not is_native_problem_only_contract(contract):
        return ""
    try:
        rendered = render_certified_prior_result_prompt(
            contract.get("certified_prior_result")
        )
    except CertifiedPriorResultContextError as exc:
        raise ProblemOnlyReviewContractError(str(exc)) from exc
    if not rendered:
        return ""
    return (
        "CONTROLLER-CERTIFIED PRIOR-RESULT DEPENDENCY (typed, closed scope):\n"
        + rendered
        + "\nOnly the exact typed exports in this self-hashed context may be "
        "used as prior-part conclusions. Recheck every receipt hash, producer "
        "hard-green status, validation-lineage binding, Lean declaration/type "
        "hash, payload hash, and consumer binding. The questions-only "
        "previous_parts objects remain dependency questions/policy only and "
        "never establish an answer. Missing, stale, unmatched, or unlisted "
        "facts fail closed; do not extrapolate beyond an export's exact type."
        " A verified typed export may serve as a controller-authenticated "
        "prior-part capability only when its exact declared type and payload "
        "supply the specific prior-result premise required by the consuming "
        "rule and every producer/consumer binding matches. The receipt alone "
        "does not prove any other applicability premise of that rule."
    )


def render_native_source_contract_prompt(contract: Mapping[str, Any]) -> str:
    if not is_native_problem_only_contract(contract):
        return render_source_contract_prompt(contract)
    evidence = contract.get("problem_evidence")
    if not isinstance(evidence, Mapping):
        raise ProblemOnlyReviewContractError(
            "native problem-only contract has no problem evidence"
        )
    submission = contract.get("answer_submission")
    submission_sha256 = contract.get("answer_submission_sha256")
    if (
        not isinstance(submission, str)
        or not submission
        or not _SHA256_RE.fullmatch(str(submission_sha256 or ""))
    ):
        raise ProblemOnlyReviewContractError(
            "native problem-only contract has no answer submission binding"
        )
    semantic_block = render_native_formalizer_semantic_dag_prompt(contract)
    constant_policy = render_native_chemistry_constant_policy(contract)
    prior_result_block = render_native_certified_prior_result_prompt(contract)
    return (
        "NATIVE PROBLEM-INPUT-ONLY CONTRACT (immutable evidence):\n"
        "- Authority: problem-only\n"
        "- Evaluation mode: answer_blind\n"
        "- Required persisted provenance (controller-owned exact JSON; echo "
        "value-for-value and never reconstruct or abbreviate any digest): "
        + json.dumps(
            native_source_contract_provenance(contract),
            ensure_ascii=False,
            sort_keys=True,
        )
        + "\n- Problem evidence: "
        + json.dumps(evidence, ensure_ascii=False, sort_keys=True)
        + "\n- Bounded generated answer submission (untrusted; read completely): "
        + submission
        + " (sha256="
        + str(submission_sha256)
        + ")"
        + "\nThe controller will deterministically materialize and revalidate "
        "this source_contract object after the worker returns. All verdicts, "
        "audits, requested-output evidence, and composition accounting remain "
        "Reviewer-owned and are never auto-repaired. The source bundle/report "
        "locators and digests above are validation metadata only; do not open "
        "those files. Treat only the inline problem "
        "evidence and listed problem images as source facts. Treat the current "
        "Lean candidate and bound answer submission as untrusted generated "
        "outputs to audit, never as problem facts. Open the answer submission "
        "but no other unlisted project artifact. Independently rederive and "
        "audit every submission raw_value and display_value against its exact "
        "requested output id/kind/unit/reporting_policy and named Lean carrier. "
        "Do not copy raw/display answer values into source_contract provenance "
        "or controller process history. Every requested output, reporting rule, "
        "tolerance, and candidate-domain restriction must be derived from the "
        "bound problem evidence, auditable chemistry evidence allowed by the "
        "bound policy within its exact scope, or an exact typed export in the "
        "controller-certified prior-result context. Missing or ambiguous "
        "evidence fails "
        "closed.\n"
        + prior_result_block
        + ("\n" if prior_result_block else "")
        + constant_policy
        + "\n"
        + semantic_block
    )


def _legacy_shadow_contract(contract: Mapping[str, Any]) -> dict[str, Any]:
    evidence = contract.get("problem_evidence")
    evidence = evidence if isinstance(evidence, Mapping) else {}
    return {
        "schema_version": 3,
        "required": True,
        "available": True,
        "valid": True,
        "domain": "chemistry",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "authority": "problem-only",
        "target": contract.get("target"),
        "lean_sha256": contract.get("candidate_sha256"),
        "candidate_sha256": contract.get("candidate_sha256"),
        "source_bundle_sha256": contract.get("source_bundle_sha256"),
        "source_record_sha256": contract.get("source_record_sha256"),
        "blueprint": "",
        "blueprint_sha256": "",
        "source_report": contract.get("source_report"),
        "source_sha256": contract.get("source_report_sha256"),
        "source_report_sha256": contract.get("source_report_sha256"),
        "entry_id": contract.get("source_record_id"),
        "blind_record_sha256": contract.get("source_record_sha256"),
        "blind_candidate_record": contract.get("candidate"),
        "blind_candidate_sha256": contract.get("candidate_sha256"),
        "lean_result_contracts_sha256": None,
        "requested_outputs": evidence.get("requested_outputs", []),
        "requested_outputs_sha256": contract.get("requested_outputs_sha256"),
        "reporting_policy_sha256": contract.get("reporting_policy_sha256"),
        "measurement_policy_sha256": contract.get("measurement_policy_sha256"),
        "candidate_domain_policy_sha256": contract.get(
            "candidate_domain_policy_sha256"
        ),
        "chemistry_constant_dataset": contract.get(
            "chemistry_constant_dataset"
        ),
        "answer_submission_sha256": contract.get("answer_submission_sha256"),
        "certified_prior_result_sha256": contract.get(
            "certified_prior_result_sha256"
        ),
        "certified_prior_result_context_receipt_sha256": contract.get(
            "certified_prior_result_context_receipt_sha256"
        ),
        "preflight_sha256": contract.get("preflight_sha256"),
        "question_field": "question",
        "question_sha256": contract.get("question_sha256"),
        "previous_blind_sha256": contract.get("previous_parts_sha256"),
        "previous_blind_hashes": [],
        "images": contract.get("images", []),
        "errors": [],
    }


def _validate_native_composition_accounting(
    item: Mapping[str, Any],
    expected: Mapping[str, Any],
    contract: Mapping[str, Any],
    *,
    index: int,
    passing: bool,
) -> str:
    """Validate the opt-in whole-product topology and component ledger."""

    requirements = expected.get("audit_requirements")
    required = (
        isinstance(requirements, list)
        and _IMAGE_COMPONENT_ACCOUNTING in requirements
    )
    if not required:
        if "composition_accounting" in item:
            return (
                f"requested output {index} has unbound composition_accounting"
            )
        return ""

    accounting = item.get("composition_accounting")
    if not isinstance(accounting, Mapping):
        return f"requested output {index} has no component accounting audit"
    if set(accounting) != _COMPOSITION_ACCOUNTING_FIELDS:
        return (
            f"requested output {index} component accounting fields are invalid"
        )

    bound_images = contract.get("images")
    if not isinstance(bound_images, list) or not bound_images:
        return "native source contract images are missing"
    bound_by_path: dict[str, str] = {}
    for image in bound_images:
        if not isinstance(image, Mapping):
            return "native source contract image is invalid"
        path = image.get("path")
        digest = image.get("sha256")
        if (
            not isinstance(path, str)
            or not path
            or not isinstance(digest, str)
            or not _SHA256_RE.fullmatch(digest)
            or path in bound_by_path
        ):
            return "native source contract image is invalid"
        bound_by_path[path] = digest

    source_images = accounting.get("source_images")
    if not isinstance(source_images, list) or not source_images:
        return f"requested output {index} component source_images are missing"
    seen_images: set[str] = set()
    for source_image in source_images:
        if (
            not isinstance(source_image, Mapping)
            or set(source_image) != _COMPOSITION_SOURCE_IMAGE_FIELDS
        ):
            return f"requested output {index} component source image is invalid"
        path = source_image.get("path")
        digest = source_image.get("sha256")
        if (
            not isinstance(path, str)
            or path in seen_images
            or bound_by_path.get(path) != digest
        ):
            return (
                f"requested output {index} component source image is not "
                "bound problem evidence"
            )
        seen_images.add(path)
    if seen_images != set(bound_by_path):
        return (
            f"requested output {index} component source_images do not cover "
            "every bound image"
        )

    product_nodes = accounting.get("product_nodes")
    if not isinstance(product_nodes, list) or not product_nodes:
        return f"requested output {index} product_nodes are missing"
    nodes_by_id: dict[str, str] = {}
    node_multiplicities: dict[str, int] = {}
    node_image_paths: set[str] = set()
    non_adduct_nodes: set[str] = set()
    for node in product_nodes:
        if (
            not isinstance(node, Mapping)
            or set(node) != _COMPOSITION_PRODUCT_NODE_FIELDS
        ):
            return f"requested output {index} has an invalid product node"
        node_id = node.get("node_id")
        node_kind = node.get("node_kind")
        descriptor = node.get("formula_or_descriptor")
        source_path = node.get("source_path")
        source_locator = node.get("source_locator")
        multiplicity = node.get("multiplicity")
        if (
            not isinstance(node_id, str)
            or not _COMPOSITION_ID_RE.fullmatch(node_id)
            or node_id == "none"
            or node_id in nodes_by_id
            or not isinstance(node_kind, str)
            or node_kind not in _COMPOSITION_PRODUCT_NODE_KINDS
            or not isinstance(descriptor, str)
            or not descriptor.strip()
            or not isinstance(source_path, str)
            or source_path not in bound_by_path
            or not isinstance(source_locator, str)
            or not source_locator.strip()
            or isinstance(multiplicity, bool)
            or not isinstance(multiplicity, int)
            or not 1 <= multiplicity <= 1_000_000
        ):
            return f"requested output {index} has an invalid product node"
        nodes_by_id[node_id] = node_kind
        node_multiplicities[node_id] = multiplicity
        node_image_paths.add(source_path)
        if node_kind != "adduct":
            non_adduct_nodes.add(node_id)
    if node_image_paths != set(bound_by_path):
        return (
            f"requested output {index} product_nodes do not cover every "
            "bound image"
        )
    if len(non_adduct_nodes) < 2:
        return (
            f"requested output {index} needs at least two non-adduct "
            "product nodes"
        )

    assembly_edges = accounting.get("assembly_edges")
    if not isinstance(assembly_edges, list) or not assembly_edges:
        return f"requested output {index} assembly_edges are missing"
    edges_by_id: set[str] = set()
    adjacency = {node_id: set() for node_id in nodes_by_id}
    has_non_adduct_edge = False
    for edge in assembly_edges:
        if (
            not isinstance(edge, Mapping)
            or set(edge) != _COMPOSITION_ASSEMBLY_EDGE_FIELDS
        ):
            return f"requested output {index} has an invalid assembly edge"
        edge_id = edge.get("edge_id")
        from_id = edge.get("from_node_id")
        to_id = edge.get("to_node_id")
        relation = edge.get("relation")
        multiplicity = edge.get("multiplicity")
        if (
            not isinstance(edge_id, str)
            or not _COMPOSITION_ID_RE.fullmatch(edge_id)
            or edge_id == "none"
            or edge_id in edges_by_id
            or not isinstance(from_id, str)
            or from_id not in nodes_by_id
            or not isinstance(to_id, str)
            or to_id not in nodes_by_id
            or from_id == to_id
            or not isinstance(relation, str)
            or relation not in _COMPOSITION_ASSEMBLY_RELATIONS
            or isinstance(multiplicity, bool)
            or not isinstance(multiplicity, int)
            or not 1 <= multiplicity <= 1_000_000
        ):
            return f"requested output {index} has an invalid assembly edge"
        edges_by_id.add(edge_id)
        adjacency[from_id].add(to_id)
        adjacency[to_id].add(from_id)
        if from_id in non_adduct_nodes and to_id in non_adduct_nodes:
            has_non_adduct_edge = True
    if not has_non_adduct_edge:
        return (
            f"requested output {index} needs an edge between non-adduct "
            "product nodes"
        )
    pending = [next(iter(nodes_by_id))]
    visited: set[str] = set()
    while pending:
        node_id = pending.pop()
        if node_id in visited:
            continue
        visited.add(node_id)
        pending.extend(adjacency[node_id] - visited)
    if visited != set(nodes_by_id):
        return f"requested output {index} product topology is disconnected"

    boundary_checks = accounting.get("boundary_checks")
    if not isinstance(boundary_checks, list) or not boundary_checks:
        return f"requested output {index} boundary_checks are missing"
    seen_boundaries: set[str] = set()
    seen_boundary_kinds: set[str] = set()
    has_ambiguous_boundary = False
    for boundary in boundary_checks:
        if (
            not isinstance(boundary, Mapping)
            or set(boundary) != _COMPOSITION_BOUNDARY_CHECK_FIELDS
        ):
            return f"requested output {index} has an invalid boundary check"
        boundary_id = boundary.get("boundary_id")
        boundary_kind = boundary.get("boundary_kind")
        source_path = boundary.get("source_path")
        source_locator = boundary.get("source_locator")
        disposition = boundary.get("disposition")
        edge_id = boundary.get("assembly_edge_id")
        boundary_status = boundary.get("status")
        if (
            not isinstance(boundary_id, str)
            or not _COMPOSITION_ID_RE.fullmatch(boundary_id)
            or boundary_id == "none"
            or boundary_id in seen_boundaries
            or not isinstance(boundary_kind, str)
            or boundary_kind not in _COMPOSITION_BOUNDARY_KINDS
            or not isinstance(source_path, str)
            or source_path not in bound_by_path
            or not isinstance(source_locator, str)
            or not source_locator.strip()
            or not isinstance(disposition, str)
            or disposition not in _COMPOSITION_BOUNDARY_DISPOSITIONS
            or not isinstance(boundary_status, str)
            or boundary_status not in {"resolved", "ambiguous"}
        ):
            return f"requested output {index} has an invalid boundary check"
        if disposition == "represented_by_edge":
            if not isinstance(edge_id, str) or edge_id not in edges_by_id:
                return (
                    f"requested output {index} boundary check has an invalid "
                    "assembly edge reference"
                )
        elif edge_id != "none":
            return (
                f"requested output {index} boundary check has an invalid "
                "assembly edge disposition"
            )
        if (boundary_status == "ambiguous") != (disposition == "ambiguous"):
            return (
                f"requested output {index} boundary status and disposition "
                "are inconsistent"
            )
        seen_boundaries.add(boundary_id)
        seen_boundary_kinds.add(boundary_kind)
        has_ambiguous_boundary = (
            has_ambiguous_boundary or boundary_status == "ambiguous"
        )
    if (
        "bracket" not in seen_boundary_kinds
        or not seen_boundary_kinds.intersection(
            {"connector", "cross_boundary_bond"}
        )
    ):
        return (
            f"requested output {index} boundary_checks do not trace both "
            "brackets and outgoing connections"
        )

    status = str(accounting.get("status") or "").strip().lower()
    if status not in {"matched", "failed"}:
        return f"requested output {index} component accounting status is invalid"
    if has_ambiguous_boundary and (passing or status == "matched"):
        return (
            f"passing or matched requested output {index} leaves an "
            "ambiguous product boundary"
        )
    if not str(accounting.get("evidence") or "").strip():
        return f"requested output {index} component accounting has no evidence"
    outer_carrier = item.get("lean_carrier")
    if (
        not isinstance(accounting.get("lean_carrier"), str)
        or not str(accounting.get("lean_carrier")).strip()
        or accounting.get("lean_carrier") != outer_carrier
    ):
        return (
            f"requested output {index} component accounting Lean carrier is "
            "missing or mismatched"
        )

    components = accounting.get("components")
    if not isinstance(components, list):
        return f"requested output {index} components must be a list"
    seen_labels: set[str] = set()
    covered_component_nodes: set[str] = set()
    for component in components:
        if (
            not isinstance(component, Mapping)
            or set(component) != _COMPOSITION_COMPONENT_FIELDS
        ):
            return f"requested output {index} has an invalid component entry"
        product_node_id = component.get("product_node_id")
        label = component.get("label")
        descriptor = component.get("formula_or_descriptor")
        multiplicity = component.get("multiplicity")
        role = component.get("role")
        if (
            not isinstance(product_node_id, str)
            or product_node_id not in nodes_by_id
            or product_node_id in covered_component_nodes
            or not isinstance(label, str)
            or not label.strip()
            or label in seen_labels
            or not isinstance(descriptor, str)
            or not descriptor.strip()
            or isinstance(multiplicity, bool)
            or not isinstance(multiplicity, int)
            or not 1 <= multiplicity <= 1_000_000
            or multiplicity != node_multiplicities[product_node_id]
            or not isinstance(role, str)
            or role not in _COMPOSITION_COMPONENT_ROLES
        ):
            return f"requested output {index} has an invalid component entry"
        covered_component_nodes.add(product_node_id)
        seen_labels.add(label)

    assembly = accounting.get("assembly_expression")
    combined = accounting.get("combined_formula_or_quantity")
    if not isinstance(assembly, str) or not isinstance(combined, str):
        return f"requested output {index} component accounting is incomplete"
    if status == "matched" and (
        not components or not assembly.strip() or not combined.strip()
    ):
        return f"requested output {index} matched component accounting is incomplete"
    if status == "matched" and covered_component_nodes != set(nodes_by_id):
        return (
            f"requested output {index} matched components do not exactly "
            "cover product_nodes"
        )
    missing_assembly_node_ids = [
        node_id
        for node_id in nodes_by_id
        if re.search(
            rf"(?<![a-z0-9_-]){re.escape(node_id)}(?![a-z0-9_-])",
            assembly,
        )
        is None
    ]
    if status == "matched" and missing_assembly_node_ids:
        return (
            f"requested output {index} assembly_expression omits a product "
            "node id; missing="
            + json.dumps(missing_assembly_node_ids, ensure_ascii=False)
        )
    if passing and status != "matched":
        return (
            f"passing verdict leaves requested output {index} component "
            "accounting unmatched"
        )
    return ""


def _validate_native_requested_outputs(
    review: Mapping[str, Any],
    contract: Mapping[str, Any],
    *,
    passing: bool,
) -> str:
    evidence = contract.get("problem_evidence")
    expected_outputs = (
        evidence.get("requested_outputs")
        if isinstance(evidence, Mapping)
        else None
    )
    actual_outputs = review.get("requested_outputs")
    if not isinstance(expected_outputs, list) or not expected_outputs:
        return "native source contract requested_outputs are missing"
    if not isinstance(actual_outputs, list):
        return "requested_outputs must exactly cover the bound problem outputs"
    expected_by_id = {
        item.get("id"): item
        for item in expected_outputs
        if isinstance(item, Mapping) and isinstance(item.get("id"), str)
    }
    expected_ids = [
        item.get("id")
        for item in expected_outputs
        if isinstance(item, Mapping)
    ]
    if (
        len(expected_by_id) != len(expected_outputs)
        or len(actual_outputs) != len(expected_outputs)
    ):
        return "requested_outputs do not exactly cover the bound problem outputs"
    actual_ids: list[str] = []
    for index, item in enumerate(actual_outputs, start=1):
        if not isinstance(item, Mapping):
            return f"requested output {index} is not an object"
        output_id = item.get("output_id")
        if not isinstance(output_id, str):
            return (
                f"requested output {index} output_id is not bound problem evidence"
            )
        expected = expected_by_id.get(output_id)
        if expected is None:
            return f"requested output {index} output_id is not bound problem evidence"
        actual_ids.append(output_id)
        requirement = item.get("source_requirement")
        if requirement != expected.get("source_requirement"):
            return (
                f"requested output {index} source_requirement is not bound "
                "problem evidence"
            )
        status = str(item.get("status") or "").strip().lower()
        submission_status = str(
            item.get("submission_status") or ""
        ).strip().lower()
        reporting_status = str(
            item.get("reporting_policy_status") or ""
        ).strip().lower()
        if status not in {"covered", "blocked"}:
            return f"requested output {index} has an invalid status"
        if submission_status not in {"matched", "failed"}:
            return f"requested output {index} has no answer submission audit"
        if reporting_status not in {"matched", "failed"}:
            return f"requested output {index} has no reporting policy audit"
        if not str(item.get("lean_carrier") or "").strip():
            return f"requested output {index} has no Lean carrier"
        if not str(item.get("evidence") or "").strip():
            return f"requested output {index} has no audit evidence"
        composition_error = _validate_native_composition_accounting(
            item,
            expected,
            contract,
            index=index,
            passing=passing,
        )
        if composition_error:
            return composition_error
        if passing and status != "covered":
            return f"passing verdict leaves requested output {index} uncovered"
        if passing and submission_status != "matched":
            return f"passing verdict leaves requested output {index} submission unmatched"
        if passing and reporting_status != "matched":
            return f"passing verdict leaves requested output {index} reporting unmatched"
    if actual_ids != expected_ids:
        return "requested_outputs do not preserve bound problem output order"
    return ""


def validate_native_passing_preflight(
    contract: Mapping[str, Any] | None,
    *,
    require_zero_sorries: bool,
) -> str:
    """Validate worker-local deterministic evidence for a passing verdict."""
    if not is_native_problem_only_contract(contract):
        return ""
    raw = contract.get("preflight")
    # Durable gates rebuild source/candidate provenance without historical
    # preflight; their containing pipeline report validates those rows.
    if raw is None:
        return ""
    candidate = str(contract.get("candidate") or "")
    try:
        row = _validate_preflight(
            raw,
            candidate,
            expected_lean_sha256=contract.get("candidate_sha256"),
            expected_bundle_sha256=contract.get("source_bundle_sha256"),
        )
    except ProblemOnlyReviewContractError as exc:
        return str(exc)
    if (
        row.get("status") != "passed"
        or row.get("compiles") is not True
        or row.get("returncode") != 0
    ):
        return "passing Review requires a successful deterministic Lean preflight"
    if require_zero_sorries and row.get("sorry_count") != 0:
        return "solved proof Review requires deterministic sorry_count=0"
    return ""


def validate_native_review_source_certificate(
    review: Mapping[str, Any],
    expected_contract: Mapping[str, Any] | None,
    *,
    passing: bool,
) -> str:
    if not is_native_problem_only_contract(expected_contract):
        return validate_review_source_certificate(
            review, expected_contract, passing=passing,
        )
    expected = native_source_contract_provenance(expected_contract)
    actual = review.get("source_contract")
    if not isinstance(actual, Mapping):
        return "source_contract provenance is missing"
    if dict(actual) != expected:
        actual_fields = set(actual)
        expected_fields = set(expected)
        if actual_fields != expected_fields:
            return (
                "source_contract does not match native problem-only evidence: "
                f"fields missing={sorted(expected_fields - actual_fields)!r}, "
                f"extra={sorted(actual_fields - expected_fields)!r}"
            )
        for key, expected_value in expected.items():
            actual_value = actual.get(key)
            if actual_value == expected_value:
                continue
            if (
                key.endswith("sha256")
                and isinstance(expected_value, str)
                and isinstance(actual_value, str)
            ):
                return (
                    "source_contract does not match native problem-only "
                    f"evidence: {key} expected={expected_value!r} "
                    f"actual={actual_value!r} "
                    f"(length {len(actual_value)}, expected "
                    f"{len(expected_value)})"
                )
            return (
                "source_contract does not match native problem-only evidence: "
                f"{key} differs"
            )
        return "source_contract does not match native problem-only evidence"
    if passing:
        preflight_error = validate_native_passing_preflight(
            expected_contract,
            require_zero_sorries=False,
        )
        if preflight_error:
            return preflight_error
    requested_error = _validate_native_requested_outputs(
        review, expected_contract, passing=passing,
    )
    if requested_error:
        return requested_error
    shadow = _legacy_shadow_contract(expected_contract)
    shadow_review = dict(review)
    shadow_review["source_contract"] = source_contract_provenance(shadow)
    return validate_review_source_certificate(
        shadow_review, shadow, passing=passing,
    )


def validate_review_source_contract_current(
    *, project_path: Path, contract: Mapping[str, Any] | None,
) -> str:
    """Recheck immutable inputs immediately before and after a model worker."""
    if not is_native_problem_only_contract(contract):
        return ""
    preflight = contract.get("preflight")
    if not isinstance(preflight, Mapping):
        return "native worker contract has no deterministic Lean preflight"
    candidate = str(contract.get("candidate") or "")
    try:
        target = _safe_project_file(
            project_path, candidate, label="Lean candidate",
        )
        if _sha256_bytes(target.read_bytes()) != contract.get("candidate_sha256"):
            return "native problem-only Review inputs changed after contract creation"
        fresh = _build_native_contract(
            project_path=project_path,
            target=target,
            preflight=preflight,
        )
    except ProblemOnlyReviewContractError as exc:
        return str(exc)
    if fresh != dict(contract):
        return "native problem-only Review inputs changed after contract creation"
    return ""


def stored_review_provenance_matches_current(
    *,
    project_path: Path,
    target: Path,
    provenance: Any,
    bind_candidate: bool,
) -> tuple[bool, str]:
    # Preserve source-only formal passes; bind solved proofs to the candidate.
    try:
        native = native_problem_only_enabled(project_path)
    except ProblemOnlyReviewContractError as exc:
        return False, str(exc)
    if not native:
        return stored_provenance_matches_current(
            project_path=project_path,
            target=target,
            provenance=provenance,
        )
    try:
        fresh_contract = _build_native_contract(
            project_path=project_path,
            target=target,
            preflight=None,
        )
        expected = native_source_contract_provenance(fresh_contract)
    except ProblemOnlyReviewContractError as exc:
        return False, str(exc)
    if not isinstance(provenance, Mapping):
        return False, "stored Review certificate has no source_contract provenance"
    actual = dict(provenance)
    if set(actual) != set(expected):
        return False, "stored native Review provenance fields are stale or ambiguous"

    candidate_bound = {
        "candidate_sha256",
        "preflight_sha256",
    }
    for key, value in expected.items():
        if key in candidate_bound:
            continue
        if actual.get(key) != value:
            return False, f"stored native Review certificate is stale: {key} changed"

    actual_candidate = str(actual.get("candidate_sha256") or "")
    if not _SHA256_RE.fullmatch(actual_candidate):
        return False, "stored native Review candidate binding is invalid"
    if bind_candidate and actual_candidate != expected.get("candidate_sha256"):
        return False, "stored native Review certificate is stale: candidate changed"

    preflight_sha256 = str(actual.get("preflight_sha256") or "")
    if bind_candidate and not _SHA256_RE.fullmatch(preflight_sha256):
        return False, "stored native Review preflight binding is invalid"
    return True, ""


def validate_native_pipelined_preflight(
    *,
    project_path: Path,
    preflight: Any,
    expected_rels: list[str],
    solved_rels: list[str],
    expected_iteration: int,
) -> str:
    """Validate the durable deterministic evidence for a native handoff."""
    try:
        if not native_problem_only_enabled(project_path):
            return ""
        _bundle_path, bundle_payload, _manifest, _rows = _load_bundle(
            project_path
        )
        bundle_sha256 = _sha256_bytes(bundle_payload)
    except ProblemOnlyReviewContractError as exc:
        return str(exc)
    if not isinstance(preflight, Mapping):
        return "native pipelined Review preflight is missing"
    if set(preflight) != {
        "iteration", "jobs", "duration_secs", "summary", "targets",
    }:
        return "native pipelined Review preflight fields are incomplete or ambiguous"
    if preflight.get("iteration") != expected_iteration:
        return "native pipelined Review preflight iteration mismatch"
    jobs = preflight.get("jobs")
    duration = preflight.get("duration_secs")
    if (
        isinstance(jobs, bool)
        or not isinstance(jobs, int)
        or jobs < 1
        or isinstance(duration, bool)
        or not isinstance(duration, (int, float))
        or not math.isfinite(duration)
        or duration < 0
    ):
        return "native pipelined Review preflight metadata is invalid"
    raw_rows = preflight.get("targets")
    if not isinstance(raw_rows, list):
        return "native pipelined Review preflight targets are missing"
    rows: dict[str, dict[str, Any]] = {}
    for raw in raw_rows:
        if not isinstance(raw, Mapping):
            return "native pipelined Review preflight row is not an object"
        rel = str(raw.get("file") or "")
        if not rel or rel in rows:
            return "native pipelined Review preflight has duplicate/missing target"
        try:
            target = _safe_project_file(
                project_path, rel, label="Lean candidate",
            )
            rows[rel] = _validate_preflight(
                raw,
                rel,
                expected_lean_sha256=_sha256_bytes(target.read_bytes()),
                expected_bundle_sha256=bundle_sha256,
            )
        except ProblemOnlyReviewContractError as exc:
            return str(exc)
    expected = sorted(set(expected_rels))
    if sorted(rows) != expected:
        return (
            "native pipelined Review preflight target mismatch: "
            f"expected={expected!r}, actual={sorted(rows)!r}"
        )
    summary = preflight.get("summary")
    passed = sum(row["status"] == "passed" for row in rows.values())
    expected_summary = {
        "total": len(rows),
        "passed": passed,
        "failed": len(rows) - passed,
    }
    if not isinstance(summary, Mapping) or dict(summary) != expected_summary:
        return "native pipelined Review preflight summary is inconsistent"
    for rel in solved_rels:
        row = rows.get(rel)
        if row is None or (
            row.get("status") != "passed"
            or row.get("compiles") is not True
            or row.get("returncode") != 0
            or row.get("sorry_count") != 0
        ):
            return (
                f"solved proof Review target {rel} lacks successful, "
                "sorry-free deterministic preflight"
            )
    return ""
