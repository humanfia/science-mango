"""Hash-bound official-source contract shared by target Review workers.

The blueprint is generated material.  It is useful context, but it must never
be allowed to replace the source report, rubric answer, or source images that
the preparation command recorded for a target.  This module resolves that
record once, fingerprints every authoritative input, and validates the exact
fingerprints echoed by a Review certificate.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import unicodedata
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

from archon.commands.tooling.domain_profile import (
    DomainProfile,
    load_domain_profile,
)


SOURCE_CONTRACT_SCHEMA_VERSION = 1
BLIND_SOURCE_CONTRACT_SCHEMA_VERSION = 3
SOURCE_AUTHORITY = (
    "official source/rubric/images > blueprint > generated reports"
)
BLIND_SOURCE_AUTHORITY = "problem-only"
SOURCE_INCONSISTENCY_KIND = "official_internal_contradiction"
_SOURCE_REPORT_RE = re.compile(
    r"^\s*%\s*archon:source-report\s+(.+?)\s*$", re.MULTILINE,
)
_CHEMISTRY_CHECKS = (
    "chemical_semantics",
    "formula_mass_consistency",
    "conservation_laws",
    "units_dimensions",
    "numerical_reporting",
    "structure_stereochemistry",
    "identification_uniqueness",
    "answer_smuggling",
)
_INDEPENDENT_SOURCE_CHECKS = (
    "requested_outputs",
    "official_answer",
    "image_grounding",
    "domain_invariants",
    "reporting_convention",
    "adversarial_counterexample",
)
_BLIND_SOURCE_CHECKS = (
    "answer_independence",
    "raw_derivation",
    "reporting_rule_source",
    "tolerance_provenance",
    "candidate_domain_provenance",
    "lean_result_binding",
)
_CONTRACT_AUDIT_CHECKS = (
    "statement_scope",
    "hypothesis_derivability",
    "conclusion_alignment",
    "bridge_completeness",
)
_PASS = {"pass", "passed", "covered", "aligned", "resolved"}
_FAIL = {
    "fail", "failed", "blocked", "conflict", "missing", "needs_redraft",
    "unresolved",
}
_NOT_APPLICABLE = {"not_applicable", "not applicable", "n/a", "na"}
_SOURCE_INCONSISTENCY_FIELDS = (
    "official_claim",
    "derived_claim",
    "derivation_carrier",
    "evidence",
)
_BLIND_FORBIDDEN_REPORT_FIELDS = {
    "answer",
    "solution",
    "marking",
    "rubric",
    "explanation",
    "reasoning",
    "grader",
}
_BLIND_REVIEW_FORBIDDEN_FIELDS = {
    "official_answer_alignment",
    "source_inconsistency",
}
_SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")
_LEAN_DECLARATION_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_NUMERIC_TEXT_RE = re.compile(
    r"^[+-]?(?:(?:\d+(?:\.\d*)?)|(?:\.\d+))(?:[eE][+-]?\d+)?$"
)
_RATIONAL_TEXT_RE = re.compile(r"^(?P<num>-?(?:0|[1-9][0-9]*))/(?P<den>[1-9][0-9]*)$")
_MAX_NUMERIC_TEXT_LENGTH = 256
_MAX_NUMERIC_COEFFICIENT_DIGITS = 192
_MAX_NUMERIC_EXPONENT_ABS = 1000
_MAX_REPORTED_PRECISION_DIGITS = 100
_RESULT_CONTRACT_FIELDS = {
    "role",
    "declaration",
    "expected_type",
    "expected_type_sha256",
    "result_payload_sha256",
}
_RESULT_CONTRACT_ROLES = {"raw_result", "reported_result"}
_BLIND_CANDIDATE_FIELDS = {
    "schema_version", "protocol", "phase", "evaluation_mode",
    "official_answer_seen", "id", "blind_record_sha256", "result_kind",
    "raw_result", "reported_result", "reporting_rule_source",
    "tolerance_provenance", "candidate_domain_provenance",
    "lean_declarations", "lean_result_contracts",
}
_BLIND_RAW_RESULT_FIELDS = {
    "expression", "lean_expression", "derivation_spec", "certified_interval",
    "value", "unit",
}
_BLIND_REPORTED_RESULT_FIELDS = {
    "value", "text", "lean_expression", "unit", "precision", "rounding_rule",
}


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _file_sha256(path: Path) -> str:
    try:
        return _sha256_bytes(path.read_bytes())
    except OSError:
        return ""


def _value_sha256(value: Any) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
    ).encode("utf-8")
    return _sha256_bytes(payload)


def normalize_lean_result_type(value: str) -> str:
    """Canonicalize a solver-declared Lean type before hashing it.

    This normalization is intentionally modest: Unicode is canonicalized and
    insignificant whitespace is collapsed, while every token and delimiter is
    retained.  Lean still checks the exact type in a generated probe later.
    """
    return " ".join(unicodedata.normalize("NFKC", value).split())


def lean_result_type_sha256(value: str) -> str:
    return _sha256_bytes(normalize_lean_result_type(value).encode("utf-8"))


def blind_result_payload_sha256(
    candidate: Mapping[str, Any], role: str,
) -> str:
    """Bind a result contract to the exact candidate fields it certifies."""
    common = {
        "schema_version": candidate.get("schema_version"),
        "protocol": candidate.get("protocol"),
        "id": candidate.get("id"),
        "blind_record_sha256": candidate.get("blind_record_sha256"),
        "result_kind": candidate.get("result_kind"),
        "role": role,
    }
    if role == "raw_result":
        common["raw_result"] = candidate.get("raw_result")
    elif role == "reported_result":
        common.update({
            "raw_result": candidate.get("raw_result"),
            "reported_result": candidate.get("reported_result"),
            "reporting_rule_source": candidate.get("reporting_rule_source"),
            "tolerance_provenance": candidate.get("tolerance_provenance"),
            "candidate_domain_provenance": candidate.get(
                "candidate_domain_provenance"
            ),
        })
    else:
        raise ValueError(f"unsupported result-contract role: {role}")
    return _value_sha256(common)


def _decimal_value(value: object) -> Decimal | None:
    if isinstance(value, bool) or value is None:
        return None
    text = str(value).strip()
    if len(text) > _MAX_NUMERIC_TEXT_LENGTH:
        return None
    if not _NUMERIC_TEXT_RE.fullmatch(text):
        return None
    mantissa, _, raw_exponent = text.lower().partition("e")
    if sum(character.isdigit() for character in mantissa) > _MAX_NUMERIC_COEFFICIENT_DIGITS:
        return None
    if raw_exponent:
        try:
            exponent = int(raw_exponent)
        except ValueError:
            return None
        if abs(exponent) > _MAX_NUMERIC_EXPONENT_ABS:
            return None
    try:
        parsed = Decimal(text)
    except InvalidOperation:
        return None
    return parsed if parsed.is_finite() else None


def _decimal_lean_expression(value: Decimal) -> str:
    sign, digits, exponent = value.as_tuple()
    coefficient = int("".join(str(digit) for digit in digits) or "0")
    if sign:
        coefficient = -coefficient
    if exponent >= 0:
        return f"({coefficient * (10 ** exponent)} : ℝ)"
    denominator = 10 ** (-exponent)
    return f"(({coefficient} : ℝ) / {denominator})"


def _exact_rational_value(value: object) -> Fraction | None:
    """Parse an exact JSON string, rejecting noncanonical rational spellings."""
    if (
        not isinstance(value, str)
        or not value
        or value != value.strip()
        or len(value) > _MAX_NUMERIC_TEXT_LENGTH
    ):
        return None
    rational = _RATIONAL_TEXT_RE.fullmatch(value)
    if rational:
        if max(
            len(rational.group("num").lstrip("-")),
            len(rational.group("den")),
        ) > _MAX_NUMERIC_COEFFICIENT_DIGITS:
            return None
        numerator = int(rational.group("num"))
        denominator = int(rational.group("den"))
        parsed = Fraction(numerator, denominator)
        # Slash form is canonical iff already reduced, with a positive
        # denominator and no redundant sign/leading zeros (enforced by regex).
        if parsed.numerator != numerator or parsed.denominator != denominator:
            return None
        return parsed
    decimal = _decimal_value(value)
    return Fraction(decimal) if decimal is not None else None


def _fraction_lean_expression(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"(({value.numerator} : ℝ) / {value.denominator})"


def _reported_quantum(precision: object, reported: Decimal) -> Decimal | None:
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
            quantum = _decimal_value(text)
            return quantum.copy_abs() if quantum is not None and quantum != 0 else None
    if (
        digits is None
        or digits < 0
        or digits > _MAX_REPORTED_PRECISION_DIGITS
    ):
        return None
    if kind in {"decimal", "decimal_place", "decimal_places", "dp"}:
        return Decimal(1).scaleb(-digits)
    if kind in {
        "significant", "significant_figure", "significant_figures", "sigfig", "sf",
    }:
        if digits < 1:
            return None
        if reported == 0:
            return Decimal(1).scaleb(-(digits - 1))
        return Decimal(1).scaleb(reported.copy_abs().adjusted() - digits + 1)
    return None


def expected_numeric_result_types(
    candidate: Mapping[str, Any],
) -> dict[str, str] | None:
    """Derive the only admissible numeric theorem types from candidate data."""
    raw = candidate.get("raw_result")
    reported = candidate.get("reported_result")
    if not isinstance(raw, Mapping) or not isinstance(reported, Mapping):
        return None
    raw_value = _exact_rational_value(raw.get("value"))
    reported_value = _decimal_value(reported.get("value"))
    raw_expression = str(raw.get("lean_expression") or "").strip()
    derivation_spec = str(raw.get("derivation_spec") or "").strip()
    interval = raw.get("certified_interval")
    if not isinstance(interval, Mapping) or set(interval) != {"lower", "upper"}:
        return None
    lower = (
        _exact_rational_value(interval.get("lower"))
        if isinstance(interval, Mapping)
        else None
    )
    upper = (
        _exact_rational_value(interval.get("upper"))
        if isinstance(interval, Mapping)
        else None
    )
    quantum = (
        _reported_quantum(reported.get("precision"), reported_value)
        if reported_value is not None
        else None
    )
    if (
        raw_value is None
        or reported_value is None
        or quantum is None
        or not raw_expression
        or not derivation_spec
        or lower is None
        or upper is None
        or lower > upper
        or raw_value < lower
        or raw_value > upper
    ):
        return None
    # A raw carrier must name or compute an independently derived expression;
    # merely restating the submitted numeral would be a reflexive certificate.
    if (
        not _LEAN_DECLARATION_RE.fullmatch(raw_expression)
        or "." not in raw_expression
        or not _LEAN_DECLARATION_RE.fullmatch(derivation_spec)
        or "." not in derivation_spec
        or derivation_spec in {"True", "False"}
        or lower >= upper
    ):
        return None
    raw_type = (
        f"({derivation_spec}) ∧ "
        f"({_fraction_lean_expression(lower)} ≤ ({raw_expression}) ∧ "
        f"({raw_expression}) ≤ {_fraction_lean_expression(upper)})"
    )
    reported_type = (
        "IChO2026Chem.Reporting.ReportsAtQuantum "
        f"({raw_expression}) {_decimal_lean_expression(reported_value)} "
        f"{_decimal_lean_expression(quantum)}"
    )
    return {
        "raw_result": raw_type,
        "reported_result": reported_type,
    }


def expected_nonnumeric_result_types(
    candidate: Mapping[str, Any],
) -> dict[str, str] | None:
    """Derive safe nonnumeric proposition types from named Lean specs.

    Only qualified identifiers are accepted here.  This prevents candidate
    JSON from injecting commands into a later low-privilege Lean verifier.
    The payload marker binds the complete human-facing result bytes; Review
    audits whether the named semantic spec faithfully represents those bytes.
    """
    result: dict[str, str] = {}
    for role in sorted(_RESULT_CONTRACT_ROLES):
        raw = candidate.get(role)
        if not isinstance(raw, Mapping):
            return None
        semantic_spec = str(raw.get("lean_expression") or "").strip()
        if (
            not _LEAN_DECLARATION_RE.fullmatch(semantic_spec)
            or "." not in semantic_spec
            or semantic_spec in {"True", "False"}
        ):
            return None
        payload_hash = blind_result_payload_sha256(candidate, role)
        result[role] = (
            f'("{payload_hash}" : String) = "{payload_hash}" ∧ '
            f"{semantic_spec}"
        )
    return result


def validate_blind_result_contracts(
    candidate: Mapping[str, Any],
) -> list[str]:
    """Validate exact candidate-to-theorem bindings without reading answers.

    Numeric types are generated, not trusted.  Other result kinds must embed
    their exact role payload digest in a nontrivial proposition; Review remains
    responsible for checking that proposition's domain semantics.
    """
    raw_contracts = candidate.get("lean_result_contracts")
    if not isinstance(raw_contracts, list) or len(raw_contracts) != 2:
        return [
            "answer-blind candidate lean_result_contracts must contain exactly "
            "raw_result and reported_result contracts"
        ]
    errors: list[str] = []
    by_role: dict[str, Mapping[str, Any]] = {}
    declarations: list[str] = []
    numeric_types = (
        expected_numeric_result_types(candidate)
        if candidate.get("result_kind") == "numeric"
        else None
    )
    nonnumeric_types = (
        expected_nonnumeric_result_types(candidate)
        if candidate.get("result_kind") in {
            "symbolic", "classification", "underdetermined",
        }
        else None
    )
    if candidate.get("result_kind") == "numeric" and numeric_types is None:
        errors.append(
            "numeric result contracts require a source-derived raw_result.derivation_spec, "
            "a nontrivial raw_result.lean_expression, a certified_interval containing "
            "raw_result.value, reported_result.value, and a valid precision"
        )
    if candidate.get("result_kind") != "numeric" and nonnumeric_types is None:
        errors.append(
            "nonnumeric result contracts require raw_result.lean_expression and "
            "reported_result.lean_expression to be safe fully-qualified Prop names"
        )
    for index, item in enumerate(raw_contracts, start=1):
        if not isinstance(item, Mapping):
            errors.append(f"lean_result_contracts[{index}] must be an object")
            continue
        missing = sorted(_RESULT_CONTRACT_FIELDS - set(item))
        extra = sorted(set(item) - _RESULT_CONTRACT_FIELDS)
        if missing or extra:
            errors.append(
                f"lean_result_contracts[{index}] has invalid fields"
                + (f"; missing {', '.join(missing)}" if missing else "")
                + (f"; unexpected {', '.join(extra)}" if extra else "")
            )
            continue
        role = str(item.get("role") or "")
        if role not in _RESULT_CONTRACT_ROLES or role in by_role:
            errors.append(f"lean_result_contracts[{index}] has invalid/duplicate role")
            continue
        by_role[role] = item
        declaration = str(item.get("declaration") or "").strip()
        declarations.append(declaration)
        if not _LEAN_DECLARATION_RE.fullmatch(declaration) or "." not in declaration:
            errors.append(
                f"lean_result_contracts[{index}].declaration must be an exact "
                "fully qualified Lean name"
            )
        expected_type = str(item.get("expected_type") or "").strip()
        if not expected_type:
            errors.append(f"lean_result_contracts[{index}].expected_type is empty")
            continue
        actual_type_hash = lean_result_type_sha256(expected_type)
        if str(item.get("expected_type_sha256") or "").lower() != actual_type_hash:
            errors.append(
                f"lean_result_contracts[{index}].expected_type_sha256 does not "
                "match the normalized expected_type"
            )
        payload_hash = blind_result_payload_sha256(candidate, role)
        if str(item.get("result_payload_sha256") or "").lower() != payload_hash:
            errors.append(
                f"lean_result_contracts[{index}].result_payload_sha256 does not "
                f"bind the candidate {role} payload"
            )
        if numeric_types is not None:
            if normalize_lean_result_type(expected_type) != normalize_lean_result_type(
                numeric_types[role]
            ):
                errors.append(
                    f"lean_result_contracts[{index}].expected_type is not the "
                    f"mechanically derived numeric {role} proposition"
                )
        elif nonnumeric_types is not None:
            if normalize_lean_result_type(expected_type) != normalize_lean_result_type(
                nonnumeric_types[role]
            ):
                errors.append(
                    f"lean_result_contracts[{index}].expected_type is not the "
                    f"mechanically derived nonnumeric {role} proposition"
                )
    if set(by_role) != _RESULT_CONTRACT_ROLES:
        errors.append("lean_result_contracts roles must be raw_result and reported_result")
    listed = candidate.get("lean_declarations")
    if not isinstance(listed, list) or listed != declarations:
        errors.append(
            "answer-blind candidate lean_declarations must exactly match the "
            "ordered lean_result_contracts declarations"
        )
    if len(set(declarations)) != len(declarations):
        errors.append("lean_result_contracts declaration names must be unique")
    return errors


def _normalized_evaluation_mode(report: Mapping[str, Any]) -> str:
    raw = report.get("evaluation_mode")
    if raw is None and isinstance(report.get("evaluation"), Mapping):
        raw = report["evaluation"].get("mode")
    mode = str(raw or "visible").strip().lower().replace("-", "_")
    return "answer_blind" if mode == "answer_blind" else mode


def is_answer_blind_contract(contract: Mapping[str, Any] | None) -> bool:
    """Return whether a resolved Review contract is answer-blind."""
    return bool(contract) and contract.get("evaluation_mode") == "answer_blind"


def _blind_key_tokens(key: object) -> tuple[str, list[str]]:
    snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", str(key).strip())
    normalized = re.sub(r"[^a-z0-9]+", "_", snake.lower()).strip("_")
    return normalized, [part for part in normalized.split("_") if part]


def _blind_answer_bearing_key(key: object) -> bool:
    normalized, tokens = _blind_key_tokens(key)
    # These are names of required anti-leakage audits, not answer payloads.
    if normalized in {"answer_independence", "answer_smuggling"}:
        return False
    if normalized == "reusable_conclusions":
        return True
    return any(
        any(part == stem or part == stem + "s" for stem in _BLIND_FORBIDDEN_REPORT_FIELDS)
        for part in tokens
    ) or normalized.startswith("official_")


def _forbidden_blind_report_paths(value: Any, path: str = "report") -> list[str]:
    """Find answer-bearing field names anywhere in an answer-blind report."""
    found: list[str] = []
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key)
            normalized, _tokens = _blind_key_tokens(key)
            child_path = f"{path}.{key}"
            # This required boolean is metadata, not answer content.
            if normalized == "official_answer_seen":
                if child is not False:
                    found.append(child_path)
            elif _blind_answer_bearing_key(key):
                found.append(child_path)
            found.extend(_forbidden_blind_report_paths(child, child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(_forbidden_blind_report_paths(child, f"{path}[{index}]"))
    return found


def _forbidden_blind_review_paths(value: Any, path: str = "review") -> list[str]:
    found: list[str] = []
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key)
            normalized, _tokens = _blind_key_tokens(key)
            child_path = f"{path}.{key}"
            if normalized == "official_answer_seen":
                if child is not False:
                    found.append(child_path)
            elif normalized in _BLIND_REVIEW_FORBIDDEN_FIELDS or _blind_answer_bearing_key(key):
                found.append(child_path)
            found.extend(_forbidden_blind_review_paths(child, child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(_forbidden_blind_review_paths(child, f"{path}[{index}]"))
    return found


def _validate_blind_candidate(
    *,
    project_path: Path,
    entry_id: str,
    blind_record_sha256: str,
    source_entry: Mapping[str, Any],
) -> tuple[str, str, str, list[str]]:
    """Validate and fingerprint the solver-owned, answer-free candidate."""
    relative = f"blind_candidates/{entry_id}.json" if entry_id else ""
    if not relative:
        return "", "", "", ["answer-blind candidate path cannot be resolved"]
    path = (project_path / relative).resolve()
    try:
        path.relative_to(project_path.resolve())
    except ValueError:
        return relative, "", "", ["answer-blind candidate escapes project root"]
    if not path.is_file() or path.is_symlink():
        return relative, "", "", [f"answer-blind candidate is missing or unsafe: {relative}"]
    digest = _file_sha256(path)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return relative, digest, "", [f"answer-blind candidate is invalid JSON: {exc}"]
    if not isinstance(value, Mapping):
        return relative, digest, "", ["answer-blind candidate must be a JSON object"]
    errors: list[str] = []
    missing_fields = sorted(_BLIND_CANDIDATE_FIELDS - set(value))
    extra_fields = sorted(set(value) - _BLIND_CANDIDATE_FIELDS)
    if missing_fields or extra_fields:
        errors.append(
            "answer-blind candidate has invalid fields"
            + (f"; missing {', '.join(missing_fields)}" if missing_fields else "")
            + (f"; unexpected {', '.join(extra_fields)}" if extra_fields else "")
        )
    expected = {
        "schema_version": 1,
        "protocol": "icho-answer-blind-v1",
        "phase": "solve",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "id": entry_id,
        "blind_record_sha256": blind_record_sha256,
    }
    for key, expected_value in expected.items():
        if value.get(key) != expected_value:
            errors.append(f"answer-blind candidate {key} does not match solve contract")
    allowed_result_kinds = {
        "numeric", "symbolic", "classification", "underdetermined"
    }
    if value.get("result_kind") not in allowed_result_kinds:
        errors.append("answer-blind candidate result_kind is missing or unsupported")
    raw_result = value.get("raw_result")
    if not isinstance(raw_result, Mapping):
        errors.append("answer-blind candidate raw_result must be an object")
    else:
        raw_extra = sorted(set(raw_result) - _BLIND_RAW_RESULT_FIELDS)
        if raw_extra:
            errors.append(
                "answer-blind candidate raw_result has unexpected fields: "
                + ", ".join(raw_extra)
            )
        if not isinstance(raw_result.get("expression"), str) or not str(
            raw_result.get("expression")
        ).strip():
            errors.append("answer-blind candidate raw_result.expression is missing")
        if value.get("result_kind") == "numeric" and _exact_rational_value(
            raw_result.get("value")
        ) is None:
            errors.append(
                "answer-blind numeric raw_result.value must be an exact decimal "
                "or canonical reduced numerator/denominator JSON string"
            )
    reported_result = value.get("reported_result")
    if not isinstance(reported_result, Mapping):
        errors.append("answer-blind candidate reported_result must be an object")
    else:
        reported_extra = sorted(set(reported_result) - _BLIND_REPORTED_RESULT_FIELDS)
        if reported_extra:
            errors.append(
                "answer-blind candidate reported_result has unexpected fields: "
                + ", ".join(reported_extra)
            )
        if value.get("result_kind") == "numeric" and not isinstance(
            reported_result.get("value"), str
        ):
            errors.append(
                "answer-blind numeric reported_result.value must be an exact JSON string"
            )
    domain_policy = source_entry.get("candidate_domain_policy")
    domain_provenance = value.get("candidate_domain_provenance")
    if not isinstance(domain_policy, Mapping) or not domain_policy:
        errors.append("answer-blind source candidate_domain_policy is missing")
    if (
        not isinstance(domain_provenance, Mapping)
        or set(domain_provenance) != {"candidate_domain_policy", "derivation"}
        or domain_provenance.get("candidate_domain_policy") != domain_policy
        or not isinstance(domain_provenance.get("derivation"), Mapping)
        or not domain_provenance.get("derivation")
    ):
        errors.append(
            "answer-blind candidate_domain_provenance must bind the exact source "
            "candidate_domain_policy and a nonempty structured derivation"
        )
    requested_outputs = source_entry.get("requested_outputs")
    if not isinstance(requested_outputs, list) or not requested_outputs:
        errors.append("answer-blind source requested_outputs is missing")
    else:
        seen_requested: set[str] = set()
        for index, requested in enumerate(requested_outputs, start=1):
            if not isinstance(requested, Mapping) or set(requested) != {
                "id", "source_requirement", "kind", "unit", "reporting_policy",
            }:
                errors.append(f"answer-blind requested output {index} has invalid fields")
                continue
            requested_id = str(requested.get("id") or "").strip()
            kind = str(requested.get("kind") or "").strip()
            policy = requested.get("reporting_policy")
            if not requested_id or requested_id in seen_requested:
                errors.append(f"answer-blind requested output {index} has invalid id")
            seen_requested.add(requested_id)
            if kind not in {"numeric", "integer", "formula", "classification", "finite_set"}:
                errors.append(f"answer-blind requested output {index} has invalid kind")
            if not isinstance(policy, Mapping) or not policy:
                errors.append(f"answer-blind requested output {index} has invalid policy")
        if len(requested_outputs) > 1 and value.get("result_kind") != "symbolic":
            errors.append("answer-blind multi-output candidate must be symbolic")
    for key in (
        "raw_result", "reported_result", "reporting_rule_source",
        "tolerance_provenance", "candidate_domain_provenance",
        "lean_declarations", "lean_result_contracts",
    ):
        if key not in value:
            errors.append(f"answer-blind candidate {key} is missing")
    if not isinstance(value.get("lean_declarations"), list) or not value.get(
        "lean_declarations"
    ):
        errors.append("answer-blind candidate lean_declarations must be non-empty")
    errors.extend(validate_blind_result_contracts(value))
    reporting_policy = source_entry.get("reporting_policy")
    if not isinstance(reporting_policy, Mapping) or not reporting_policy:
        errors.append("answer-blind source entry reporting_policy is missing")
    elif value.get("reporting_rule_source") != reporting_policy:
        errors.append(
            "answer-blind candidate reporting_rule_source must exactly equal the "
            "source entry reporting_policy"
        )
    measurement_policy = source_entry.get("measurement_policy")
    tolerance = value.get("tolerance_provenance")
    if not isinstance(measurement_policy, Mapping) or not measurement_policy:
        errors.append("answer-blind source entry measurement_policy is missing")
    elif not isinstance(tolerance, Mapping) or tolerance.get(
        "measurement_policy"
    ) != measurement_policy:
        errors.append(
            "answer-blind candidate tolerance_provenance.measurement_policy must "
            "exactly equal the source entry measurement_policy"
        )
    reported = value.get("reported_result")
    if isinstance(reported, Mapping) and isinstance(reporting_policy, Mapping):
        tie_rule = reporting_policy.get("tie_rule")
        if reported.get("rounding_rule") != tie_rule:
            errors.append(
                "answer-blind candidate reported_result.rounding_rule must equal "
                "source reporting_policy.tie_rule"
            )
        if value.get("result_kind") == "numeric" and reported.get(
            "precision"
        ) != reporting_policy.get("final_precision"):
            errors.append(
                "answer-blind numeric candidate reported_result.precision must "
                "exactly equal source reporting_policy.final_precision"
            )
    forbidden = _forbidden_blind_report_paths(value, path="candidate")
    if forbidden:
        errors.append(
            "answer-blind candidate contains forbidden field(s): "
            + ", ".join(forbidden)
        )
    contracts_digest = _value_sha256(value.get("lean_result_contracts"))
    return relative, digest, contracts_digest, errors


def _previous_blind_hashes(previous_parts: list[Any]) -> tuple[list[dict[str, str]], list[str]]:
    """Collect and validate any explicitly frozen prior-artifact digests."""
    hashes: list[dict[str, str]] = []
    errors: list[str] = []

    def visit(value: Any, path: str) -> None:
        if isinstance(value, Mapping):
            for raw_key, child in value.items():
                key = str(raw_key)
                normalized = key.strip().lower().replace("-", "_")
                child_path = f"{path}.{key}"
                if normalized.endswith("_sha256"):
                    digest = str(child or "").strip().lower()
                    if not _SHA256_RE.fullmatch(digest):
                        errors.append(
                            f"previous blind hash {child_path} is not a SHA-256 digest"
                        )
                    else:
                        hashes.append({"path": child_path, "sha256": digest})
                visit(child, child_path)
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, f"{path}[{index}]")

    visit(previous_parts, "entry.previous_parts")
    hashes.sort(key=lambda item: (item["path"], item["sha256"]))
    return hashes, errors


def _project_locator(path: Path, project_path: Path) -> str:
    try:
        relative = os.path.relpath(path.resolve(), start=project_path.resolve())
    except OSError:
        relative = os.path.relpath(path, start=project_path)
    return Path(relative).as_posix()


def blueprint_path_for_target(project_path: Path, target: Path) -> Path:
    rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    slug = "_".join(Path(rel).with_suffix("").parts)
    return project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"


def _resolve_project_path(project_path: Path, raw: str) -> Path:
    """Resolve a regular project-relative file without following symlinks."""
    if not isinstance(raw, str) or not raw.strip() or "\\" in raw:
        raise ValueError("path must be a non-empty POSIX project-relative locator")
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("path must stay project-relative and contain no '..'")
    root = project_path.resolve()
    cursor = root
    for part in relative.parts:
        if part in {"", "."}:
            continue
        cursor = cursor / part
        if cursor.is_symlink():
            raise ValueError(f"path may not traverse a symlink: {cursor}")
    resolved = cursor.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError("path escapes project root") from exc
    if not resolved.is_file() or resolved.is_symlink():
        raise ValueError("path is not a regular non-symlink file")
    return resolved


def _safe_existing_target(project_path: Path, target: Path) -> Path:
    root = project_path.resolve()
    lexical = Path(os.path.abspath(target))
    try:
        relative = lexical.relative_to(root)
    except ValueError as exc:
        raise ValueError("Lean target escapes project root") from exc
    return _resolve_project_path(root, relative.as_posix())


def _source_report_path(
    *, project_path: Path, target: Path, blueprint_path: Path,
) -> tuple[Path | None, list[str]]:
    errors: list[str] = []
    try:
        blueprint_path = _safe_existing_target(project_path, blueprint_path)
    except ValueError as exc:
        return None, [f"blueprint path is unsafe: {exc}"]
    try:
        blueprint = blueprint_path.read_text(encoding="utf-8")
    except OSError as exc:
        return None, [f"blueprint is missing or unreadable: {exc}"]
    matches = [item.strip() for item in _SOURCE_REPORT_RE.findall(blueprint)]
    if len(matches) != 1:
        return None, [
            "blueprint must contain exactly one % archon:source-report marker "
            f"for {target.name}; found {len(matches)}"
        ]
    try:
        report_path = _resolve_project_path(project_path, matches[0])
    except ValueError as exc:
        return None, [f"source report path is unsafe: {exc}"]
    return report_path, errors


def build_review_source_contract(
    *,
    project_path: Path,
    target: Path,
    profile: DomainProfile | None = None,
) -> dict[str, Any]:
    """Resolve and fingerprint one target's official evidence bundle.

    Chemistry uses this as a fail-closed contract.  Other profiles receive the
    same evidence when it is available, while retaining compatibility with
    older projects that never generated source reports.
    """
    project_path = project_path.resolve()
    try:
        target = _safe_existing_target(project_path, target)
    except ValueError as exc:
        return {
            "schema_version": SOURCE_CONTRACT_SCHEMA_VERSION,
            "required": True,
            "available": False,
            "valid": False,
            "domain": "unknown",
            "evaluation_mode": "visible",
            "authority": SOURCE_AUTHORITY,
            "target": "",
            "images": [],
            "errors": [f"Lean target path is unsafe: {exc}"],
        }
    profile = profile or load_domain_profile(project_path)
    required = profile.name == "chemistry"
    rel = target.relative_to(project_path).as_posix()
    blueprint_path = blueprint_path_for_target(project_path, target)
    errors: list[str] = []

    lean_sha256 = _file_sha256(target)
    if not lean_sha256:
        errors.append(f"Lean target is missing or unreadable: {target}")
    blueprint_sha256 = _file_sha256(blueprint_path)
    report_path, report_errors = _source_report_path(
        project_path=project_path,
        target=target,
        blueprint_path=blueprint_path,
    )
    errors.extend(report_errors)

    report: dict[str, Any] = {}
    source_sha256 = ""
    if report_path is not None and report_path.is_file():
        try:
            raw_report = report_path.read_bytes()
            loaded = json.loads(raw_report.decode("utf-8"))
            if not isinstance(loaded, dict):
                errors.append("source report root is not a JSON object")
            else:
                report = loaded
                source_sha256 = _sha256_bytes(raw_report)
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            errors.append(f"source report is unreadable or invalid JSON: {exc}")

    evaluation_mode = _normalized_evaluation_mode(report)
    answer_blind = evaluation_mode == "answer_blind"
    if report and evaluation_mode not in {"visible", "answer_blind"}:
        errors.append(f"unsupported source report evaluation_mode {evaluation_mode!r}")
    if answer_blind:
        if report.get("schema_version") != 3:
            errors.append("answer-blind source report requires schema_version=3")
        if report.get("official_answer_seen") is not False:
            errors.append(
                "answer-blind source report requires official_answer_seen=false"
            )
        if str(report.get("phase") or "").strip().lower() != "solve":
            errors.append("answer-blind source report requires phase=solve")
        forbidden_paths = _forbidden_blind_report_paths(report)
        if forbidden_paths:
            errors.append(
                "answer-blind source report contains forbidden field(s): "
                + ", ".join(forbidden_paths)
            )

    entry = report.get("entry")
    if not isinstance(entry, dict):
        entry = {}
        if report:
            errors.append("source report entry is missing")
    report_target = str(report.get("output_lean") or "").lstrip("./")
    if report and report_target != rel:
        errors.append(
            f"source report output_lean {report_target!r} does not match {rel!r}"
        )

    current_question = entry.get("current_question")
    question_field = "current_question"
    if not isinstance(current_question, str) or not current_question.strip():
        question_field = "question"
        current_question = entry.get("question")
    answer = None if answer_blind else entry.get("answer")
    previous_parts = entry.get("previous_parts")
    entry_id = str(entry.get("id") or "").strip()
    blind_record_sha256 = str(
        report.get("blind_record_sha256") or ""
    ).strip().lower()
    if answer_blind:
        if not entry_id or not re.fullmatch(r"[A-Za-z0-9._-]+", entry_id):
            errors.append("answer-blind source report entry.id is missing or unsafe")
        if not _SHA256_RE.fullmatch(blind_record_sha256):
            errors.append(
                "answer-blind source report blind_record_sha256 is invalid"
            )
        if entry.get("blind_record_sha256") != blind_record_sha256:
            errors.append(
                "source report blind_record_sha256 disagrees with entry"
            )
        (
            candidate_path,
            candidate_sha256,
            candidate_result_contracts_sha256,
            candidate_errors,
        ) = (
            _validate_blind_candidate(
                project_path=project_path,
                entry_id=entry_id,
                blind_record_sha256=blind_record_sha256,
                source_entry=entry,
            )
        )
        errors.extend(candidate_errors)
    else:
        candidate_path = ""
        candidate_sha256 = ""
        candidate_result_contracts_sha256 = ""
    if not isinstance(current_question, str) or not current_question.strip():
        errors.append(
            "source report entry.current_question/question is missing"
            if answer_blind
            else "source report entry.current_question is missing"
        )
        current_question = ""
    if not answer_blind and (not isinstance(answer, str) or not answer.strip()):
        errors.append("source report entry.answer is missing")
        answer = ""
    if not isinstance(previous_parts, list):
        errors.append("source report entry.previous_parts is not a list")
        previous_parts = []
    top_previous = report.get("previous_parts")
    if report and top_previous != previous_parts:
        errors.append(
            "source report previous_parts disagrees with entry.previous_parts"
        )
    previous_blind_hashes: list[dict[str, str]] = []
    if answer_blind:
        previous_blind_hashes, previous_hash_errors = _previous_blind_hashes(
            previous_parts
        )
        errors.extend(previous_hash_errors)

    raw_image_paths = entry.get("image_paths")
    if not isinstance(raw_image_paths, list):
        raw_image_paths = []
        errors.append("source report entry.image_paths is not a list")
    if required and not raw_image_paths:
        errors.append("chemistry source contract requires at least one image")
    images: list[dict[str, str]] = []
    seen_images: set[str] = set()
    for index, raw_path in enumerate(raw_image_paths, start=1):
        text = str(raw_path or "").strip()
        if not text:
            errors.append(f"source image path {index} is empty")
            continue
        try:
            image_path = _resolve_project_path(project_path, text)
        except ValueError as exc:
            errors.append(f"source image path {index} is unsafe: {exc}")
            continue
        locator = _project_locator(image_path, project_path)
        if locator in seen_images:
            errors.append(f"duplicate source image path: {locator}")
            continue
        seen_images.add(locator)
        digest = _file_sha256(image_path)
        if not digest:
            errors.append(f"source image is missing or unreadable: {image_path}")
        images.append({"path": locator, "sha256": digest})

    # Non-chemistry projects without generated source artifacts keep their
    # historical behavior.  If an optional bundle is present, however, it is
    # still hash-bound and audited exactly like the chemistry bundle.
    available = bool(report and source_sha256)
    if not required and not available:
        errors = []

    contract = {
        "schema_version": (
            BLIND_SOURCE_CONTRACT_SCHEMA_VERSION
            if answer_blind
            else SOURCE_CONTRACT_SCHEMA_VERSION
        ),
        "required": required,
        "available": available,
        "valid": not errors and (available or not required),
        "domain": profile.name,
        "evaluation_mode": evaluation_mode,
        "official_answer_seen": (
            False if answer_blind else bool(report.get("official_answer_seen", True))
        ),
        "authority": BLIND_SOURCE_AUTHORITY if answer_blind else SOURCE_AUTHORITY,
        "target": rel,
        "lean_sha256": lean_sha256,
        "blueprint": _project_locator(blueprint_path, project_path),
        "blueprint_sha256": blueprint_sha256,
        "source_report": (
            _project_locator(report_path, project_path) if report_path else ""
        ),
        "source_sha256": source_sha256,
        "current_question_sha256": _value_sha256(current_question),
        "previous_parts_sha256": _value_sha256(previous_parts),
        "images": images,
        "errors": errors,
        "official_evidence": {
            "current_question": current_question,
            "previous_parts": previous_parts,
        },
    }
    if answer_blind:
        contract.update({
            "entry_id": entry_id,
            "blind_record_sha256": blind_record_sha256,
            "blind_candidate_record": (
                candidate_path
            ),
            "blind_candidate_sha256": candidate_sha256,
            "lean_result_contracts_sha256": (
                candidate_result_contracts_sha256
            ),
            "question_field": question_field,
            "question_sha256": _value_sha256(current_question),
            "previous_blind_sha256": _value_sha256(previous_parts),
            "previous_blind_hashes": previous_blind_hashes,
            "requested_outputs": entry.get("requested_outputs", []),
        })
        # Do not materialize an answer value or answer digest in blind mode.
        contract["problem_evidence"] = contract.pop("official_evidence")
    else:
        contract["answer_sha256"] = _value_sha256(answer)
        contract["official_evidence"]["answer"] = answer
    return contract


def source_contract_provenance(contract: Mapping[str, Any]) -> dict[str, Any]:
    """Return the exact, compact provenance object a certificate must echo."""
    if is_answer_blind_contract(contract):
        return {
            "schema_version": BLIND_SOURCE_CONTRACT_SCHEMA_VERSION,
            "authority": BLIND_SOURCE_AUTHORITY,
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "target": str(contract.get("target") or ""),
            "lean_sha256": str(contract.get("lean_sha256") or ""),
            "blueprint": str(contract.get("blueprint") or ""),
            "blueprint_sha256": str(contract.get("blueprint_sha256") or ""),
            "source_report": str(contract.get("source_report") or ""),
            "source_sha256": str(contract.get("source_sha256") or ""),
            "entry_id": str(contract.get("entry_id") or ""),
            "blind_record_sha256": str(
                contract.get("blind_record_sha256") or ""
            ),
            "blind_candidate_record": str(
                contract.get("blind_candidate_record") or ""
            ),
            "blind_candidate_sha256": str(
                contract.get("blind_candidate_sha256") or ""
            ),
            "lean_result_contracts_sha256": str(
                contract.get("lean_result_contracts_sha256") or ""
            ),
            "requested_outputs_sha256": _value_sha256(
                contract.get("requested_outputs", [])
            ),
            "question_field": str(contract.get("question_field") or ""),
            "question_sha256": str(contract.get("question_sha256") or ""),
            "previous_blind_sha256": str(
                contract.get("previous_blind_sha256") or ""
            ),
            "previous_blind_hashes": [
                {
                    "path": str(item.get("path") or ""),
                    "sha256": str(item.get("sha256") or ""),
                }
                for item in contract.get("previous_blind_hashes", [])
                if isinstance(item, Mapping)
            ],
            "images": [
                {
                    "path": str(item.get("path") or ""),
                    "sha256": str(item.get("sha256") or ""),
                }
                for item in contract.get("images", [])
                if isinstance(item, Mapping)
            ],
        }
    return {
        "schema_version": SOURCE_CONTRACT_SCHEMA_VERSION,
        "authority": SOURCE_AUTHORITY,
        "target": str(contract.get("target") or ""),
        "lean_sha256": str(contract.get("lean_sha256") or ""),
        "blueprint": str(contract.get("blueprint") or ""),
        "blueprint_sha256": str(contract.get("blueprint_sha256") or ""),
        "source_report": str(contract.get("source_report") or ""),
        "source_sha256": str(contract.get("source_sha256") or ""),
        "current_question_sha256": str(
            contract.get("current_question_sha256") or ""
        ),
        "answer_sha256": str(contract.get("answer_sha256") or ""),
        "previous_parts_sha256": str(
            contract.get("previous_parts_sha256") or ""
        ),
        "images": [
            {
                "path": str(item.get("path") or ""),
                "sha256": str(item.get("sha256") or ""),
            }
            for item in contract.get("images", [])
            if isinstance(item, Mapping)
        ],
    }


def render_source_contract_prompt(contract: Mapping[str, Any]) -> str:
    """Render an authoritative evidence block for either target reviewer."""
    provenance = source_contract_provenance(contract)
    if is_answer_blind_contract(contract):
        evidence = contract.get("problem_evidence")
        if not isinstance(evidence, Mapping):
            evidence = {}
        errors = contract.get("errors")
        if not isinstance(errors, list):
            errors = []
        question_field = str(contract.get("question_field") or "question")
        return (
            "ANSWER-BLIND PROBLEM CONTRACT (first-class, immutable evidence):\n"
            f"- Authority: {BLIND_SOURCE_AUTHORITY}\n"
            "- Evaluation mode: answer_blind\n"
            "- Official answer seen: false\n"
            f"- Contract valid: {bool(contract.get('valid'))}\n"
            f"- Contract errors: {json.dumps(errors, ensure_ascii=False)}\n"
            "- Required provenance (echo exactly): "
            f"{json.dumps(provenance, ensure_ascii=False, sort_keys=True)}\n"
            f"- entry.{question_field}: "
            f"{json.dumps(evidence.get('current_question', ''), ensure_ascii=False)}\n"
            "- entry.previous_parts (questions/dependency policy only; no answers or bound certificates): "
            f"{json.dumps(evidence.get('previous_parts', []), ensure_ascii=False)}\n"
            "- Frozen candidate record to audit as an untrusted generated artifact: "
            f"{contract.get('blind_candidate_record') or 'MISSING'}\n"
            "Every listed problem image must be opened and inspected. Treat the "
            "problem statement and problem images as the only authority. Earlier "
            "results must be rederived inline unless the problem prints a fallback. "
            "The blueprint, Lean file, traces, "
            "and generated reports are untrusted artifacts to audit, never sources "
            "of problem facts. Do not open, search for, infer from, or request any "
            "official answer, worked solution, marking scheme, rubric, answer key, "
            "or visible-run artifact. First audit a symbolic specification derived "
            "only from the problem; then audit the independently derived candidate; "
            "then require the candidate, raw derivation, reporting rule, and hashes "
            "to be frozen before any later reveal or scoring. Verify every "
            "lean_result_contracts entry: its payload hash, normalized exact-type "
            "hash, fully-qualified declaration, and nontrivial result proposition "
            "must bind the raw/reported candidate to the compiled Lean result; a "
            "declaration of True or an unrelated tautology fails. Any answer-conditioned "
            "assumption, post-hoc tolerance, ungrounded candidate domain, staged "
            "rounding chosen to hit a value, or missing provenance must fail closed.\n"
        )
    evidence = contract.get("official_evidence")
    if not isinstance(evidence, Mapping):
        evidence = {}
    errors = contract.get("errors")
    if not isinstance(errors, list):
        errors = []
    return (
        "OFFICIAL SOURCE CONTRACT (first-class, immutable evidence):\n"
        f"- Authority: {SOURCE_AUTHORITY}\n"
        f"- Contract valid: {bool(contract.get('valid'))}\n"
        f"- Contract errors: {json.dumps(errors, ensure_ascii=False)}\n"
        f"- Required provenance (echo exactly): "
        f"{json.dumps(provenance, ensure_ascii=False, sort_keys=True)}\n"
        "- entry.current_question: "
        f"{json.dumps(evidence.get('current_question', ''), ensure_ascii=False)}\n"
        "- entry.answer (official rubric): "
        f"{json.dumps(evidence.get('answer', ''), ensure_ascii=False)}\n"
        "- entry.previous_parts: "
        f"{json.dumps(evidence.get('previous_parts', []), ensure_ascii=False)}\n"
        "Every listed source image must be opened and inspected. The blueprint, "
        "Lean file, traces, and task reports are generated artifacts and cannot "
        "override this source contract. If the blueprint or Lean reverses, "
        "weakens, rounds differently from, or otherwise conflicts with an "
        "official requested output, fail with a redraft route. Never reinterpret "
        "the official question to make generated artifacts self-consistent. "
        "The official rubric remains immutable. A passing Review may report "
        "official_answer_alignment=conflict only in the narrow case where the "
        "official givens or printed intermediates mathematically derive a claim "
        "that contradicts the official final claim, and Lean explicitly carries "
        "the honest derived result and the conflict. In that case include a "
        "source_inconsistency object with "
        f"kind={SOURCE_INCONSISTENCY_KIND}, status=verified, and nonempty "
        "official_claim, derived_claim, derivation_carrier, and evidence. This "
        "route is not for alternate interpretations, rounding preferences, "
        "missing information, or conflicts introduced by a blueprint, Lean, or "
        "generated report. Otherwise official_answer_alignment must be aligned; "
        "omit source_inconsistency. Every other source, contract, requested-"
        "output, image, chemistry, and blueprint-conflict check remains strict.\n"
    )


def _status_and_evidence(value: Any) -> tuple[str, str]:
    if not isinstance(value, Mapping):
        return "", ""
    return (
        str(value.get("status") or "").strip().lower(),
        str(value.get("evidence") or value.get("reason") or "").strip(),
    )


def normalized_review_source_certificate(review: Any) -> dict[str, Any]:
    """Persist the complete, strict source-audit evidence needed at freeze."""
    if not isinstance(review, Mapping):
        return {}

    def audit_group(name: str, checks: tuple[str, ...]) -> dict[str, Any]:
        raw = review.get(name)
        raw = raw if isinstance(raw, Mapping) else {}
        return {
            check: {
                "status": _status_and_evidence(raw.get(check))[0],
                "evidence": _status_and_evidence(raw.get(check))[1],
            }
            for check in checks
        }

    requested: list[dict[str, str]] = []
    raw_requested = review.get("requested_outputs")
    if isinstance(raw_requested, list):
        for item in raw_requested:
            if not isinstance(item, Mapping):
                continue
            requested.append({
                key: str(item.get(key) or "").strip().lower()
                if key == "status"
                else str(item.get(key) or "").strip()
                for key in ("source_requirement", "lean_carrier", "status", "evidence")
            })

    conflicts: list[dict[str, str]] = []
    raw_conflicts = review.get("blueprint_conflicts")
    if isinstance(raw_conflicts, list):
        for item in raw_conflicts:
            if not isinstance(item, Mapping):
                continue
            conflicts.append({
                key: str(item.get(key) or "").strip().lower()
                if key == "status"
                else str(item.get(key) or "").strip()
                for key in (
                    "source_claim", "blueprint_or_lean_claim", "status", "evidence",
                )
            })

    images: list[dict[str, Any]] = []
    raw_images = review.get("image_audit")
    if isinstance(raw_images, list):
        for item in raw_images:
            if not isinstance(item, Mapping):
                continue
            images.append({
                "path": str(item.get("path") or "").strip(),
                "sha256": str(item.get("sha256") or "").strip().lower(),
                "inspected": item.get("inspected"),
                "evidence": str(item.get("evidence") or "").strip(),
            })

    return {
        "source_contract": provenance_from_review(review),
        "blind_source_audit": audit_group(
            "blind_source_audit", _BLIND_SOURCE_CHECKS
        ),
        "contract_audit": audit_group("contract_audit", _CONTRACT_AUDIT_CHECKS),
        "requested_outputs": requested,
        "blueprint_conflicts": conflicts,
        "image_audit": images,
        "chemistry_checks": audit_group("chemistry_checks", _CHEMISTRY_CHECKS),
    }


def _verified_source_inconsistency(
    review: Mapping[str, Any],
) -> tuple[bool, str]:
    """Validate the optional, narrow official-source inconsistency claim."""
    raw = review.get("source_inconsistency")
    if raw is None:
        return False, ""
    if not isinstance(raw, Mapping):
        return False, "source_inconsistency must be an object"
    if raw.get("kind") != SOURCE_INCONSISTENCY_KIND:
        return (
            False,
            "source_inconsistency kind must be "
            f"{SOURCE_INCONSISTENCY_KIND}",
        )
    status = str(raw.get("status") or "").strip().lower()
    if status != "verified":
        return False, "source_inconsistency status must be verified"
    for key in _SOURCE_INCONSISTENCY_FIELDS:
        value = raw.get(key)
        if not isinstance(value, str) or not value.strip():
            return False, f"source_inconsistency {key} is missing"
    return True, ""


def source_assessment_from_review(review: Any) -> dict[str, Any]:
    """Normalize the source verdict fields retained by persistent gates.

    Validation remains the authority for accepting a Review.  This helper is
    deliberately loss-minimizing for the small source-assessment schema so a
    rejected certificate also leaves an inspectable, deterministic record.
    """
    alignment: dict[str, str] | None = None
    inconsistency: dict[str, str] | None = None
    if isinstance(review, Mapping):
        raw_alignment = review.get("official_answer_alignment")
        if isinstance(raw_alignment, Mapping):
            alignment = {
                "status": str(
                    raw_alignment.get("status")
                    or raw_alignment.get("verdict")
                    or ""
                ).strip().lower(),
                "evidence": str(
                    raw_alignment.get("evidence")
                    or raw_alignment.get("reason")
                    or ""
                ).strip(),
            }
        raw_inconsistency = review.get("source_inconsistency")
        if isinstance(raw_inconsistency, Mapping):
            inconsistency = {
                # ``kind`` is deliberately not token-normalized: validation
                # treats it as an exact schema discriminator.
                "kind": str(raw_inconsistency.get("kind") or ""),
                "status": str(
                    raw_inconsistency.get("status") or ""
                ).strip().lower(),
                **{
                    key: str(raw_inconsistency.get(key) or "").strip()
                    for key in _SOURCE_INCONSISTENCY_FIELDS
                },
            }
    return {
        "official_answer_alignment": alignment,
        "source_inconsistency": inconsistency,
    }


def validate_review_source_certificate(
    review: Mapping[str, Any],
    expected_contract: Mapping[str, Any] | None,
    *,
    passing: bool,
) -> str:
    """Validate hashes and chemistry-specific source-audit fields.

    Optional legacy/non-chemistry bundles do not change the old certificate
    schema.  A chemistry bundle is fail closed, including when preparation did
    not leave enough evidence to compute all expected hashes.
    """
    if not expected_contract:
        return ""
    answer_blind = is_answer_blind_contract(expected_contract)
    required = bool(expected_contract.get("required"))
    available = bool(expected_contract.get("available"))
    actual = review.get("source_contract")
    # Preserve legacy non-chemistry certificates.  New non-chemistry workers
    # still emit and bind provenance when a source bundle exists, but an older
    # certificate that predates this field remains admissible.
    if (
        not required
        and not answer_blind
        and (not available or not isinstance(actual, Mapping))
    ):
        return ""
    errors = expected_contract.get("errors")
    errors = errors if isinstance(errors, list) else []
    if passing and (not expected_contract.get("valid") or errors):
        return "official source contract is invalid: " + "; ".join(
            str(item) for item in errors
        )

    expected = source_contract_provenance(expected_contract)
    if not isinstance(actual, Mapping):
        return "source_contract provenance is missing"
    provenance_keys = (
        (
            "schema_version", "authority", "evaluation_mode",
            "official_answer_seen", "target", "lean_sha256", "blueprint",
            "blueprint_sha256", "source_report", "source_sha256",
            "entry_id", "blind_record_sha256", "blind_candidate_record",
            "blind_candidate_sha256", "lean_result_contracts_sha256",
            "requested_outputs_sha256",
            "question_field",
            "question_sha256", "previous_blind_sha256", "previous_blind_hashes",
        )
        if answer_blind
        else (
            "schema_version", "authority", "target", "lean_sha256", "blueprint",
            "blueprint_sha256", "source_report", "source_sha256",
            "current_question_sha256", "answer_sha256", "previous_parts_sha256",
        )
    )
    for key in provenance_keys:
        if actual.get(key) != expected.get(key):
            return f"source_contract {key} does not match authoritative evidence"
    actual_images = actual.get("images")
    if actual_images != expected["images"]:
        return "source_contract image paths or hashes are stale/mismatched"

    if not required and not answer_blind:
        return ""

    if answer_blind:
        forbidden = _forbidden_blind_review_paths(review)
        if forbidden:
            return (
                "answer-blind Review contains forbidden field(s): "
                + ", ".join(forbidden)
            )
        blind_audit = review.get("blind_source_audit")
        if not isinstance(blind_audit, Mapping):
            return "blind_source_audit is missing"
        blind_failed = False
        for name in _BLIND_SOURCE_CHECKS:
            check_status, check_evidence = _status_and_evidence(
                blind_audit.get(name)
            )
            if check_status not in _PASS | _FAIL:
                return (
                    f"blind_source_audit.{name} has unsupported status "
                    f"{check_status!r}"
                )
            if not check_evidence:
                return f"blind_source_audit.{name} evidence is missing"
            blind_failed = blind_failed or check_status in _FAIL
        if passing and blind_failed:
            return "passing verdict contradicts failed blind_source_audit"

    audit_groups = [("contract_audit", _CONTRACT_AUDIT_CHECKS)]
    if not answer_blind:
        audit_groups.insert(
            0, ("independent_source_audit", _INDEPENDENT_SOURCE_CHECKS)
        )
    for group_name, names in audit_groups:
        group = review.get(group_name)
        if not isinstance(group, Mapping):
            return f"{group_name} is missing"
        group_failed = False
        for name in names:
            check_status, check_evidence = _status_and_evidence(group.get(name))
            if check_status not in _PASS | _FAIL:
                return (
                    f"{group_name}.{name} has unsupported status "
                    f"{check_status!r}"
                )
            if not check_evidence:
                return f"{group_name}.{name} evidence is missing"
            group_failed = group_failed or check_status in _FAIL
        if passing and group_failed:
            return f"passing verdict contradicts failed {group_name}"

    requested = review.get("requested_outputs")
    if not isinstance(requested, list) or not requested:
        qualifier = "problem" if answer_blind else "official"
        return f"requested_outputs must contain every {qualifier} requested output"
    requested_failed = False
    for index, item in enumerate(requested, start=1):
        if not isinstance(item, Mapping):
            return f"requested output {index} is not an object"
        for key in ("source_requirement", "lean_carrier", "status", "evidence"):
            if not str(item.get(key) or "").strip():
                return f"requested output {index} is missing {key}"
        status = str(item.get("status") or "").strip().lower()
        if status not in _PASS | _FAIL:
            return f"requested output {index} has unsupported status {status!r}"
        requested_failed = requested_failed or status in _FAIL
    if passing and requested_failed:
        return "passing verdict contradicts a blocked requested output"

    if not answer_blind:
        alignment = review.get("official_answer_alignment")
        status, evidence = _status_and_evidence(alignment)
        if status not in _PASS | _FAIL or not evidence:
            return "official_answer_alignment status/evidence is missing"
        verified_inconsistency, inconsistency_error = (
            _verified_source_inconsistency(review)
        )
        if inconsistency_error:
            return inconsistency_error
        if status == "conflict":
            if passing and not verified_inconsistency:
                return (
                    "passing official_answer_alignment conflict requires verified "
                    "source_inconsistency"
                )
        else:
            if verified_inconsistency:
                return (
                    "verified source_inconsistency requires "
                    "official_answer_alignment status=conflict"
                )
            if passing and status not in _PASS:
                return "passing verdict contradicts official answer alignment"

    conflicts = review.get("blueprint_conflicts")
    if not isinstance(conflicts, list):
        return "blueprint_conflicts must be a list"
    for index, conflict in enumerate(conflicts, start=1):
        if not isinstance(conflict, Mapping):
            return f"blueprint conflict {index} is not an object"
        for key in (
            "source_claim", "blueprint_or_lean_claim", "status", "evidence",
        ):
            if not str(conflict.get(key) or "").strip():
                return f"blueprint conflict {index} is missing {key}"
        conflict_status = str(conflict.get("status") or "").strip().lower()
        resolved_status = (
            "resolved_in_favor_of_problem_source"
            if answer_blind
            else "resolved_in_favor_of_official_source"
        )
        if conflict_status not in {resolved_status, "unresolved", "failed"}:
            return f"blueprint conflict {index} has invalid status"
        if passing and conflict_status != resolved_status:
            return "passing verdict leaves a blueprint/source conflict unresolved"

    image_audit = review.get("image_audit")
    if not isinstance(image_audit, list):
        return "image_audit must be a list"
    expected_images = expected["images"]
    if len(image_audit) != len(expected_images):
        return "image_audit does not cover every authoritative image"
    for index, (audit, image) in enumerate(
        zip(image_audit, expected_images), start=1,
    ):
        if not isinstance(audit, Mapping):
            return f"image audit {index} is not an object"
        if (
            audit.get("path") != image["path"]
            or audit.get("sha256") != image["sha256"]
        ):
            return f"image audit {index} path/hash does not match source contract"
        if not isinstance(audit.get("inspected"), bool):
            return f"image audit {index} inspected must be boolean"
        if passing and audit.get("inspected") is not True:
            return f"image audit {index} was not inspected"
        if not str(audit.get("evidence") or "").strip():
            return f"image audit {index} evidence is missing"

    chemistry = review.get("chemistry_checks")
    if not isinstance(chemistry, Mapping):
        return "chemistry_checks are missing"
    chemistry_failed = False
    for name in _CHEMISTRY_CHECKS:
        check_status, check_evidence = _status_and_evidence(chemistry.get(name))
        if check_status not in _PASS | _FAIL | _NOT_APPLICABLE:
            return f"chemistry check {name} has unsupported status {check_status!r}"
        if not check_evidence:
            return f"chemistry check {name} evidence is missing"
        chemistry_failed = chemistry_failed or check_status in _FAIL
    if passing and chemistry_failed:
        return "passing verdict contradicts a failed chemistry check"
    return ""


def provenance_from_review(review: Any) -> dict[str, Any] | None:
    if not isinstance(review, Mapping):
        return None
    raw = review.get("source_contract")
    return dict(raw) if isinstance(raw, Mapping) else None


def stored_provenance_matches_current(
    *, project_path: Path, target: Path, provenance: Any,
) -> tuple[bool, str]:
    """Compare a persisted certificate binding with current target inputs."""
    profile = load_domain_profile(project_path)
    if profile.name != "chemistry":
        return True, ""
    contract = build_review_source_contract(
        project_path=project_path, target=target, profile=profile,
    )
    if not contract.get("valid"):
        errors = contract.get("errors") or ["invalid official source contract"]
        return False, "; ".join(str(item) for item in errors)
    expected = source_contract_provenance(contract)
    if not isinstance(provenance, Mapping):
        return False, "stored Review certificate has no source_contract provenance"
    for key, value in expected.items():
        if provenance.get(key) != value:
            return False, f"stored Review certificate is stale: {key} changed"
    return True, ""
