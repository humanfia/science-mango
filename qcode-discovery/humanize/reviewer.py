"""Independent, read-only Codex review for qcode search rounds."""

from __future__ import annotations

import copy
import json
import re
import subprocess
import time
from collections.abc import Callable
from pathlib import Path
from typing import Any

from evaluation.geometry import candidate_geometry
from evaluation.search_contract import (
    LEGACY_GEOMETRY_CONTRACT,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    lattices_for_geometry_contract,
)

from .state import candidate_terminal_negative


_LEGACY_REVIEW_FIELDS = frozenset(
    {"verdict", "summary", "risks", "recommended_focus", "lessons"}
)
_CURRENT_REVIEW_FIELDS = _LEGACY_REVIEW_FIELDS | {
    "schema_version",
    "search_action",
}
_REVIEW_VERDICTS = ("continue", "promote", "stop", "reject_round")
_RISK_SEVERITIES = ("P0", "P1", "P2", "P3")
_SEARCH_ACTION_INTENTS = (
    "maintain",
    "diversify",
    "explore_undercovered",
    "repair_verified_failure",
    "exploit_trusted_exact",
    "expand_bb_family",
    "change_bb_search_representation",
)
_SEARCH_ACTION_DIMENSIONS = (
    "portfolio_role",
    "algebraic_relation_type",
    "support_split_type",
    "orbit_span_bin",
    "geometry_twist_class",
    "mutation_tactic",
    "renderer_descriptor_id",
    "catalog_manifest_id",
    "catalog_kind",
)
_SEARCH_ACTION_IDENTIFIER_DIMENSIONS = frozenset({
    "renderer_descriptor_id",
    "catalog_manifest_id",
})
_SEARCH_ACTION_SAFE_ID = re.compile(
    r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}\Z"
)
_SEARCH_ACTION_DIRECTIONS = ("increase", "decrease", "maintain")
_SEARCH_ACTION_PRIORITIES = ("high", "medium", "low")
_SEARCH_ACTION_SOURCES = (
    "current_round",
    "round_history",
    "trusted_exact_history",
    "candidate_diversity",
    "failure_direction_feedback",
)
_SEARCH_ACTION_VALUES = {
    "portfolio_role": frozenset(
        {
            "affine_automorphism_cover",
            "shared_anchor_coset_cover",
            "complementary_diagonal_cover",
            "asymmetric_anchor_cover",
            "failure_repair_restart",
        }
    ),
    "algebraic_relation_type": frozenset(
        {
            "affine_orbit",
            "shared_anchor_coset",
            "complementary_diagonal",
            "asymmetric_anchor",
            "unstructured",
        }
    ),
    "support_split_type": frozenset(
        {"2+2", "2+3", "3+2", "2+4", "4+2", "3+3"}
    ),
    "orbit_span_bin": frozenset({"0", "1", "2"}),
    "geometry_twist_class": frozenset({"0", "1", "2"}),
    "mutation_tactic": frozenset(
        {
            "novel_structure_exploration",
            "repair_x_low_weight",
            "repair_z_low_weight",
            "repair_dual_balance",
        }
    ),
    "catalog_kind": frozenset({"action", "cover", "protograph"}),
}

def _review_text_schema(*, maximum: int) -> dict[str, Any]:
    """Return API-compatible generation-time text constraints.

    Codex structured outputs reject regex lookaround, so JSON Schema enforces
    type and length while ``validate_review`` rejects reserved ``QCODE_``
    markers recursively before an artifact is persisted or consumed.
    """

    return {
        "type": "string",
        "minLength": 1,
        "maxLength": maximum,
    }


def _focus_item_schema(
    dimension: str, values: frozenset[str]
) -> dict[str, Any]:
    """Close one dimension/value branch for structured-output generation."""

    return {
        "type": "object",
        "additionalProperties": False,
        "required": ["dimension", "value", "direction", "priority"],
        "properties": {
            "dimension": {"type": "string", "const": dimension},
            "value": {"type": "string", "enum": sorted(values)},
            "direction": {
                "type": "string",
                "enum": list(_SEARCH_ACTION_DIRECTIONS),
            },
            "priority": {
                "type": "string",
                "enum": list(_SEARCH_ACTION_PRIORITIES),
            },
        },
    }


def _identifier_focus_item_schema(dimension: str) -> dict[str, Any]:
    """Allow an inert registry ID while forbidding code-like text."""

    return {
        "type": "object",
        "additionalProperties": False,
        "required": ["dimension", "value", "direction", "priority"],
        "properties": {
            "dimension": {"type": "string", "const": dimension},
            "value": {
                "type": "string",
                "minLength": 1,
                "maxLength": 128,
                "pattern": "^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$",
            },
            "direction": {
                "type": "string",
                "enum": list(_SEARCH_ACTION_DIRECTIONS),
            },
            "priority": {
                "type": "string",
                "enum": list(_SEARCH_ACTION_PRIORITIES),
            },
        },
    }


REVIEW_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "additionalProperties": False,
    "required": [
        "schema_version",
        "verdict",
        "summary",
        "risks",
        "recommended_focus",
        "lessons",
        "search_action",
    ],
    "properties": {
        "schema_version": {"type": "integer", "const": 2},
        "verdict": {
            "type": "string",
            "enum": list(_REVIEW_VERDICTS),
        },
        "summary": _review_text_schema(maximum=4000),
        "risks": {
            "type": "array",
            "maxItems": 16,
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["severity", "finding", "evidence"],
                "properties": {
                    "severity": {
                        "type": "string", "enum": list(_RISK_SEVERITIES)
                    },
                    "finding": _review_text_schema(maximum=2000),
                    "evidence": _review_text_schema(maximum=4000),
                },
            },
        },
        "recommended_focus": {
            "type": "array",
            "maxItems": 16,
            "items": _review_text_schema(maximum=500),
        },
        "lessons": {
            "type": "array",
            "maxItems": 16,
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["insight", "evidence", "action"],
                "properties": {
                    "insight": _review_text_schema(maximum=1000),
                    "evidence": _review_text_schema(maximum=2000),
                    "action": _review_text_schema(maximum=1000),
                },
            },
        },
        "search_action": {
            "type": "object",
            "additionalProperties": False,
            "required": [
                "schema_version",
                "advisory_only",
                "intent",
                "horizon_rounds",
                "focus",
                "evidence_refs",
                "rationale",
            ],
            "properties": {
                "schema_version": {"type": "integer", "const": 1},
                "advisory_only": {"type": "boolean", "const": True},
                "intent": {
                    "type": "string",
                    "enum": list(_SEARCH_ACTION_INTENTS),
                },
                "horizon_rounds": {
                    "type": "integer",
                    "minimum": 1,
                    "maximum": 3,
                },
                "focus": {
                    "type": "array",
                    "maxItems": 8,
                    "items": {
                        "anyOf": [
                            _focus_item_schema(dimension, values)
                            for dimension, values in _SEARCH_ACTION_VALUES.items()
                        ] + [
                            _identifier_focus_item_schema(dimension)
                            for dimension in sorted(
                                _SEARCH_ACTION_IDENTIFIER_DIMENSIONS
                            )
                        ],
                    },
                },
                "evidence_refs": {
                    "type": "array",
                    "maxItems": 16,
                    "items": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["source", "round", "candidate_key"],
                        "properties": {
                            "source": {
                                "type": "string",
                                "enum": list(_SEARCH_ACTION_SOURCES),
                            },
                            "round": {
                                "type": ["integer", "null"],
                                "minimum": 1,
                            },
                            "candidate_key": {
                                "type": ["string", "null"],
                                "pattern": "^[0-9a-f]{20,64}$",
                            },
                        },
                    },
                },
                "rationale": _review_text_schema(maximum=4000),
            },
        },
    },
}


class ReviewError(RuntimeError):
    """The independent review failed or violated its output contract."""


def _validate_exact_fields(
    value: dict[str, Any], expected: frozenset[str], label: str
) -> None:
    missing = expected - value.keys()
    extra = value.keys() - expected
    if missing:
        raise ReviewError(f"{label} missing fields: " + ", ".join(sorted(missing)))
    if extra:
        raise ReviewError(
            f"{label} contains unsupported fields: " + ", ".join(sorted(extra))
        )


def _validate_string(value: Any, label: str, *, maximum: int) -> None:
    if not isinstance(value, str) or not value.strip():
        raise ReviewError(f"{label} must be a non-empty string")
    if len(value) > maximum:
        raise ReviewError(f"{label} exceeds maximum length {maximum}")


def _reject_reserved_markers(value: Any, path: str = "review") -> None:
    if isinstance(value, str):
        if "QCODE_" in value:
            raise ReviewError(f"{path} contains a reserved QCODE_ marker")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            _reject_reserved_markers(item, f"{path}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _reject_reserved_markers(item, f"{path}[{index}]")


def _validate_search_action(value: Any) -> None:
    if not isinstance(value, dict):
        raise ReviewError("review search_action must be an object")
    expected = frozenset(
        {
            "schema_version",
            "advisory_only",
            "intent",
            "horizon_rounds",
            "focus",
            "evidence_refs",
            "rationale",
        }
    )
    _validate_exact_fields(value, expected, "review search_action")
    if isinstance(value["schema_version"], bool) or value["schema_version"] != 1:
        raise ReviewError("review search_action.schema_version must be 1")
    if value["advisory_only"] is not True:
        raise ReviewError("review search_action.advisory_only must be true")
    if value["intent"] not in _SEARCH_ACTION_INTENTS:
        raise ReviewError(f"invalid search_action intent: {value['intent']!r}")
    horizon = value["horizon_rounds"]
    if isinstance(horizon, bool) or not isinstance(horizon, int) or not 1 <= horizon <= 3:
        raise ReviewError("review search_action.horizon_rounds must be an integer 1-3")

    focus = value["focus"]
    if not isinstance(focus, list) or len(focus) > 8:
        raise ReviewError("review search_action.focus must be an array of at most 8 items")
    focus_fields = frozenset({"dimension", "value", "direction", "priority"})
    for index, item in enumerate(focus):
        if not isinstance(item, dict):
            raise ReviewError(f"review search_action.focus[{index}] must be an object")
        _validate_exact_fields(
            item, focus_fields, f"review search_action.focus[{index}]"
        )
        dimension = item["dimension"]
        if dimension not in _SEARCH_ACTION_DIMENSIONS:
            raise ReviewError(
                f"invalid search_action focus dimension: {dimension!r}"
            )
        if dimension in _SEARCH_ACTION_IDENTIFIER_DIMENSIONS:
            if (
                not isinstance(item["value"], str)
                or _SEARCH_ACTION_SAFE_ID.fullmatch(item["value"]) is None
            ):
                raise ReviewError(
                    "search_action registry identifier is unsafe"
                )
        else:
            allowed_values = _SEARCH_ACTION_VALUES[dimension]
            if item["value"] not in allowed_values:
                raise ReviewError(
                    "search_action focus value is incompatible with dimension "
                    f"{dimension!r}: {item['value']!r}"
                )
        if item["direction"] not in _SEARCH_ACTION_DIRECTIONS:
            raise ReviewError(
                f"invalid search_action focus direction: {item['direction']!r}"
            )
        if item["priority"] not in _SEARCH_ACTION_PRIORITIES:
            raise ReviewError(
                f"invalid search_action focus priority: {item['priority']!r}"
            )

    refs = value["evidence_refs"]
    if not isinstance(refs, list) or len(refs) > 16:
        raise ReviewError(
            "review search_action.evidence_refs must be an array of at most 16 items"
        )
    ref_fields = frozenset({"source", "round", "candidate_key"})
    for index, item in enumerate(refs):
        if not isinstance(item, dict):
            raise ReviewError(
                f"review search_action.evidence_refs[{index}] must be an object"
            )
        _validate_exact_fields(
            item, ref_fields, f"review search_action.evidence_refs[{index}]"
        )
        if item["source"] not in _SEARCH_ACTION_SOURCES:
            raise ReviewError(
                f"invalid search_action evidence source: {item['source']!r}"
            )
        round_number = item["round"]
        if round_number is not None and (
            isinstance(round_number, bool)
            or not isinstance(round_number, int)
            or round_number < 1
        ):
            raise ReviewError(
                "search_action evidence round must be null or a positive integer"
            )
        candidate_key = item["candidate_key"]
        if candidate_key is not None and (
            not isinstance(candidate_key, str)
            or not 20 <= len(candidate_key) <= 64
            or any(character not in "0123456789abcdef" for character in candidate_key)
        ):
            raise ReviewError(
                "search_action evidence candidate_key must be null or 20-64 "
                "lowercase hexadecimal characters"
            )
    _validate_string(
        value["rationale"], "review search_action.rationale", maximum=4000
    )


def _validate_legacy_review(value: dict[str, Any]) -> dict[str, Any]:
    """Replay the original v1 validator without imposing v2 constraints.

    Historical artifacts were intentionally validated permissively: unknown
    top-level and nested fields were retained, nested scalar text was checked
    through ``str(...)``, and there were no collection/length or reserved-word
    limits.  Keeping those exact semantics is important for durable replay;
    fresh generation never enters this path.
    """

    missing = _LEGACY_REVIEW_FIELDS - value.keys()
    if missing:
        raise ReviewError(
            "review output missing fields: " + ", ".join(sorted(missing))
        )
    if value["verdict"] not in _REVIEW_VERDICTS:
        raise ReviewError(f"invalid review verdict: {value['verdict']!r}")
    if not isinstance(value["summary"], str) or not value["summary"].strip():
        raise ReviewError("review summary must be non-empty")
    if not all(
        isinstance(value[name], list)
        for name in ("risks", "recommended_focus", "lessons")
    ):
        raise ReviewError(
            "review risks, recommended_focus, and lessons must be arrays"
        )
    for risk in value["risks"]:
        if not isinstance(risk, dict) or risk.get("severity") not in (
            _RISK_SEVERITIES
        ):
            raise ReviewError("every risk needs severity P0-P3")
        if not str(risk.get("finding", "")).strip() or not str(
            risk.get("evidence", "")
        ).strip():
            raise ReviewError("every risk needs a finding and evidence")
    for lesson in value["lessons"]:
        if not isinstance(lesson, dict) or any(
            not str(lesson.get(field, "")).strip()
            for field in ("insight", "evidence", "action")
        ):
            raise ReviewError("every lesson needs insight, evidence, and action")
    return value


def _validate_current_review(value: dict[str, Any]) -> dict[str, Any]:
    """Validate a current v2 artifact using the strict generation contract."""

    _validate_exact_fields(value, _CURRENT_REVIEW_FIELDS, "review output")
    if isinstance(value["schema_version"], bool) or value["schema_version"] != 2:
        raise ReviewError("review schema_version must be 2")
    if value["verdict"] not in _REVIEW_VERDICTS:
        raise ReviewError(f"invalid review verdict: {value['verdict']!r}")
    _validate_string(value["summary"], "review summary", maximum=4000)
    if not all(
        isinstance(value[name], list)
        for name in ("risks", "recommended_focus", "lessons")
    ):
        raise ReviewError(
            "review risks, recommended_focus, and lessons must be arrays"
        )
    if len(value["risks"]) > 16:
        raise ReviewError("review risks must contain at most 16 items")
    if len(value["recommended_focus"]) > 16:
        raise ReviewError("review recommended_focus must contain at most 16 items")
    if len(value["lessons"]) > 16:
        raise ReviewError("review lessons must contain at most 16 items")
    risk_fields = frozenset({"severity", "finding", "evidence"})
    for index, risk in enumerate(value["risks"]):
        if not isinstance(risk, dict):
            raise ReviewError(f"review risks[{index}] must be an object")
        _validate_exact_fields(risk, risk_fields, f"review risks[{index}]")
        if risk["severity"] not in _RISK_SEVERITIES:
            raise ReviewError("every risk needs severity P0-P3")
        _validate_string(
            risk["finding"], f"review risks[{index}].finding", maximum=2000
        )
        _validate_string(
            risk["evidence"], f"review risks[{index}].evidence", maximum=4000
        )
    for index, focus in enumerate(value["recommended_focus"]):
        _validate_string(
            focus, f"review recommended_focus[{index}]", maximum=500
        )
    lesson_fields = frozenset({"insight", "evidence", "action"})
    for index, lesson in enumerate(value["lessons"]):
        if not isinstance(lesson, dict):
            raise ReviewError(f"review lessons[{index}] must be an object")
        _validate_exact_fields(lesson, lesson_fields, f"review lessons[{index}]")
        _validate_string(
            lesson["insight"], f"review lessons[{index}].insight", maximum=1000
        )
        _validate_string(
            lesson["evidence"], f"review lessons[{index}].evidence", maximum=2000
        )
        _validate_string(
            lesson["action"], f"review lessons[{index}].action", maximum=1000
        )
    _validate_search_action(value["search_action"])
    _reject_reserved_markers(value)
    return value


def validate_review(
    value: Any, *, require_current: bool = False
) -> dict[str, Any]:
    """Validate permissive legacy-v1 or strict current-v2 reviewer output.

    The default preserves the historical v1 validator semantics so previously
    accepted artifacts remain replayable.  Objects carrying both v2-only
    fields are validated strictly.  New Codex generation uses
    ``REVIEW_SCHEMA`` and always sets ``require_current=True``.
    """
    if not isinstance(value, dict):
        raise ReviewError("review output must be a JSON object")
    if require_current:
        if not {"schema_version", "search_action"}.issubset(value):
            raise ReviewError(
                "legacy reviewer output is not accepted for this operation"
            )
        return _validate_current_review(value)
    if {"schema_version", "search_action"}.issubset(value):
        return _validate_current_review(value)
    return _validate_legacy_review(value)


_ADVISORY_ROW_FIELDS = (
    "candidate_key",
    "construction",
    "action_id",
    "action_family_bin",
    "subgroup_normal",
    "support_orbit_bin",
    "left_support",
    "right_support",
    "geometry",
    "ell",
    "m",
    "n",
    "k",
    "A_terms",
    "B_terms",
    "archive_cell",
    "archive_round",
    "pattern_type",
    "pattern_classifier_version",
    "term_count",
    "stage",
    "search_status",
    "distance_status",
    "d_is_exact",
    "distance_trusted",
    "milp_attempted",
    "candidate_persistence_lane",
    "candidate_persistence_reason",
    "winner_capable_parameters",
    "minimum_winning_distance",
    "singleton_distance_upper_bound",
    "static_eligibility",
    "structural_novelty",
    "distance_retry_required",
    "distance_backend_error",
)

_TRUSTED_EXACT_COMPACT_FIELDS = (
    "candidate_key",
    "construction",
    "action_id",
    "action_family_bin",
    "subgroup_normal",
    "support_orbit_bin",
    "left_support",
    "right_support",
    "geometry",
    "ell",
    "m",
    "n",
    "k",
    "d",
    "fom",
    "A_terms",
    "B_terms",
    "archive_cell",
    "archive_round",
    "pattern_type",
    "pattern_classifier_version",
    "term_count",
    "stage",
    "search_status",
    "distance_status",
    "d_is_exact",
    "distance_trusted",
    "algebraic_relation_type",
    "support_split_type",
    "orbit_span_bin",
    "candidate_persistence_lane",
    "audit_attempt",
    "trusted_win_gate",
)
_ROUND_HISTORY_COMPACT_FIELDS = (
    "round",
    "round_number",
    "new_candidates",
    "new_candidate_count",
    "milp_audited",
    "audited_count",
    "milp_audited_count",
    "milp_exact",
    "milp_exact_count",
    "trusted_exact_total",
    "trusted_exact_count",
    "trusted_win_total",
    "trusted_win_count",
    "unresolved_count",
    "best_exact_fom",
    "review_verdict",
    "review_summary",
    "search_action",
    "search_regime",
    "candidate_diversity",
    "sealed_exact_audit",
    "failure_direction_feedback",
    "portfolio_allocation",
    "stage_statuses",
)
_TRUSTED_EXACT_DETAILS_LIMIT = 20
_MEMORY_EXCERPT_LIMIT = 12000
_REVIEWABLE_EVOLUTION_LATTICES = frozenset(
    lattices_for_geometry_contract(LEGACY_GEOMETRY_CONTRACT)
) | frozenset(
    lattices_for_geometry_contract(TWISTED_TORUS_GEOMETRY_CONTRACT)
)


def _normalized_compact_construction(
    row: dict[str, Any],
) -> dict[str, Any] | None:
    if not isinstance(row.get("construction"), dict):
        return None
    try:
        from evaluation.construction import normalize_construction_claim

        normalized = normalize_construction_claim(dict(row))
        construction = (
            normalized.get("construction")
            if isinstance(normalized, dict)
            and isinstance(normalized.get("construction"), dict)
            else normalized
        )
        return dict(construction) if isinstance(construction, dict) else None
    except (ImportError, KeyError, TypeError, ValueError, OverflowError):
        return None


def _negative_witness_geometry(
    row: dict[str, Any],
    *,
    formal_audit: bool = False,
    allow_search_oracle: bool = False,
    allow_search_oracle_upper_bound: bool = False,
    allow_historical_scalar_cutoff: bool = False,
) -> dict[str, Any] | None:
    """Project strict replayed witness geometry as negative evidence only."""

    audit_attempt = row.get("audit_attempt")
    formal_threshold_rejection = bool(
        formal_audit
        and isinstance(audit_attempt, dict)
        and audit_attempt.get("schema_version") == 2
        and isinstance(audit_attempt.get("evidence"), dict)
        and row.get("threshold_rejection_proven") is True
        and (
            row.get("final_gate_excluded_by_upper_bound") is True
            or row.get("search_final_gate_excluded_by_upper_bound") is True
        )
    )
    oracle = row.get("low_weight_oracle")
    search_oracle_rejection = bool(
        allow_search_oracle
        and row.get("search_status") == "terminal_negative"
        and row.get("threshold_rejection_proven") is True
        and row.get("threshold_proof_source") == "low_weight_oracle"
        and (
            row.get("final_gate_excluded_by_upper_bound") is True
            or row.get("search_final_gate_excluded_by_upper_bound") is True
        )
        and isinstance(oracle, dict)
        and oracle.get("outcome") == "SAT"
    )
    search_oracle_upper_bound = bool(
        allow_search_oracle_upper_bound
        and isinstance(oracle, dict)
        and oracle.get("outcome") == "SAT"
    )
    if not (
        candidate_terminal_negative(row)
        or formal_threshold_rejection
        or search_oracle_rejection
        or search_oracle_upper_bound
    ):
        return None
    witness = (
        oracle.get("witness")
        if search_oracle_rejection or search_oracle_upper_bound
        else None
    )
    if not isinstance(witness, dict):
        witness = row.get("threshold_proof_witness")
    if not isinstance(witness, dict):
        details = row.get("milp_details")
        if isinstance(details, dict):
            witness = details.get("minimum_direction_witness")
    if not isinstance(witness, dict):
        witness = row.get("symplectic_weight_witness")
    if not isinstance(witness, dict):
        return None
    n = row.get("n")
    ell = row.get("ell")
    m = row.get("m")
    k = row.get("k")
    a_terms = row.get("A_terms")
    b_terms = row.get("B_terms")
    compact_construction = _normalized_compact_construction(row)
    # Reject dimensions and degree before touching a potentially huge bit
    # vector or allocating dense BB matrices. Stage 2 evaluates exactly these
    # allow-listed lattices under the challenge's degree-six gate.
    common_dimensions_valid = bool(
        type(n) is int
        and type(k) is int
        and 1 <= k <= n
    )
    bb_dimensions_valid = bool(
        type(ell) is int
        and type(m) is int
        and (ell, m) in _REVIEWABLE_EVOLUTION_LATTICES
        and n == 2 * ell * m
        and isinstance(a_terms, (list, tuple))
        and isinstance(b_terms, (list, tuple))
        and 1 <= len(a_terms) <= 6
        and 1 <= len(b_terms) <= 6
    )
    if not common_dimensions_valid or (
        compact_construction is None and not bb_dimensions_valid
    ):
        return None
    side = witness.get("side")
    weight = witness.get("weight")
    bits = witness.get("bits")
    if (
        side not in {"X", "Z"}
        or type(weight) is not int
        or weight < 1
        or not isinstance(bits, list)
        or len(bits) != n
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != weight
    ):
        return None
    try:
        import numpy as np

        from evaluation.bb_code import build_bb_code, validate_terms
        from evaluation.css_logical_detector import (
            verify_css_logical_detectors,
        )
        from evaluation.distance_milp import get_code_matrices
        from evaluation.evaluator import (
            compute_challenge_rejection_cutoff,
            compute_fom_rejection_cutoff,
        )
        from evaluation.low_weight_oracle import (
            verify_css_low_weight_oracle,
        )

        def strict_terms(value: Any, name: str) -> list[tuple[int, int]]:
            if not isinstance(value, (list, tuple)):
                raise TypeError(f"{name} is not a term sequence")
            normalized: list[tuple[int, int]] = []
            for term in value:
                if (
                    not isinstance(term, (list, tuple))
                    or len(term) != 2
                    or any(type(coordinate) is not int for coordinate in term)
                ):
                    raise TypeError(f"{name} contains an invalid term")
                normalized.append((term[0], term[1]))
            validate_terms(ell, m, normalized, name)
            return normalized

        if compact_construction is not None:
            from evaluation.construction import build_css_code_from_claim

            code = build_css_code_from_claim({
                "construction": compact_construction,
            })
            normalized_a = normalized_b = None
        else:
            normalized_a = strict_terms(a_terms, "A")
            normalized_b = strict_terms(b_terms, "B")
            code = build_bb_code(
                ell,
                m,
                normalized_a,
                normalized_b,
                geometry=row.get("geometry"),
            )
        if int(code.num_qudits) != n or int(code.dimension) != k:
            return None
        hx, hz, lx, lz = get_code_matrices(code)
        detector = verify_css_logical_detectors(hx, hz, lx, lz)
        if detector.get("verified") is not True:
            return None
        if (
            search_oracle_rejection or search_oracle_upper_bound
        ) and verify_css_low_weight_oracle(
            oracle,
            hx,
            hz,
            lx,
            lz,
            # A SAT operator is a self-verifying algebraic upper-bound
            # witness. Preserve its historical source binding so a completed
            # round remains replayable after the oracle implementation is
            # upgraded; do not use this relaxation for positive lower bounds.
            require_current_source=False,
        ):
            return None
        vector = np.asarray(bits, dtype=np.uint8)
        checks, logicals = (hz, lz) if side == "X" else (hx, lx)
        if np.any((checks @ vector) & 1) or not np.any(
            (logicals @ vector) & 1
        ):
            return None
        challenge_cutoff = compute_challenge_rejection_cutoff(n, k, 12.0)
        if not search_oracle_upper_bound and weight > challenge_cutoff:
            scalar_cutoff = compute_fom_rejection_cutoff(n, k, 12.0)
            historical_scalar_contract = bool(
                allow_historical_scalar_cutoff
                and search_oracle_rejection
                and challenge_cutoff < weight <= scalar_cutoff
                and row.get("fom_rejection_cutoff") == scalar_cutoff
                and row.get("challenge_rejection_cutoff") == scalar_cutoff
                and row.get("minimum_winning_distance") == scalar_cutoff + 1
                and row.get("threshold_rejected") is True
                and row.get("threshold_proof_distance") == weight
                and row.get("threshold_proof_witness") == witness
                and row.get("low_weight_witness") == witness
                and row.get("distance_upper_bound") == weight
                and row.get("distance_upper_bound_source")
                == "low_weight_oracle"
                and row.get("fom_target_excluded_by_upper_bound") is True
                and row.get("final_gate_excluded_by_upper_bound") is True
                and row.get("search_final_gate_excluded_by_upper_bound") is True
                and type(oracle.get("max_weight")) is int
                and weight <= oracle["max_weight"] <= scalar_cutoff
            )
            if not historical_scalar_contract:
                return None
    except Exception:
        return None
    support = [index for index, bit in enumerate(bits) if bit]
    block_size = (
        n // 2
        if compact_construction is not None and type(n) is int and n % 2 == 0
        else ell * m
        if type(ell) is int and type(m) is int and ell > 0 and m > 0
        else None
    )
    replayed = {
        "semantics": "negative_upper_bound_witness",
        "side": side,
        "weight": weight,
        "support": support,
        "block_support": [
            {
                "qubit": index,
                "block": (
                    "unknown"
                    if block_size is None
                    else "left" if index < block_size else "right"
                ),
                "offset": (
                    index
                    if block_size is None or index < block_size
                    else index - block_size
                ),
            }
            for index in support
        ],
    }
    if compact_construction is not None:
        replayed["construction"] = compact_construction
        replayed["action_id"] = compact_construction.get("action_id")
        replayed["left_support"] = copy.deepcopy(
            compact_construction.get("left_support")
        )
        replayed["right_support"] = copy.deepcopy(
            compact_construction.get("right_support")
        )
    else:
        replayed.update({
            "ell": ell,
            "m": m,
            "A_terms": copy.deepcopy(row.get("A_terms")),
            "B_terms": copy.deepcopy(row.get("B_terms")),
        })
        geometry = candidate_geometry(row)
        if geometry is not None:
            replayed["geometry"] = geometry
    return replayed


def replay_search_oracle_witness_geometry(
    row: dict[str, Any],
) -> dict[str, Any] | None:
    """Replay one Stage-2 SAT witness for negative-only search feedback.

    This deliberately exposes only the geometry of a concrete logical
    operator after rebuilding the BB code, validating its logical detectors,
    replaying the self-bound oracle evidence, and checking the challenge
    rejection threshold.  It is not a distance lower bound and cannot promote
    a candidate.
    """

    return _negative_witness_geometry(row, allow_search_oracle=True)


def replay_search_oracle_upper_bound_geometry(
    row: dict[str, Any],
) -> dict[str, Any] | None:
    """Replay a Stage-2 SAT witness as a mathematical distance upper bound.

    Unlike :func:`replay_search_oracle_witness_geometry`, this helper does not
    require or trust pre-existing terminal/exclusion flags and does not apply a
    challenge cutoff.  It rebuilds the candidate, replays the self-hashed SAT
    oracle artifact, and independently checks the logical operator.  Callers
    must compare the returned weight with their own target before excluding a
    candidate; this function never supplies positive search credit.
    """

    return _negative_witness_geometry(
        row,
        allow_search_oracle_upper_bound=True,
    )


def replay_historical_scalar_only_search_oracle_witness_geometry(
    row: dict[str, Any],
) -> dict[str, Any] | None:
    """Replay a source-bound old scalar-only terminal marker.

    This is a narrowly scoped migration hook for immutable rounds produced by
    a known historical evaluator.  It performs the same construction, oracle,
    and algebraic witness replay as the normal path; the only relaxation is
    that a valid witness may lie above today's Pareto-aware challenge cutoff
    while remaining below the row's exactly reproduced old scalar cutoff.
    """

    return _negative_witness_geometry(
        row,
        allow_search_oracle=True,
        allow_historical_scalar_cutoff=True,
    )


def _upper_bound_neutral_advisory(
    row: dict[str, Any],
    *,
    formal_audit: bool = False,
    allow_search_oracle: bool = False,
) -> dict[str, Any]:
    """Project an untrusted row without exposing upper-bound reward signals."""
    projected = {
        name: copy.deepcopy(row[name])
        for name in _ADVISORY_ROW_FIELDS
        if name in row
    }
    if "construction" in projected:
        normalized_construction = _normalized_compact_construction(row)
        if normalized_construction is None:
            projected.pop("construction", None)
        else:
            projected["construction"] = normalized_construction
    projected["distance_policy"] = (
        "unresolved upper-bound magnitude withheld; no positive distance "
        "credit"
    )

    details = row.get("milp_details")
    if isinstance(details, dict):
        coverage_fields = (
            "exact",
            "checkpoint_status",
            "total_logicals",
            "num_logicals_checked",
            "logicals_optimal",
            "logicals_incumbent",
            "logicals_timeout",
            "all_timeout",
            "no_incumbent",
        )
        projected["milp_coverage"] = {
            name: copy.deepcopy(details[name])
            for name in coverage_fields
            if name in details
        }

    terminal_negative = candidate_terminal_negative(row)
    if terminal_negative:
        projected["proof_backed_terminal_negative"] = {
            name: copy.deepcopy(row[name])
            for name in (
                "threshold_rejection_proven",
                "threshold_proof_source",
                "threshold_proof_distance",
                "fom_rejection_cutoff",
                "challenge_rejection_cutoff",
                "fom_target_excluded_by_upper_bound",
                "final_gate_excluded_by_upper_bound",
                "search_final_gate_excluded_by_upper_bound",
            )
            if name in row
        }
        witness_geometry = _negative_witness_geometry(
            row,
            formal_audit=formal_audit,
            allow_search_oracle=allow_search_oracle,
        )
        if witness_geometry is not None:
            projected["replayed_low_weight_witness"] = witness_geometry
    elif formal_audit:
        witness_geometry = _negative_witness_geometry(row, formal_audit=True)
        if witness_geometry is not None:
            projected["replayed_low_weight_witness"] = witness_geometry
    elif allow_search_oracle:
        witness_geometry = _negative_witness_geometry(
            row, allow_search_oracle=True
        )
        if witness_geometry is not None:
            projected["replayed_low_weight_witness"] = witness_geometry

    if any(
        name in row
        for name in (
            "distance_lower_bound",
            "distance_lower_bound_proven",
            "distance_lower_bound_status",
            "fom_lower_bound",
        )
    ):
        projected["unverified_lower_bound_claim_withheld"] = True
    return projected


def _trusted_exact_compact(row: dict[str, Any]) -> dict[str, Any]:
    """Return the small, decision-relevant index entry for one exact audit."""
    projected = {
        name: copy.deepcopy(row[name])
        for name in _TRUSTED_EXACT_COMPACT_FIELDS
        if name in row
    }
    if "construction" in projected:
        normalized_construction = _normalized_compact_construction(row)
        if normalized_construction is None:
            projected.pop("construction", None)
        else:
            projected["construction"] = normalized_construction
    return projected


def _round_history_compact(row: dict[str, Any]) -> dict[str, Any]:
    """Project one historical round without replaying untrusted candidates."""
    return {
        name: copy.deepcopy(row[name])
        for name in _ROUND_HISTORY_COMPACT_FIELDS
        if name in row
    }


def build_review_prompt(
    *,
    round_number: int,
    contract: dict[str, Any],
    candidates: list[dict[str, Any]],
    audited: list[dict[str, Any]],
    archive_top: list[dict[str, Any]],
    memory: str,
    trusted_exact_history: list[dict[str, Any]] | None = None,
    trusted_exact_wins: list[dict[str, Any]] | None = None,
    round_history: list[dict[str, Any]] | None = None,
) -> str:
    """Build an evidence-only review prompt with explicit trust boundaries."""
    trusted_exact_history = trusted_exact_history or []
    trusted_exact_wins = trusted_exact_wins or []
    round_history = round_history or []
    memory_excerpt = memory[-_MEMORY_EXCERPT_LIMIT:]
    compact_exact_history = [
        _trusted_exact_compact(row) for row in trusted_exact_history
    ]
    exact_history_details = copy.deepcopy(
        trusted_exact_history[:_TRUSTED_EXACT_DETAILS_LIMIT]
    )
    compact_exact_wins = [
        _trusted_exact_compact(row) for row in trusted_exact_wins
    ]
    compact_round_history = [
        _round_history_compact(row) for row in round_history
    ]
    from evolve.coset_search_contract import (
        COSET_RENDERER_V3_ID,
        trusted_coset_catalog_registry_document,
        trusted_coset_renderer_registry_document,
    )

    renderer_registry = trusted_coset_renderer_registry_document()
    catalog_registry = trusted_coset_catalog_registry_document()
    evidence = {
        "round": round_number,
        "contract": contract,
        "new_candidate_count": len(candidates),
        "new_candidates": [
            _upper_bound_neutral_advisory(
                row, allow_search_oracle=True
            )
            for row in candidates[:20]
        ],
        "milp_audited": [
            _upper_bound_neutral_advisory(row, formal_audit=True)
            for row in audited
        ],
        "archive_top": [
            _upper_bound_neutral_advisory(row)
            for row in archive_top[:20]
        ],
        "upper_bound_neutralization_policy": {
            "bp_osd_distance_and_fom_magnitudes_withheld": True,
            "unreplayed_upper_bounds_cannot_permanently_reject": True,
            "positive_distance_credit_sources": [
                "trusted_exact_history",
            ],
        },
        "trusted_exact_policy": {
            "source": "canonical evaluations.jsonl",
            "classification": "AuditOutcome.EXACT",
            "formal_checkpoint_replay_required": True,
            "challenge_win_rule": "evaluation.final_gate.classify_win",
            "authoritative_construction_rebuild_required": True,
            "explicit_known_code_registry_replay_required": True,
            "registry_novel_true_required_for_stop": True,
        },
        "trusted_exact_history": compact_exact_history,
        "trusted_exact_history_details": exact_history_details,
        "trusted_exact_history_coverage": {
            "total": len(trusted_exact_history),
            "compact_index_included": len(compact_exact_history),
            "compact_index_omitted": 0,
            "details_included": len(exact_history_details),
            "details_omitted": len(trusted_exact_history)
            - len(exact_history_details),
            "details_selection": "input_order_first_20",
        },
        "trusted_exact_wins": compact_exact_wins,
        "trusted_exact_wins_coverage": {
            "total": len(trusted_exact_wins),
            "compact_index_included": len(compact_exact_wins),
            "compact_index_omitted": 0,
        },
        "round_history": compact_round_history,
        "round_history_coverage": {
            "total": len(round_history),
            "compact_index_included": len(compact_round_history),
            "compact_index_omitted": 0,
        },
        "trusted_coset_renderer_registry": {
            "advisory_only": True,
            "renderer_registry_sha256": renderer_registry[
                "registry_sha256"
            ],
            # The registry also retains historical renderer descriptors for
            # artifact replay.  Only v3 has an installed next-round activation
            # handler, so advertising v2 here would invite a proposal that the
            # controller is required to reject.
            "activatable_renderers": [
                {
                    "renderer_descriptor_id": row["descriptor_id"],
                    "catalog_kind": row["catalog_kind"],
                    "support_splits": row["support_splits"],
                }
                for row in renderer_registry["descriptors"]
                if row["descriptor_id"] == COSET_RENDERER_V3_ID
            ],
            "catalog_registry_sha256": catalog_registry["registry_sha256"],
            "installed_catalog_manifests": [
                {
                    "catalog_manifest_id": row["manifest_id"],
                    "catalog_kind": row["catalog_kind"],
                    "catalog_id": row["catalog_id"],
                }
                for row in catalog_registry["manifests"]
            ],
            "unknown_catalog_behavior": (
                "sealed_non_executable_advisory_continue_trusted_renderer"
            ),
        },
        "memory_coverage": {
            "total_characters": len(memory),
            "included_characters": len(memory_excerpt),
            "omitted_characters": len(memory) - len(memory_excerpt),
            "selection": "most_recent_12000_characters",
        },
    }
    return f"""You are the independent reviewer in a Humanize-style RLCR loop for
quantum error-correcting code discovery. Review the round evidence below. You
did not generate these candidates and must remain skeptical.

Trust boundary:
- Python rank calculations can propose k but do not constitute a Lean proof.
- BP-OSD returns an upper bound on distance, never a lower bound or exact d.
- A MILP result is exact only when every logical direction was solved to proven
  optimality and milp_details.exact is true.
- Only trusted_exact_history was independently replayed from the canonical
  audit log. trusted_exact_wins is the subset that also passes a construction
  rebuild and explicit known-code registry replay with novel=true.
- trusted_exact_history is the complete compact index, never a top-N sample.
  trusted_exact_history_details may be bounded, and its explicit coverage
  object states exactly how many detail rows were included or omitted.
- round_history is the complete compact index of prior-round aggregate
  evidence. It never grants positive distance credit to unresolved rows.
- archive_top, new_candidates, and milp_audited are upper-bound-neutral
  projections: unresolved BP/OSD d and FOM magnitudes are deliberately absent.
- A replayable low-weight witness may be used only as negative evidence.
- Positive distance credit requires trusted exact history or a formally
  certified lower bound; survival under BP/OSD is not such a bound.
- Your review cannot upgrade any numerical claim. Only MILP certificates and
  later Lean compilation can do so.
- Flag stale or physically implausible FOM claims, duplicated candidates,
  partial MILP coverage, and selection bias.

Verdicts:
- continue: search another round with the recommended focus.
- promote: the audited set is worth sending to Lean now; search may continue.
- stop: recommend stopping; the controller will honor this only when
  trusted_exact_wins is non-empty.
- reject_round: evidence is corrupt or misleading; do not learn from it.

Search-action contract:
- Emit schema_version=2 and a search_action with schema_version=1.
- search_action is advisory_only=true. It may recommend only an allowlisted
  search intent and focus value for the next 1-3 rounds.
- It cannot change stop rules, budgets, proof thresholds, stage ordering,
  worker limits, or machine-owned state, and must not contain any reserved
  QCODE_ marker.
- Cite concrete evidence_refs. Use round_history when recommending a regime
  change; do not infer a trend from a single round.
- For a coset renderer request, emit exactly one support_split_type focus.
  The current installed action catalog can be selected implicitly, or name a
  renderer_descriptor_id, catalog_manifest_id, and catalog_kind together.
  These are inert registry IDs, never module/callable names. Unknown action,
  cover, or protograph IDs produce a sealed non-executable advisory. They never
  install or execute a new mathematical construction, never stop the machine
  search, and the next round continues with the source-owned trusted renderer.

Long-term BitLesson memory (may be empty):
---
{memory_excerpt}
---

Round evidence JSON:
{json.dumps(evidence, ensure_ascii=False, indent=2, default=str)}

Return only the JSON object required by the supplied output schema. Lessons
must be evidence-backed and reusable; omit speculative lessons.
"""


class CodexReviewer:
    """Invoke a fresh Codex session as the independent round reviewer."""

    def __init__(
        self,
        *,
        repo_dir: Path,
        model: str,
        effort: str,
        timeout: int = 5400,
        codex_bin: str = "codex",
        max_attempts: int = 3,
        retry_backoff_seconds: float = 1.0,
        sleeper: Callable[[float], None] = time.sleep,
    ):
        if max_attempts < 1:
            raise ValueError("max_attempts must be at least 1")
        if retry_backoff_seconds < 0:
            raise ValueError("retry_backoff_seconds must be non-negative")
        self.repo_dir = repo_dir
        self.model = model
        self.effort = effort
        self.timeout = timeout
        self.codex_bin = codex_bin
        self.max_attempts = max_attempts
        self.retry_backoff_seconds = retry_backoff_seconds
        self.sleeper = sleeper

    def review(self, prompt: str, round_dir: Path) -> dict[str, Any]:
        schema_path = round_dir / "review-schema.json"
        output_path = round_dir / "review.json"
        schema_path.write_text(json.dumps(REVIEW_SCHEMA, indent=2) + "\n")
        command = [
            self.codex_bin,
            "exec",
            "--model", self.model,
            "--config", f'model_reasoning_effort="{self.effort}"',
            "--sandbox", "read-only",
            "--ephemeral",
            "--cd", str(self.repo_dir),
            "--output-schema", str(schema_path),
            "--output-last-message", str(output_path),
            "-",
        ]
        failures: list[ReviewError] = []
        log_paths: list[Path] = []
        for attempt in range(1, self.max_attempts + 1):
            log_path = round_dir / f"review-attempt-{attempt:02d}.log"
            log_paths.append(log_path)
            try:
                with log_path.open("w", encoding="utf-8") as log_stream:
                    log_stream.write(
                        f"[review-attempt] attempt={attempt}/{self.max_attempts} "
                        f"model={self.model} effort={self.effort} "
                        f"timeout_seconds={self.timeout}\n"
                    )
                    log_stream.flush()
                    try:
                        output_path.unlink(missing_ok=True)
                        subprocess.run(
                            command,
                            input=prompt,
                            text=True,
                            stdout=log_stream,
                            stderr=subprocess.STDOUT,
                            timeout=self.timeout,
                            check=True,
                        )
                    except (
                        subprocess.CalledProcessError,
                        subprocess.TimeoutExpired,
                        OSError,
                    ) as exc:
                        raise ReviewError(
                            "independent Codex review process failed "
                            f"on attempt {attempt}/{self.max_attempts}; "
                            f"{type(exc).__name__}: {exc}; "
                            f"see {log_path}"
                        ) from exc

                    if not output_path.is_file():
                        raise ReviewError(
                            "independent Codex review produced no output "
                            f"on attempt {attempt}/{self.max_attempts}; "
                            f"see {log_path}"
                        )
                    try:
                        value = json.loads(output_path.read_text())
                    except (json.JSONDecodeError, OSError) as exc:
                        raise ReviewError(
                            "independent review output was not valid JSON "
                            f"on attempt {attempt}/{self.max_attempts}: "
                            f"{output_path}; see {log_path}"
                        ) from exc
                    try:
                        validated = validate_review(value, require_current=True)
                    except ReviewError as exc:
                        raise ReviewError(
                            "independent review output violated its schema "
                            f"on attempt {attempt}/{self.max_attempts}: {exc}; "
                            f"see {log_path}"
                        ) from exc
                    log_stream.write("\n[review-attempt] status=success\n")
                    return validated
            except ReviewError as exc:
                failures.append(exc)
                try:
                    with log_path.open("a", encoding="utf-8") as log_stream:
                        log_stream.write(f"\n[review-attempt] failure={exc}\n")
                except OSError:
                    pass

            if attempt < self.max_attempts:
                delay = self.retry_backoff_seconds * (2 ** (attempt - 1))
                self.sleeper(delay)

        logs = ", ".join(str(path) for path in log_paths)
        raise ReviewError(
            "independent Codex review failed after "
            f"{self.max_attempts} attempts; see attempt logs: {logs}"
        ) from failures[-1]
