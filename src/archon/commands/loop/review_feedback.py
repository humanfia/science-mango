"""Answer-safe Review history and repair hand-offs.

Review certificates intentionally retain rich free-form evidence for controller
auditing.  That evidence must not be copied back into answer-blind model prompts:
it may contain a derived result, an expected value, or other answer-bearing text.
This module projects durable gate records onto a small controller-owned schema
containing only validated enum values, indices, counters, and content hashes.
"""

from __future__ import annotations

import math
import re
from collections.abc import Mapping
from typing import Any


FEEDBACK_SCHEMA_VERSION = 1
_MAX_EVENTS = 20
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_SAFE_INDEXED_CHECK_RE = re.compile(
    r"^(?P<group>requested_outputs|bridge_obligations|image_audit)"
    r"\[(?:0|[1-9][0-9]?)\]$"
)
_SAFE_REQUIRED_CHECK_IDS = {
    "requested_outputs.required", "bridge_obligations.required", "image_audit.required",
}

_SAFE_STATUSES = {
    "blocked",
    "blocked_infrastructure",
    "error",
    "failed",
    "invalid",
    "missing",
    "needs_redraft",
    "not_applicable",
    "passed",
    "proof_review_exhausted",
    "retry",
    "review_exhausted",
    "solved",
    "timeout",
}
_STATUS_ALIASES = {
    "approved": "passed",
    "closed": "passed",
    "compiles": "passed",
    "complete": "passed",
    "completed": "passed",
    "fail": "failed",
    "partial": "failed",
    "pass": "passed",
    "review_passing": "passed",
    "success": "passed",
    "unresolved": "failed",
}
_CHECK_PASS_STATUSES = {
    "aligned", "approved", "covered", "encoded", "grounded", "pass",
    "passed", "proved", "resolved", "review_passing", "success", "verified",
}
_CHECK_FAIL_STATUSES = {
    "blocked", "conflict", "error", "fail", "failed", "invalid", "missing",
    "needs_redraft", "not_started", "partial", "rejected", "timeout",
    "unresolved",
}
_CHECK_NOT_APPLICABLE_STATUSES = {"n/a", "na", "not_applicable"}
_FAILED_STATUSES = {"failed", "invalid", "missing"}
_TRANSITIONS = {"formalization_redraft_passed"}
_PROOF_ROUTES = {
    "blocked_infrastructure", "needs_redraft", "retry_proof", "solved",
}
_REDRAFT_KINDS = {
    "answer_as_assumption",
    "branch_ambiguous",
    "missing_foundational_bridge",
    "missing_uncertainty",
    "not_applicable",
    "other_modeling_defect",
    "underdetermined_contract",
    "wrong_or_weakened_target",
}

_CHECK_GROUPS: dict[str, tuple[str, ...]] = {
    "independent_source_audit": (
        "requested_outputs",
        "official_answer",
        "image_grounding",
        "domain_invariants",
        "reporting_convention",
        "adversarial_counterexample",
    ),
    "blind_source_audit": (
        "answer_independence",
        "raw_derivation",
        "reporting_rule_source",
        "tolerance_provenance",
        "candidate_domain_provenance",
        "lean_result_binding",
    ),
    "contract_audit": (
        "statement_scope",
        "hypothesis_derivability",
        "conclusion_alignment",
        "bridge_completeness",
    ),
    "chemistry_checks": (
        "chemical_semantics",
        "formula_mass_consistency",
        "conservation_laws",
        "units_dimensions",
        "numerical_reporting",
        "structure_stereochemistry",
        "identification_uniqueness",
        "answer_smuggling",
    ),
    "checks": (
        "source_faithfulness",
        "derivability",
        "abstraction_sufficiency",
        "uncertainty_propagation",
        "branch_orientation",
        "countermodel_resistance",
    ),
}
_REQUIRED_GROUPS = {
    "proof": (
        "blind_source_audit", "contract_audit", "chemistry_checks",
    ),
    "formalization": (
        "checks",
        "independent_source_audit",
        "contract_audit",
        "chemistry_checks",
    ),
}


_REDRAFT_ACTIONS = {
    "answer_as_assumption": "remove_answer_shaped_assumptions",
    "branch_ambiguous": "encode_and_justify_the_selected_branch",
    "missing_foundational_bridge": "add_explicit_source_to_model_bridges",
    "missing_uncertainty": "encode_required_uncertainty_propagation",
    "other_modeling_defect": "repair_the_model_contract",
    "underdetermined_contract": "represent_missing_degrees_of_freedom_honestly",
    "wrong_or_weakened_target": "restore_every_requested_output_and_constraint",
}


def _token(value: Any, allowed: set[str]) -> str:
    token = str(value or "").strip().lower().replace("-", "_").replace(" ", "_")
    return token if token in allowed else ""


def _status_token(value: Any) -> str:
    token = str(value or "").strip().lower().replace("-", "_").replace(" ", "_")
    if not token:
        return ""
    token = _STATUS_ALIASES.get(token, token)
    return token if token in _SAFE_STATUSES else "invalid"


def _check_status_token(value: Any) -> str:
    token = str(value or "").strip().lower().replace("-", "_").replace(" ", "_")
    if not token:
        return "missing"
    if token in _CHECK_PASS_STATUSES:
        return "passed"
    if token in _CHECK_FAIL_STATUSES:
        return "failed"
    if token in _CHECK_NOT_APPLICABLE_STATUSES:
        return "not_applicable"
    return "invalid"


def _safe_check_id(value: Any, *, review_kind: str) -> str:
    if not isinstance(value, str):
        return ""
    allowed_groups = {
        "blind_source_audit",
        "independent_source_audit",
        "contract_audit",
        "chemistry_checks",
    }
    if review_kind == "formalization":
        allowed_groups.add("checks")
    allowed = {
        f"{group}.{name}"
        for group, names in _CHECK_GROUPS.items()
        if group in allowed_groups
        for name in names
    }
    if value in allowed:
        return value
    if value in _SAFE_REQUIRED_CHECK_IDS:
        if value.startswith("bridge_obligations") and review_kind != "formalization":
            return ""
        return value
    indexed = _SAFE_INDEXED_CHECK_RE.fullmatch(value)
    if indexed is None:
        return ""
    if (
        indexed.group("group") == "bridge_obligations"
        and review_kind != "formalization"
    ):
        return ""
    return value



def _bounded_int(value: Any, *, minimum: int = 0, maximum: int = 1_000_000) -> int | None:
    if isinstance(value, bool):
        return None
    try:
        result = int(value)
    except (TypeError, ValueError):
        return None
    return result if minimum <= result <= maximum else None


def _normalize_sha256(value: Any, *, field: str) -> str:
    digest = str(value or "").strip().lower()
    if not digest:
        return ""
    if not _SHA256_RE.fullmatch(digest):
        raise ValueError(f"{field} must be a lowercase SHA-256 digest")
    return digest


def _record_candidate_sha256(record: Mapping[str, Any]) -> str:
    return _normalize_sha256(
        record.get("candidate_sha256"), field="candidate_sha256"
    )


def _candidate_sha256(record: Mapping[str, Any], explicit: str = "") -> str:
    current = _normalize_sha256(explicit, field="candidate_sha256")
    stored = _record_candidate_sha256(record)
    if current and stored and current != stored:
        raise ValueError("repair feedback candidate SHA-256 does not match gate record")
    return current or stored


def _certificate(record: Mapping[str, Any], review_kind: str) -> Mapping[str, Any]:
    if review_kind == "proof":
        value = record.get("blind_review_certificate")
    else:
        value = record.get("certificate")
    return value if isinstance(value, Mapping) else {}


def _safe_check_statuses(
    certificate: Mapping[str, Any],
    *,
    review_kind: str,
) -> dict[str, str]:
    statuses: dict[str, str] = {}
    nested_blind = certificate.get("blind_review_certificate")
    sources = [certificate]
    if isinstance(nested_blind, Mapping):
        sources.append(nested_blind)
    required_groups = list(_REQUIRED_GROUPS[review_kind])
    if review_kind == "formalization" and any(
        isinstance(source.get("blind_source_audit"), Mapping)
        for source in sources
    ):
        required_groups[
            required_groups.index("independent_source_audit")
        ] = "blind_source_audit"
    for group in required_groups:
        names = _CHECK_GROUPS[group]
        raw_group = None
        for source in sources:
            candidate = source.get(group)
            if isinstance(candidate, Mapping):
                raw_group = candidate
                break
        if not isinstance(raw_group, Mapping):
            for name in names:
                statuses[f"{group}.{name}"] = "missing"
            continue
        for name in names:
            raw_check = raw_group.get(name)
            if not isinstance(raw_check, Mapping):
                statuses[f"{group}.{name}"] = "missing"
                continue
            status = _check_status_token(raw_check.get("status"))
            allow_na = group == "chemistry_checks" or (
                group == "checks"
                and name in {"uncertainty_propagation", "branch_orientation"}
            )
            if status == "not_applicable" and not allow_na:
                status = "invalid"
            if not str(
                raw_check.get("evidence") or raw_check.get("reason") or ""
            ).strip():
                status = "invalid"
            statuses[f"{group}.{name}"] = status

    for source in sources:
        for list_name, status_key, success in (
            ("requested_outputs", "status", {"covered", "passed"}),
            ("bridge_obligations", "status", {"covered", "passed"}),
        ):
            values = source.get(list_name)
            if not isinstance(values, list):
                continue
            for index, item in enumerate(values[:100]):
                check_id = f"{list_name}[{index}]"
                if not isinstance(item, Mapping):
                    statuses[check_id] = "invalid"
                    continue
                status = _check_status_token(item.get(status_key))
                if list_name == "requested_outputs" and (
                    str(item.get("submission_status") or "")
                    .strip()
                    .lower()
                    != "matched"
                    or str(item.get("reporting_policy_status") or "")
                    .strip()
                    .lower()
                    != "matched"
                ):
                    status = "failed"
                if (
                    list_name == "requested_outputs"
                    and "composition_accounting" in item
                ):
                    composition = item.get("composition_accounting")
                    if (
                        not isinstance(composition, Mapping)
                        or str(composition.get("status") or "")
                        .strip()
                        .lower()
                        != "matched"
                    ):
                        status = "failed"
                if status != "passed":
                    statuses[check_id] = status
        images = source.get("image_audit")
        if isinstance(images, list):
            for index, item in enumerate(images[:100]):
                check_id = f"image_audit[{index}]"
                if not isinstance(item, Mapping):
                    statuses[check_id] = "invalid"
                elif item.get("inspected") is not True:
                    statuses[check_id] = "failed"
    return dict(sorted(statuses.items()))


def failed_check_ids(
    certificate: Mapping[str, Any],
    *,
    review_kind: str,
) -> list[str]:
    """Return answer-free identifiers for checks that did not pass."""
    return [
        check_id
        for check_id, status in _safe_check_statuses(
            certificate,
            review_kind=review_kind,
        ).items()
        if status in _FAILED_STATUSES
    ]


def safe_preflight_summary(preflight: Mapping[str, Any] | None) -> dict[str, Any]:
    """Project deterministic preflight data without diagnostics or source text."""
    if not isinstance(preflight, Mapping) or not preflight:
        return {}
    status = _status_token(preflight.get("status"))
    if not status:
        return {}
    if status not in {"passed", "failed", "timeout", "error", "missing", "invalid"}:
        status = "invalid"
    result: dict[str, Any] = {"status": status}
    compiles = preflight.get("compiles")
    if isinstance(preflight.get("compiles"), bool):
        result["compiles"] = compiles
    if "returncode" in preflight:
        returncode = preflight.get("returncode")
        if returncode is None:
            result["returncode"] = None
        else:
            parsed = _bounded_int(returncode, minimum=-255, maximum=255)
            if parsed is not None:
                result["returncode"] = parsed
    sorry_count = _bounded_int(preflight.get("sorry_count"), maximum=100_000)
    if sorry_count is not None:
        result["sorry_count"] = sorry_count
    if status == "passed" and (
        compiles is not True or result.get("returncode") != 0
    ):
        result["status"] = "invalid"
    elif status in {"failed", "timeout", "error", "missing"} and compiles is True:
        result["status"] = "invalid"
    duration = preflight.get("duration_secs")
    if isinstance(duration, (int, float)) and not isinstance(duration, bool):
        duration = float(duration)
        if math.isfinite(duration) and 0.0 <= duration <= 86_400.0:
            if duration < 60:
                bucket = "under_1m"
            elif duration < 300:
                bucket = "1_to_5m"
            elif duration < 900:
                bucket = "5_to_15m"
            elif duration < 3600:
                bucket = "15_to_60m"
            else:
                bucket = "at_least_60m"
            result["duration_bucket"] = bucket
    return result


def build_feedback_event(
    *,
    review_kind: str,
    candidate_sha256: str,
    event_id: str,
    iteration: int,
    attempt: int,
    resulting_status: str,
    certificate: Mapping[str, Any] | None,
    route: str = "",
    decision: str = "",
    redraft_kind: str = "",
    transition: str = "",
    preflight: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Create a controller-owned, answer-free durable Review event."""
    if review_kind not in {"proof", "formalization"}:
        raise ValueError(f"unsupported review kind: {review_kind}")
    digest = _normalize_sha256(candidate_sha256, field="candidate_sha256")
    if not digest:
        raise ValueError("feedback event requires a candidate SHA-256")
    event: dict[str, Any] = {
        "schema_version": FEEDBACK_SCHEMA_VERSION,
        "review_kind": review_kind,
        "candidate_sha256": digest,
        "iteration": max(0, int(iteration)),
        "attempt": max(0, int(attempt)),
        "resulting_status": _status_token(resulting_status) or "invalid",
        "failed_check_ids": failed_check_ids(
            certificate if isinstance(certificate, Mapping) else {},
            review_kind=review_kind,
        ),
    }
    safe_event_id = str(event_id or "").strip()
    if safe_event_id and len(safe_event_id) <= 240 and all(
        char.isalnum() or char in "-_:/." for char in safe_event_id
    ):
        event["event_id"] = safe_event_id
    safe_transition = _token(transition, _TRANSITIONS)
    if safe_transition:
        event["transition"] = safe_transition
        event["failed_check_ids"] = []
    if review_kind == "proof":
        event["route"] = _token(route, _PROOF_ROUTES) or "retry_proof"
        event["redraft_kind"] = (
            _token(redraft_kind, _REDRAFT_KINDS) or "not_applicable"
        )
    else:
        event["decision"] = _token(decision, {"failed", "passed"}) or "failed"
    preflight_summary = safe_preflight_summary(preflight)
    if preflight_summary:
        event["preflight"] = preflight_summary
    return event


def _safe_feedback_event(value: Any, review_kind: str) -> dict[str, Any] | None:
    if not isinstance(value, Mapping):
        return None
    if value.get("schema_version") != FEEDBACK_SCHEMA_VERSION:
        return None
    if value.get("review_kind") != review_kind:
        return None
    digest = str(value.get("candidate_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        return None
    event: dict[str, Any] = {
        "schema_version": FEEDBACK_SCHEMA_VERSION,
        "review_kind": review_kind,
        "candidate_sha256": digest,
    }
    for key in ("iteration", "attempt"):
        parsed = _bounded_int(value.get(key))
        if parsed is not None:
            event[key] = parsed
    status = _status_token(value.get("resulting_status"))
    if status:
        event["resulting_status"] = status
    transition = _token(value.get("transition"), _TRANSITIONS)
    if transition:
        event["transition"] = transition
    if review_kind == "proof":
        route = _token(value.get("route"), _PROOF_ROUTES)
        if route:
            event["route"] = route
        redraft_kind = _token(value.get("redraft_kind"), _REDRAFT_KINDS)
        if redraft_kind:
            event["redraft_kind"] = redraft_kind
    else:
        decision = _token(value.get("decision"), {"failed", "passed"})
        if decision:
            event["decision"] = decision
    failed = value.get("failed_check_ids")
    if isinstance(failed, list):
        safe_failed = {
            _safe_check_id(item, review_kind=review_kind)
            for item in failed[:100]
        }
        event["failed_check_ids"] = sorted(
            item for item in safe_failed if item
        )
    preflight = safe_preflight_summary(
        value.get("preflight") if isinstance(value.get("preflight"), Mapping) else None
    )
    if preflight:
        event["preflight"] = preflight
    return event


def sanitized_review_history(
    record: Mapping[str, Any] | None,
    *,
    review_kind: str,
) -> dict[str, Any]:
    """Return prior Review events without any free-form Review text."""
    if review_kind not in {"proof", "formalization"}:
        raise ValueError(f"unsupported review kind: {review_kind}")
    if not isinstance(record, Mapping):
        return {
            "schema_version": FEEDBACK_SCHEMA_VERSION,
            "review_kind": review_kind,
            "events": [],
        }
    events: list[dict[str, Any]] = []
    raw_events = record.get("repair_events")
    if isinstance(raw_events, list):
        for raw_event in raw_events[-_MAX_EVENTS:]:
            event = _safe_feedback_event(raw_event, review_kind)
            if event is not None:
                events.append(event)

    # Older gates have no candidate-bound repair_events.  Preserve only their
    # controller-normalized routing metadata; never copy reason/evidence.
    if not events:
        legacy_key = "history" if review_kind == "proof" else "review_events"
        legacy = record.get(legacy_key)
        if isinstance(legacy, list):
            for raw in legacy[-_MAX_EVENTS:]:
                if not isinstance(raw, Mapping):
                    continue
                event: dict[str, Any] = {"legacy_unbound": True}
                for key in ("iter", "attempt"):
                    parsed = _bounded_int(raw.get(key))
                    if parsed is not None:
                        event["iteration" if key == "iter" else key] = parsed
                transition = _token(raw.get("event"), _TRANSITIONS)
                if transition:
                    event["transition"] = transition
                if review_kind == "proof":
                    route = _token(raw.get("route"), _PROOF_ROUTES)
                    if route:
                        event["route"] = route
                    redraft = _token(raw.get("redraft_kind"), _REDRAFT_KINDS)
                    if redraft:
                        event["redraft_kind"] = redraft
                else:
                    decision = _token(raw.get("decision"), {"failed", "passed"})
                    if decision:
                        event["decision"] = decision
                resulting = _status_token(raw.get("resulting_status"))
                if resulting:
                    event["resulting_status"] = resulting
                if len(event) > 1:
                    events.append(event)

    summary: dict[str, Any] = {
        "schema_version": FEEDBACK_SCHEMA_VERSION,
        "review_kind": review_kind,
        "events": events[-_MAX_EVENTS:],
    }
    status = _status_token(record.get("status"))
    if status:
        summary["current_status"] = status
    count_key = "attempts" if review_kind == "proof" else "reviews"
    count = _bounded_int(record.get(count_key))
    if count is not None:
        summary[count_key] = count
    if review_kind == "proof":
        route = _token(record.get("proof_review_route"), _PROOF_ROUTES)
        if route:
            summary["current_route"] = route
        redraft = _token(record.get("redraft_kind"), _REDRAFT_KINDS)
        if redraft:
            summary["current_redraft_kind"] = redraft
    else:
        reopened_by = _token(
            record.get("reopened_by"),
            {"proof_review", "source_contract_freshness"},
        )
        if reopened_by:
            summary["reopened_by"] = reopened_by
        redraft = _token(record.get("redraft_kind"), _REDRAFT_KINDS)
        if redraft:
            summary["current_redraft_kind"] = redraft
    return summary


def build_repair_task(
    record: Mapping[str, Any] | None,
    *,
    review_kind: str,
    worker_stage: str,
    candidate_sha256: str = "",
    preflight: Mapping[str, Any] | None = None,
    discard_stale_record: bool = False,
) -> dict[str, Any]:
    """Build the answer-safe feedback shown to the next repair worker."""
    if review_kind not in {"proof", "formalization"}:
        raise ValueError(f"unsupported review kind: {review_kind}")
    if worker_stage not in {"proof", "formalization"}:
        raise ValueError(f"unsupported repair stage: {worker_stage}")
    record = record if isinstance(record, Mapping) else {}
    try:
        digest = _candidate_sha256(record, candidate_sha256)
    except ValueError as exc:
        if (
            discard_stale_record
            and str(exc)
            == "repair feedback candidate SHA-256 does not match gate record"
        ):
            return {}
        raise
    if not digest:
        raise ValueError("repair feedback requires a current candidate SHA-256")
    history = sanitized_review_history(record, review_kind=review_kind)
    events = history.get("events")
    bound_events = [
        event for event in events
        if isinstance(event, Mapping)
        and event.get("candidate_sha256") == digest
    ] if isinstance(events, list) else []
    latest = bound_events[-1] if bound_events else {}
    record_bound = _record_candidate_sha256(record) == digest
    event_preflight = (
        latest.get("preflight") if isinstance(latest, Mapping) else None
    )
    preflight_source = (
        preflight
        if isinstance(preflight, Mapping)
        else event_preflight
    )
    safe_preflight = safe_preflight_summary(
        preflight_source if isinstance(preflight_source, Mapping) else None
    )
    failed = []
    raw_failed = latest.get("failed_check_ids", [])
    if isinstance(raw_failed, list):
        for item in raw_failed[:100]:
            safe_id = _safe_check_id(item, review_kind=review_kind)
            if safe_id:
                failed.append(safe_id)
    if not failed and record_bound:
        failed = failed_check_ids(
            _certificate(record, review_kind),
            review_kind=review_kind,
        )

    route = ""
    redraft = ""
    transition = _token(latest.get("transition"), _TRANSITIONS)
    if review_kind == "proof" and not transition:
        route = _token(latest.get("route"), _PROOF_ROUTES)
        if not route and record_bound:
            route = _token(record.get("proof_review_route"), _PROOF_ROUTES)
        redraft = _token(latest.get("redraft_kind"), _REDRAFT_KINDS)
        if not redraft and record_bound:
            redraft = _token(record.get("redraft_kind"), _REDRAFT_KINDS)

    reason_codes: list[str] = []
    actions: list[str] = []
    decision = _token(latest.get("decision"), {"failed", "passed"})
    resulting_status = _status_token(latest.get("resulting_status"))
    if not resulting_status and record_bound:
        resulting_status = _status_token(record.get("status"))
    record_status = _status_token(record.get("status")) if record_bound else ""
    terminal_success = (
        (review_kind == "proof" and (
            route == "solved" or resulting_status in {"solved", "passed"}
        ))
        or (review_kind == "formalization" and (
            decision == "passed" or resulting_status in {"solved", "passed"}
        ))
    )
    if terminal_success or record_status in {"solved", "passed"} or resulting_status in {
        "proof_review_exhausted", "review_exhausted", "blocked_infrastructure",
    }:
        return {}
    proof_review_repair = (
        (route == "retry_proof" and resulting_status == "retry")
        or (route == "needs_redraft" and resulting_status == "needs_redraft")
    )
    review_repair = proof_review_repair or (
        review_kind == "formalization"
        and decision == "failed"
        and resulting_status == "retry"
    )
    if route in {"retry_proof", "needs_redraft"}:
        reason_codes.append(route)
    elif review_repair:
        reason_codes.append("formalization_review_failed")
    if review_repair and redraft and redraft != "not_applicable":
        reason_codes.append(redraft)
        action = _REDRAFT_ACTIONS.get(redraft)
        if action:
            actions.append(action)
    preflight_status = safe_preflight.get("status")
    preflight_repair = False
    if preflight_status == "timeout":
        preflight_repair = True
        reason_codes.append("deterministic_preflight_timeout")
        actions.append("reduce_elaboration_and_kernel_checking_cost")
    elif preflight_status == "failed":
        preflight_repair = True
        reason_codes.append("deterministic_preflight_not_compiling")
        actions.append("make_the_current_candidate_compile")
    elif preflight_status in {"error", "missing", "invalid"}:
        preflight_repair = True
        reason_codes.append("deterministic_preflight_unavailable")
        actions.append("rerun_deterministic_preflight")
    if (safe_preflight.get("sorry_count") or 0) > 0:
        preflight_repair = True
        reason_codes.append("open_proof_holes")
        actions.append("close_all_open_proof_holes")
    if failed and review_repair:
        reason_codes.append("failed_structured_checks")

    meaningful = review_repair or preflight_repair
    if not meaningful:
        return {}
    if worker_stage == "proof":
        actions.extend((
            "preserve_the_accepted_statement",
            "finish_kernel_checked_proof",
        ))
    else:
        actions.append("repair_the_statement_or_model_then_revalidate")
    task: dict[str, Any] = {
        "schema_version": FEEDBACK_SCHEMA_VERSION,
        "kind": "controller_sanitized_review_repair",
        "review_kind": review_kind,
        "worker_stage": worker_stage,
        "candidate_sha256": digest,
        "reason_codes": list(dict.fromkeys(reason_codes)),
        "failed_check_ids": sorted(set(failed)),
        "required_actions": list(dict.fromkeys(actions)),
        "history": {**history, "events": bound_events[-_MAX_EVENTS:]},
    }
    if safe_preflight:
        task["preflight"] = safe_preflight
    return task
