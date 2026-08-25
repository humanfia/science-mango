"""Controller-only activation of dormant, source-pinned bridge rules.

Formalization Reviewers may name one exact dormant rule for one blocked bridge.
They never supply the rule text, source, URL, or digest.  This module resolves
the name through the packaged empirical registry, revalidates every binding,
and returns a target- and candidate-bound receipt for the next redraft only.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from pathlib import PurePosixPath
from typing import Any

from archon.commands import chemistry_constant

from .problem_only_review_contract import (
    is_native_problem_only_contract,
    validate_native_review_source_certificate,
)


ACTIVATION_SCHEMA_VERSION = 1
REQUEST_FIELD = "trusted_bridge_requests"
DORMANT_RUNTIME_BRIDGE_IDS = chemistry_constant.DORMANT_RUNTIME_BRIDGE_IDS

_REQUEST_FIELDS = frozenset({"bridge_obligation_index", "rule_id"})
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", flags=re.ASCII)
_RULE_ID_RE = re.compile(r"^[a-z][a-z0-9_]{2,95}$", flags=re.ASCII)
_BLOCKED_BRIDGE_STATUSES = {"blocked"}
_FAILED_REVIEW_STATUS = "failed"
_SOURCE_BINDING_HASH_FIELDS = (
    "source_bundle_sha256",
    "source_record_sha256",
    "answer_submission_sha256",
    "question_sha256",
    "requested_outputs_sha256",
)


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _status(value: object) -> str:
    return str(value or "").strip().lower().replace("-", "_").replace(" ", "_")


def _safe_target_rel(value: object) -> str:
    if not isinstance(value, str) or not value or len(value) > 500:
        return ""
    path = PurePosixPath(value)
    if path.is_absolute() or path.suffix != ".lean" or ".." in path.parts:
        return ""
    normalized = path.as_posix().lstrip("./")
    return normalized if normalized == value.lstrip("./") else ""


def _requests(certificate: Mapping[str, Any]) -> list[dict[str, object]] | None:
    """Return a strict request projection, or ``None`` when malformed."""
    raw = certificate.get(REQUEST_FIELD)
    if raw is None:
        return []
    if not isinstance(raw, list) or len(raw) > len(DORMANT_RUNTIME_BRIDGE_IDS):
        return None
    bridges = certificate.get("bridge_obligations")
    if not isinstance(bridges, list):
        return None
    if raw and _status(certificate.get("status")) != _FAILED_REVIEW_STATUS:
        return None

    requests: list[dict[str, object]] = []
    seen_indices: set[int] = set()
    seen_rules: set[str] = set()
    for item in raw:
        if not isinstance(item, Mapping) or set(item) != _REQUEST_FIELDS:
            return None
        index = item.get("bridge_obligation_index")
        rule_id = item.get("rule_id")
        if (
            type(index) is not int
            or not 0 <= index < len(bridges)
            or not isinstance(rule_id, str)
            or _RULE_ID_RE.fullmatch(rule_id) is None
            or rule_id not in DORMANT_RUNTIME_BRIDGE_IDS
            or index in seen_indices
            or rule_id in seen_rules
        ):
            return None
        bridge = bridges[index]
        if (
            not isinstance(bridge, Mapping)
            or _status(bridge.get("status")) not in _BLOCKED_BRIDGE_STATUSES
        ):
            return None
        seen_indices.add(index)
        seen_rules.add(rule_id)
        requests.append({
            "bridge_obligation_index": index,
            "rule_id": rule_id,
        })
    return requests


def validate_trusted_bridge_requests(certificate: Mapping[str, Any]) -> str:
    """Validate the exact ID-only request schema used by Review milestones."""
    if not isinstance(certificate, Mapping):
        return f"{REQUEST_FIELD} requires a formalization Review object"
    requests = _requests(certificate)
    if requests is None:
        return (
            f"{REQUEST_FIELD} must be an array of unique exact dormant IDs, "
            "with exactly bridge_obligation_index and rule_id, at most one "
            "rule for each blocked bridge and only on a failed verdict"
        )
    if any(
        _validated_catalog_lookup(str(request["rule_id"])) is None
        for request in requests
    ):
        return (
            f"{REQUEST_FIELD} names a dormant rule whose sealed catalog "
            "record or hash binding is unavailable"
        )
    return ""


def _validated_catalog_lookup(rule_id: str) -> dict[str, Any] | None:
    """Resolve and independently verify one packaged empirical-rule receipt."""
    if rule_id not in DORMANT_RUNTIME_BRIDGE_IDS:
        return None
    try:
        lookup = chemistry_constant.empirical_rule(rule_id)
        sealed_registry = chemistry_constant._load_empirical_registry()
    except (ValueError, RuntimeError):
        return None
    if not isinstance(lookup, dict):
        return None
    expected_fields = {
        "approval", "base_dataset_sha256", "dataset_sha256",
        "dataset_version", "empirical_registry_manifest_sha256", "operation",
        "pinned_rule_record_sha256", "query", "record_sha256", "result",
        "runtime_network_access", "schema_version", "service", "source",
    }
    if set(lookup) != expected_fields:
        return None
    unsigned_lookup = dict(lookup)
    lookup_sha256 = unsigned_lookup.pop("record_sha256", None)
    if (
        lookup.get("schema_version") != chemistry_constant.SCHEMA_VERSION
        or lookup.get("service")
        != "archon_offline_chemistry_reference"
        or lookup.get("dataset_version") != chemistry_constant.DATASET_VERSION
        or lookup.get("operation") != "empirical_rule"
        or lookup.get("runtime_network_access") is not False
        or lookup.get("query") != {"rule": rule_id}
        or lookup.get("dataset_sha256") != chemistry_constant.DATASET_SHA256
        or lookup.get("base_dataset_sha256")
        != chemistry_constant.BASE_DATASET_SHA256
        or not isinstance(lookup_sha256, str)
        or _SHA256_RE.fullmatch(lookup_sha256) is None
        or hashlib.sha256(_canonical_json_bytes(unsigned_lookup)).hexdigest()
        != lookup_sha256
    ):
        return None

    rule = lookup.get("result")
    source = lookup.get("source")
    review = lookup.get("approval")
    if (
        not isinstance(rule, dict)
        or set(rule) != {
            "applicability_conditions", "authority_kind",
            "automatic_problem_instantiation", "claim", "exclusions",
            "rule_id", "rule_version",
        }
        or rule.get("rule_id") != rule_id
        or rule.get("automatic_problem_instantiation") is not False
        or not isinstance(rule.get("claim"), str)
        or not str(rule.get("claim") or "").strip()
        or not isinstance(rule.get("applicability_conditions"), list)
        or not rule["applicability_conditions"]
        or not all(isinstance(item, str) and item.strip() for item in rule["applicability_conditions"])
        or not isinstance(rule.get("exclusions"), list)
        or not all(isinstance(item, str) and item.strip() for item in rule["exclusions"])
        or not isinstance(source, dict)
        or set(source) != {"content_sha256", "doi", "locator", "url"}
        or not isinstance(source.get("content_sha256"), str)
        or _SHA256_RE.fullmatch(source["content_sha256"]) is None
        or not isinstance(source.get("url"), str)
        or not source["url"].startswith("https://")
        or not isinstance(source.get("locator"), str)
        or not source["locator"].strip()
        or not isinstance(review, dict)
        or set(review) != {
            "approval_scope", "approved_at", "reviewer_id", "status",
        }
        or review.get("status") != "approved"
        or review.get("approval_scope") != "rule_and_source"
    ):
        return None

    pinned_record_sha256 = lookup.get("pinned_rule_record_sha256")
    manifest_sha256 = lookup.get("empirical_registry_manifest_sha256")
    manifest = (
        sealed_registry.get("manifest")
        if isinstance(sealed_registry, Mapping)
        else None
    )
    sealed_records = (
        sealed_registry.get("records")
        if isinstance(sealed_registry, Mapping)
        else None
    )
    matching_sealed_records = (
        [
            record
            for record in sealed_records
            if isinstance(record, Mapping)
            and isinstance(record.get("rule"), Mapping)
            and record["rule"].get("rule_id") == rule_id
        ]
        if isinstance(sealed_records, list)
        else []
    )
    manifest_records = (
        manifest.get("records") if isinstance(manifest, Mapping) else None
    )
    matching_manifest_records = (
        [
            entry
            for entry in manifest_records
            if isinstance(entry, Mapping) and entry.get("rule_id") == rule_id
        ]
        if isinstance(manifest_records, list)
        else []
    )
    fresh_dataset_payload = {
        **chemistry_constant._BASE_DATASET_PAYLOAD,
        "dataset_version": chemistry_constant.DATASET_VERSION,
        "empirical_registry": sealed_registry,
    }
    fresh_dataset_sha256 = hashlib.sha256(
        _canonical_json_bytes(fresh_dataset_payload)
    ).hexdigest()
    unsigned_record = {
        "base_dataset_sha256": lookup["base_dataset_sha256"],
        "record_type": "trusted_chemistry_rule",
        "review": review,
        "rule": rule,
        "runtime_network_access": False,
        "schema_version": 1,
        "source": source,
    }
    if (
        not isinstance(pinned_record_sha256, str)
        or _SHA256_RE.fullmatch(pinned_record_sha256) is None
        or hashlib.sha256(_canonical_json_bytes(unsigned_record)).hexdigest()
        != pinned_record_sha256
        or not isinstance(manifest_sha256, str)
        or _SHA256_RE.fullmatch(manifest_sha256) is None
        or fresh_dataset_sha256 != chemistry_constant.DATASET_SHA256
        or not isinstance(sealed_registry, Mapping)
        or set(sealed_registry) != {"manifest", "records"}
        or len(matching_sealed_records) != 1
        or set(matching_sealed_records[0])
        != {
            "base_dataset_sha256",
            "record_sha256",
            "record_type",
            "review",
            "rule",
            "runtime_network_access",
            "schema_version",
            "source",
        }
        or matching_sealed_records[0].get("record_sha256")
        != pinned_record_sha256
        or matching_sealed_records[0].get("base_dataset_sha256")
        != lookup.get("base_dataset_sha256")
        or matching_sealed_records[0].get("rule") != rule
        or matching_sealed_records[0].get("source") != source
        or matching_sealed_records[0].get("review") != review
        or not isinstance(manifest, Mapping)
        or manifest.get("manifest_sha256") != manifest_sha256
        or len(matching_manifest_records) != 1
        or set(matching_manifest_records[0])
        != {"record_sha256", "rule_id", "rule_version"}
        or matching_manifest_records[0].get("record_sha256")
        != pinned_record_sha256
        or matching_manifest_records[0].get("rule_id") != rule_id
        or matching_manifest_records[0].get("rule_version")
        != rule.get("rule_version")
    ):
        return None
    return lookup


def build_trusted_bridge_activation_projection(
    certificate: Mapping[str, Any],
    *,
    target_rel: str,
    candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Rebuild complete target-local activation receipts from sealed records."""
    requests = _requests(certificate)
    if requests is None or not requests:
        return {}
    requests_sha256 = hashlib.sha256(
        _canonical_json_bytes(requests)
    ).hexdigest()
    incomplete = {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "requested_count": len(requests),
        "activated_count": 0,
        "complete": False,
        "requests_sha256": requests_sha256,
        "receipts": [],
    }
    target_rel = _safe_target_rel(target_rel)
    if (
        not target_rel
        or _SHA256_RE.fullmatch(candidate_sha256) is None
        or not is_native_problem_only_contract(expected_source_contract)
        or expected_source_contract.get("target") != target_rel
        or expected_source_contract.get("candidate") != target_rel
        or expected_source_contract.get("candidate_sha256") != candidate_sha256
    ):
        return incomplete
    try:
        source_error = validate_native_review_source_certificate(
            certificate,
            expected_source_contract,
            passing=False,
        )
    except (TypeError, ValueError):
        return incomplete
    if source_error:
        return incomplete

    source_binding: dict[str, str] = {}
    for field in _SOURCE_BINDING_HASH_FIELDS:
        value = expected_source_contract.get(field)
        if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
            return incomplete
        source_binding[field] = value

    receipts: list[dict[str, Any]] = []
    for request in requests:
        rule_id = str(request["rule_id"])
        lookup = _validated_catalog_lookup(rule_id)
        if lookup is None:
            return incomplete
        unsigned_receipt = {
            "schema_version": ACTIVATION_SCHEMA_VERSION,
            "kind": "controller_trusted_bridge_activation",
            "target": {
                "file": target_rel,
                "candidate_sha256": candidate_sha256,
            },
            "bridge_obligation_index": request["bridge_obligation_index"],
            "rule": lookup["result"],
            "source": lookup["source"],
            "review": lookup["approval"],
            "catalog_binding": {
                "base_dataset_sha256": lookup["base_dataset_sha256"],
                "dataset_sha256": lookup["dataset_sha256"],
                "empirical_registry_manifest_sha256": lookup[
                    "empirical_registry_manifest_sha256"
                ],
                "lookup_record_sha256": lookup["record_sha256"],
                "pinned_rule_record_sha256": lookup[
                    "pinned_rule_record_sha256"
                ],
                "source_content_sha256": lookup["source"]["content_sha256"],
            },
            "problem_source_binding": source_binding,
            "applicability": {
                "status": "not_evaluated_by_controller",
                "condition_semantics": "all_required_fail_closed",
                "required_condition_count": len(
                    lookup["result"]["applicability_conditions"]
                ),
                "complete_receipt_does_not_establish_conditions": True,
            },
            "scope": "next_target_local_formalization_redraft_only",
        }
        receipts.append({
            **unsigned_receipt,
            "activation_receipt_sha256": hashlib.sha256(
                _canonical_json_bytes(unsigned_receipt)
            ).hexdigest(),
        })

    return {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "requested_count": len(requests),
        "activated_count": len(receipts),
        "complete": len(receipts) == len(requests),
        "requests_sha256": requests_sha256,
        "receipts": receipts,
    }


def build_trusted_bridge_review_context(
    record: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Rebuild one consumed-activation audit context for the next Reviewer."""
    if not isinstance(record, Mapping):
        return {}
    reviews = record.get("reviews")
    last_review_iter = record.get("last_review_iter")
    repair_events = record.get("repair_events")
    if (
        _status(record.get("status")) != "retry"
        or type(reviews) is not int
        or reviews <= 0
        or type(last_review_iter) is not int
        or last_review_iter < 0
        or not isinstance(repair_events, list)
        or not repair_events
    ):
        return {}
    prior_candidate_sha256 = record.get("candidate_sha256")
    if (
        not isinstance(prior_candidate_sha256, str)
        or _SHA256_RE.fullmatch(prior_candidate_sha256) is None
        or prior_candidate_sha256 == current_candidate_sha256
        or not is_native_problem_only_contract(expected_source_contract)
        or expected_source_contract.get("target") != target_rel
        or expected_source_contract.get("candidate") != target_rel
        or expected_source_contract.get("candidate_sha256")
        != current_candidate_sha256
    ):
        return {}
    latest_event = repair_events[-1]
    if (
        not isinstance(latest_event, Mapping)
        or latest_event.get("schema_version") != 1
        or latest_event.get("review_kind") != "formalization"
        or latest_event.get("candidate_sha256") != prior_candidate_sha256
        or type(latest_event.get("iteration")) is not int
        or latest_event.get("iteration") != last_review_iter
        or type(latest_event.get("attempt")) is not int
        or latest_event.get("attempt") != reviews
        or _status(latest_event.get("resulting_status")) != "retry"
        or _status(latest_event.get("decision")) != "failed"
    ):
        return {}
    certificate = record.get("certificate")
    if not isinstance(certificate, Mapping):
        return {}
    milestones = certificate.get("milestones")
    if (
        isinstance(milestones, list)
        and len(milestones) == 1
        and isinstance(milestones[0], Mapping)
    ):
        certificate = milestones[0]
    prior_contract = dict(expected_source_contract)
    prior_contract["candidate_sha256"] = prior_candidate_sha256
    certificate_source = certificate.get("source_contract")
    if not isinstance(certificate_source, Mapping):
        return {}
    current_answer_path = expected_source_contract.get("answer_submission")
    if current_answer_path is not None:
        prior_answer_path = certificate_source.get("answer_submission")
        prior_answer_sha256 = certificate_source.get(
            "answer_submission_sha256"
        )
        if (
            prior_answer_path != current_answer_path
            or not isinstance(prior_answer_sha256, str)
            or _SHA256_RE.fullmatch(prior_answer_sha256) is None
        ):
            return {}
        prior_contract["answer_submission"] = prior_answer_path
        prior_contract["answer_submission_sha256"] = prior_answer_sha256
    activation = build_trusted_bridge_activation_projection(
        certificate,
        target_rel=target_rel,
        candidate_sha256=prior_candidate_sha256,
        expected_source_contract=prior_contract,
    )
    if not activation or activation.get("complete") is not True:
        return {}
    unsigned_context = {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "kind": "controller_trusted_bridge_activation_review_context",
        "target": {
            "file": target_rel,
            "activation_input_candidate_sha256": prior_candidate_sha256,
            "current_candidate_sha256": current_candidate_sha256,
        },
        "trusted_bridge_activations": activation,
        "scope": "audit_immediately_following_target_local_redraft",
    }
    return {
        **unsigned_context,
        "context_receipt_sha256": hashlib.sha256(
            _canonical_json_bytes(unsigned_context)
        ).hexdigest(),
    }
