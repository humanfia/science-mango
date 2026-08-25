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

_LINEAGE_KIND = "controller_trusted_bridge_activation_lineage"
_AUDIT_CONTEXT_KIND = "controller_trusted_bridge_activation_audit_context"
_REDRAFT_ACTIVATION_FIELD = "trusted_bridge_redraft_activation"
_FORMALIZATION_REDRAFT_SCOPE = "next_target_local_formalization_redraft_only"
_REVIEW_AUDIT_SCOPE = "audit_immediately_following_target_local_redraft"
_CURRENT_CANDIDATE_AUDIT_SCOPE = "audit_current_target_candidate_only"
_LINEAGE_SCOPE = "target_local_activation_lineage_for_audit_or_one_redraft"

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
_IMMUTABLE_SOURCE_BINDING_HASH_FIELDS = tuple(
    field
    for field in _SOURCE_BINDING_HASH_FIELDS
    if field != "answer_submission_sha256"
)


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _immutable_source_bindings_match(
    left: Mapping[str, Any] | None,
    right: Mapping[str, Any] | None,
) -> bool:
    """Match problem inputs while allowing a reviewed answer-file rewrite."""
    if not isinstance(left, Mapping) or not isinstance(right, Mapping):
        return False
    return all(
        left.get(field) == right.get(field)
        for field in _IMMUTABLE_SOURCE_BINDING_HASH_FIELDS
    )


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
    if _status(record.get("reopened_by")) == "proof_review":
        return _build_reopened_trusted_bridge_review_context(
            record,
            target_rel=target_rel,
            current_candidate_sha256=current_candidate_sha256,
            expected_source_contract=expected_source_contract,
        )
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


def _source_binding_from_contract(
    expected_source_contract: Mapping[str, Any] | None,
    *,
    target_rel: str,
    candidate_sha256: str,
) -> dict[str, str] | None:
    """Return the exact problem hashes for one current native contract."""
    target_rel = _safe_target_rel(target_rel)
    if (
        not target_rel
        or _SHA256_RE.fullmatch(candidate_sha256) is None
        or not is_native_problem_only_contract(expected_source_contract)
        or expected_source_contract.get("target") != target_rel
        or expected_source_contract.get("candidate") != target_rel
        or expected_source_contract.get("candidate_sha256") != candidate_sha256
    ):
        return None
    source_binding: dict[str, str] = {}
    for field in _SOURCE_BINDING_HASH_FIELDS:
        value = expected_source_contract.get(field)
        if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
            return None
        source_binding[field] = value
    return source_binding


def _single_certificate(
    value: Mapping[str, Any] | None,
) -> Mapping[str, Any] | None:
    if not isinstance(value, Mapping):
        return None
    milestones = value.get("milestones")
    if milestones is None:
        return value
    if (
        not isinstance(milestones, list)
        or len(milestones) != 1
        or not isinstance(milestones[0], Mapping)
    ):
        return None
    return milestones[0]

def trusted_bridge_lineage_matches_formalization_pass(
    lineage: Mapping[str, Any] | None,
    *,
    target_rel: str,
    formalization_pass_candidate_sha256: object,
    passing_certificate: Mapping[str, Any] | None,
) -> bool:
    """Bind a self-validating lineage to the gate record that owns it."""
    certificate = _single_certificate(passing_certificate)
    candidate_sha256 = (
        formalization_pass_candidate_sha256
        if isinstance(formalization_pass_candidate_sha256, str)
        else ""
    )
    if (
        not isinstance(lineage, Mapping)
        or certificate is None
        or not _safe_target_rel(target_rel)
        or _SHA256_RE.fullmatch(candidate_sha256) is None
    ):
        return False
    target = lineage.get("target")
    pass_binding = lineage.get("formalization_pass_binding")
    certificate_sha256 = hashlib.sha256(
        _canonical_json_bytes(certificate)
    ).hexdigest()
    return bool(
        isinstance(target, Mapping)
        and target.get("file") == target_rel
        and target.get("formalization_pass_candidate_sha256")
        == candidate_sha256
        and isinstance(pass_binding, Mapping)
        and pass_binding.get("candidate_sha256") == candidate_sha256
        and pass_binding.get("certificate_sha256") == certificate_sha256
    )



def _catalog_binding(lookup: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "base_dataset_sha256": lookup["base_dataset_sha256"],
        "dataset_sha256": lookup["dataset_sha256"],
        "empirical_registry_manifest_sha256": lookup[
            "empirical_registry_manifest_sha256"
        ],
        "lookup_record_sha256": lookup["record_sha256"],
        "pinned_rule_record_sha256": lookup["pinned_rule_record_sha256"],
        "source_content_sha256": lookup["source"]["content_sha256"],
    }


def _applicability_projection(rule: Mapping[str, Any]) -> dict[str, Any]:
    conditions = rule.get("applicability_conditions")
    condition_count = len(conditions) if isinstance(conditions, list) else 0
    return {
        "status": "not_evaluated_by_controller",
        "condition_semantics": "all_required_fail_closed",
        "required_condition_count": condition_count,
        "complete_receipt_does_not_establish_conditions": True,
    }


def _validate_activation_receipt(
    receipt: Mapping[str, Any],
    *,
    target_rel: str,
    candidate_sha256: str,
    expected_scope: str,
    expected_source_binding: Mapping[str, str] | None = None,
    require_lineage_binding: bool = False,
    formalization_pass_candidate_sha256: str = "",
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Revalidate one receipt against the sealed catalog and exact bindings."""
    allowed_fields = {
        "schema_version", "kind", "target", "bridge_obligation_index",
        "rule", "source", "review", "catalog_binding",
        "problem_source_binding", "applicability", "scope",
        "activation_receipt_sha256",
    }
    if require_lineage_binding:
        allowed_fields.add("lineage_binding")
    if set(receipt) != allowed_fields:
        return None
    unsigned_receipt = dict(receipt)
    receipt_sha256 = unsigned_receipt.pop("activation_receipt_sha256", None)
    target = receipt.get("target")
    bridge_index = receipt.get("bridge_obligation_index")
    rule = receipt.get("rule")
    source_binding = receipt.get("problem_source_binding")
    applicability = receipt.get("applicability")
    if (
        receipt.get("schema_version") != ACTIVATION_SCHEMA_VERSION
        or receipt.get("kind") != "controller_trusted_bridge_activation"
        or not isinstance(receipt_sha256, str)
        or _SHA256_RE.fullmatch(receipt_sha256) is None
        or hashlib.sha256(_canonical_json_bytes(unsigned_receipt)).hexdigest()
        != receipt_sha256
        or not isinstance(target, Mapping)
        or set(target) != {"file", "candidate_sha256"}
        or target.get("file") != target_rel
        or target.get("candidate_sha256") != candidate_sha256
        or type(bridge_index) is not int
        or bridge_index < 0
        or not isinstance(rule, Mapping)
        or rule.get("automatic_problem_instantiation") is not False
        or not isinstance(rule.get("rule_id"), str)
        or not isinstance(rule.get("applicability_conditions"), list)
        or not rule.get("applicability_conditions")
        or not isinstance(rule.get("exclusions"), list)
        or not isinstance(source_binding, Mapping)
        or set(source_binding) != set(_SOURCE_BINDING_HASH_FIELDS)
        or any(
            not isinstance(source_binding.get(field), str)
            or _SHA256_RE.fullmatch(source_binding[field]) is None
            for field in _SOURCE_BINDING_HASH_FIELDS
        )
        or not isinstance(applicability, Mapping)
        or applicability != _applicability_projection(rule)
        or receipt.get("scope") != expected_scope
    ):
        return None
    if expected_source_binding is not None and dict(source_binding) != dict(
        expected_source_binding
    ):
        return None

    lookup = _validated_catalog_lookup(str(rule["rule_id"]))
    if (
        lookup is None
        or rule != lookup["result"]
        or receipt.get("source") != lookup["source"]
        or receipt.get("review") != lookup["approval"]
        or receipt.get("catalog_binding") != _catalog_binding(lookup)
    ):
        return None

    if require_lineage_binding:
        lineage_binding = receipt.get("lineage_binding")
        if (
            not isinstance(lineage_binding, Mapping)
            or set(lineage_binding) != {
                "lineage_receipt_sha256",
                "activation_review_context_sha256",
                "activation_input_candidate_sha256",
                "formalization_pass_candidate_sha256",
            }
            or any(
                not isinstance(lineage_binding.get(field), str)
                or _SHA256_RE.fullmatch(lineage_binding[field]) is None
                for field in lineage_binding
            )
            or lineage_binding.get("formalization_pass_candidate_sha256")
            != formalization_pass_candidate_sha256
        ):
            return None
    return dict(receipt), lookup


def _validate_activation_projection(
    projection: Mapping[str, Any],
    *,
    target_rel: str,
    candidate_sha256: str,
    expected_scope: str,
    expected_source_binding: Mapping[str, str] | None = None,
    require_lineage_binding: bool = False,
    formalization_pass_candidate_sha256: str = "",
) -> list[tuple[dict[str, Any], dict[str, Any]]] | None:
    if (
        set(projection) != {
            "schema_version", "requested_count", "activated_count",
            "complete", "requests_sha256", "receipts",
        }
        or projection.get("schema_version") != ACTIVATION_SCHEMA_VERSION
        or type(projection.get("requested_count")) is not int
        or projection.get("requested_count") <= 0
        or projection.get("activated_count")
        != projection.get("requested_count")
        or projection.get("complete") is not True
        or not isinstance(projection.get("requests_sha256"), str)
        or _SHA256_RE.fullmatch(projection["requests_sha256"]) is None
        or not isinstance(projection.get("receipts"), list)
        or len(projection["receipts"]) != projection.get("requested_count")
    ):
        return None
    validated: list[tuple[dict[str, Any], dict[str, Any]]] = []
    requests: list[dict[str, object]] = []
    seen_indices: set[int] = set()
    seen_rules: set[str] = set()
    for raw_receipt in projection["receipts"]:
        if not isinstance(raw_receipt, Mapping):
            return None
        item = _validate_activation_receipt(
            raw_receipt,
            target_rel=target_rel,
            candidate_sha256=candidate_sha256,
            expected_scope=expected_scope,
            expected_source_binding=expected_source_binding,
            require_lineage_binding=require_lineage_binding,
            formalization_pass_candidate_sha256=(
                formalization_pass_candidate_sha256
            ),
        )
        if item is None:
            return None
        receipt, lookup = item
        index = receipt["bridge_obligation_index"]
        rule_id = str(receipt["rule"]["rule_id"])
        if index in seen_indices or rule_id in seen_rules:
            return None
        seen_indices.add(index)
        seen_rules.add(rule_id)
        requests.append({
            "bridge_obligation_index": index,
            "rule_id": rule_id,
        })
        validated.append((receipt, lookup))
    if hashlib.sha256(_canonical_json_bytes(requests)).hexdigest() != projection.get(
        "requests_sha256"
    ):
        return None
    return validated


def build_trusted_bridge_activation_lineage(
    record: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
    passing_certificate: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Mint durable lineage only for the candidate that passed the next FR."""
    certificate = _single_certificate(passing_certificate)
    source_certificate = (
        _passing_source_certificate(certificate)
        if certificate is not None
        else None
    )
    source_binding = _source_binding_from_contract(
        expected_source_contract,
        target_rel=target_rel,
        candidate_sha256=current_candidate_sha256,
    )
    if (
        certificate is None
        or source_certificate is None
        or source_binding is None
        or validate_trusted_bridge_requests(certificate)
    ):
        return {}
    try:
        source_error = validate_native_review_source_certificate(
            source_certificate,
            expected_source_contract,
            passing=True,
        )
    except (TypeError, ValueError):
        return {}
    if source_error:
        return {}
    context = build_trusted_bridge_review_context(
        record,
        target_rel=target_rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=expected_source_contract,
    )
    if not context:
        return {}
    context_target = context.get("target")
    if not isinstance(context_target, Mapping):
        return {}
    activation_input_sha256 = context_target.get(
        "activation_input_candidate_sha256"
    )
    if (
        not isinstance(activation_input_sha256, str)
        or _SHA256_RE.fullmatch(activation_input_sha256) is None
        or context_target.get("file") != target_rel
        or context_target.get("current_candidate_sha256")
        != current_candidate_sha256
    ):
        return {}
    certificate_sha256 = hashlib.sha256(
        _canonical_json_bytes(certificate)
    ).hexdigest()
    unsigned_lineage = {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "kind": _LINEAGE_KIND,
        "target": {
            "file": target_rel,
            "activation_input_candidate_sha256": activation_input_sha256,
            "formalization_pass_candidate_sha256": current_candidate_sha256,
        },
        "problem_source_binding": source_binding,
        "activation_review_context": context,
        "formalization_pass_binding": {
            "candidate_sha256": current_candidate_sha256,
            "certificate_sha256": certificate_sha256,
        },
        "scope": _LINEAGE_SCOPE,
    }
    lineage = {
        **unsigned_lineage,
        "lineage_receipt_sha256": hashlib.sha256(
            _canonical_json_bytes(unsigned_lineage)
        ).hexdigest(),
    }
    # Never persist a controller-minted lineage that its consumers cannot
    # validate.  The activation-input receipt and this passing candidate are
    # distinct redraft hops, so their answer submissions may differ, but every
    # hop remains exactly bound and the problem inputs must remain immutable.
    if _validate_activation_lineage(
        lineage,
        target_rel=target_rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=expected_source_contract,
    ) is None:
        return {}
    return lineage


def _validate_activation_lineage(
    lineage: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> tuple[
    dict[str, Any],
    list[tuple[dict[str, Any], dict[str, Any]]],
] | None:
    source_binding = _source_binding_from_contract(
        expected_source_contract,
        target_rel=target_rel,
        candidate_sha256=current_candidate_sha256,
    )
    if not isinstance(lineage, Mapping) or source_binding is None:
        return None
    if set(lineage) != {
        "schema_version", "kind", "target", "problem_source_binding",
        "activation_review_context", "formalization_pass_binding", "scope",
        "lineage_receipt_sha256",
    }:
        return None
    unsigned_lineage = dict(lineage)
    lineage_sha256 = unsigned_lineage.pop("lineage_receipt_sha256", None)
    target = lineage.get("target")
    pass_binding = lineage.get("formalization_pass_binding")
    context = lineage.get("activation_review_context")
    if (
        lineage.get("schema_version") != ACTIVATION_SCHEMA_VERSION
        or lineage.get("kind") != _LINEAGE_KIND
        or lineage.get("scope") != _LINEAGE_SCOPE
        or not isinstance(lineage_sha256, str)
        or _SHA256_RE.fullmatch(lineage_sha256) is None
        or hashlib.sha256(_canonical_json_bytes(unsigned_lineage)).hexdigest()
        != lineage_sha256
        or not isinstance(target, Mapping)
        or set(target) != {
            "file", "activation_input_candidate_sha256",
            "formalization_pass_candidate_sha256",
        }
        or target.get("file") != target_rel
        or not isinstance(
            target.get("activation_input_candidate_sha256"), str
        )
        or _SHA256_RE.fullmatch(
            target["activation_input_candidate_sha256"]
        ) is None
        or not isinstance(
            target.get("formalization_pass_candidate_sha256"), str
        )
        or _SHA256_RE.fullmatch(
            target["formalization_pass_candidate_sha256"]
        ) is None
        or target.get("activation_input_candidate_sha256")
        == target.get("formalization_pass_candidate_sha256")
        or lineage.get("problem_source_binding") != source_binding
        or not isinstance(pass_binding, Mapping)
        or set(pass_binding) != {"candidate_sha256", "certificate_sha256"}
        or pass_binding.get("candidate_sha256")
        != target.get("formalization_pass_candidate_sha256")
        or not isinstance(pass_binding.get("certificate_sha256"), str)
        or _SHA256_RE.fullmatch(pass_binding["certificate_sha256"]) is None
        or not isinstance(context, Mapping)
    ):
        return None
    unsigned_context = dict(context)
    context_sha256 = unsigned_context.pop("context_receipt_sha256", None)
    context_target = context.get("target")
    projection = context.get("trusted_bridge_activations")
    if (
        set(context) != {
            "schema_version", "kind", "target",
            "trusted_bridge_activations", "scope", "context_receipt_sha256",
        }
        or context.get("schema_version") != ACTIVATION_SCHEMA_VERSION
        or context.get("kind")
        != "controller_trusted_bridge_activation_review_context"
        or context.get("scope") != _REVIEW_AUDIT_SCOPE
        or not isinstance(context_sha256, str)
        or _SHA256_RE.fullmatch(context_sha256) is None
        or hashlib.sha256(_canonical_json_bytes(unsigned_context)).hexdigest()
        != context_sha256
        or not isinstance(context_target, Mapping)
        or context_target != {
            "file": target_rel,
            "activation_input_candidate_sha256": target[
                "activation_input_candidate_sha256"
            ],
            "current_candidate_sha256": target[
                "formalization_pass_candidate_sha256"
            ],
        }
        or not isinstance(projection, Mapping)
    ):
        return None

    raw_receipts = projection.get("receipts")
    has_lineage_binding = (
        isinstance(raw_receipts, list)
        and bool(raw_receipts)
        and all(
            isinstance(receipt, Mapping) and "lineage_binding" in receipt
            for receipt in raw_receipts
        )
    )
    prior_pass_candidate_sha256 = ""
    prior_lineage_binding: Mapping[str, Any] | None = None
    if has_lineage_binding:
        first_binding = raw_receipts[0].get("lineage_binding")
        if not isinstance(first_binding, Mapping):
            return None
        prior_lineage_binding = first_binding
        prior_pass_candidate_sha256 = str(
            first_binding.get("formalization_pass_candidate_sha256") or ""
        )
    validated = _validate_activation_projection(
        projection,
        target_rel=target_rel,
        candidate_sha256=target["activation_input_candidate_sha256"],
        expected_scope=_FORMALIZATION_REDRAFT_SCOPE,
        require_lineage_binding=has_lineage_binding,
        formalization_pass_candidate_sha256=prior_pass_candidate_sha256,
    )
    if validated is None:
        return None
    if any(
        not _immutable_source_bindings_match(
            receipt["problem_source_binding"], source_binding,
        )
        or (prior_lineage_binding is not None and
            receipt.get("lineage_binding") != prior_lineage_binding)
        for receipt, _lookup in validated
    ):
        return None
    return dict(lineage), validated


def _build_lineage_reprojection(
    lineage: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
    scope: str,
) -> dict[str, Any]:
    validated_lineage = _validate_activation_lineage(
        lineage,
        target_rel=target_rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=expected_source_contract,
    )
    if validated_lineage is None:
        return {}
    lineage_record, validated_receipts = validated_lineage
    source_binding = dict(lineage_record["problem_source_binding"])
    lineage_target = lineage_record["target"]
    review_context = lineage_record["activation_review_context"]
    lineage_binding = {
        "lineage_receipt_sha256": lineage_record["lineage_receipt_sha256"],
        "activation_review_context_sha256": review_context[
            "context_receipt_sha256"
        ],
        "activation_input_candidate_sha256": lineage_target[
            "activation_input_candidate_sha256"
        ],
        "formalization_pass_candidate_sha256": lineage_target[
            "formalization_pass_candidate_sha256"
        ],
    }
    receipts: list[dict[str, Any]] = []
    for original_receipt, lookup in validated_receipts:
        unsigned_receipt = {
            "schema_version": ACTIVATION_SCHEMA_VERSION,
            "kind": "controller_trusted_bridge_activation",
            "target": {
                "file": target_rel,
                "candidate_sha256": current_candidate_sha256,
            },
            "bridge_obligation_index": original_receipt[
                "bridge_obligation_index"
            ],
            "rule": lookup["result"],
            "source": lookup["source"],
            "review": lookup["approval"],
            "catalog_binding": _catalog_binding(lookup),
            "problem_source_binding": source_binding,
            "applicability": _applicability_projection(lookup["result"]),
            "lineage_binding": lineage_binding,
            "scope": scope,
        }
        receipts.append({
            **unsigned_receipt,
            "activation_receipt_sha256": hashlib.sha256(
                _canonical_json_bytes(unsigned_receipt)
            ).hexdigest(),
        })
    original_projection = review_context["trusted_bridge_activations"]
    return {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "requested_count": len(receipts),
        "activated_count": len(receipts),
        "complete": bool(receipts),
        "requests_sha256": original_projection["requests_sha256"],
        "receipts": receipts,
    }


def build_trusted_bridge_activation_audit_context(
    lineage: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Reproject validated lineage for auditing one exact current candidate."""
    projection = _build_lineage_reprojection(
        lineage,
        target_rel=target_rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=expected_source_contract,
        scope=_CURRENT_CANDIDATE_AUDIT_SCOPE,
    )
    if not projection or not isinstance(lineage, Mapping):
        return {}
    lineage_target = lineage["target"]
    review_context = lineage["activation_review_context"]
    unsigned_context = {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "kind": _AUDIT_CONTEXT_KIND,
        "target": {
            "file": target_rel,
            "formalization_pass_candidate_sha256": lineage_target[
                "formalization_pass_candidate_sha256"
            ],
            "current_candidate_sha256": current_candidate_sha256,
        },
        "lineage_binding": {
            "lineage_receipt_sha256": lineage["lineage_receipt_sha256"],
            "activation_review_context_sha256": review_context[
                "context_receipt_sha256"
            ],
            "formalization_pass_certificate_sha256": lineage[
                "formalization_pass_binding"
            ]["certificate_sha256"],
        },
        "trusted_bridge_activations": projection,
        "scope": _CURRENT_CANDIDATE_AUDIT_SCOPE,
    }
    return {
        **unsigned_context,
        "context_receipt_sha256": hashlib.sha256(
            _canonical_json_bytes(unsigned_context)
        ).hexdigest(),
    }


def build_trusted_bridge_activation_redraft_projection(
    lineage: Mapping[str, Any] | None,
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Reproject validated lineage for one target-local redraft hand-off."""
    return _build_lineage_reprojection(
        lineage,
        target_rel=target_rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=expected_source_contract,
        scope=_FORMALIZATION_REDRAFT_SCOPE,
    )


def _build_reopened_trusted_bridge_review_context(
    record: Mapping[str, Any],
    *,
    target_rel: str,
    current_candidate_sha256: str,
    expected_source_contract: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Audit a controller-carried PR-to-redraft projection on the next FR."""
    reviews = record.get("reviews")
    last_reopened_iter = record.get("last_reopened_iter")
    prior_candidate_sha256 = record.get("candidate_sha256")
    reopen_history = record.get("reopen_history")
    certificate = record.get("certificate")
    projection = record.get(_REDRAFT_ACTIVATION_FIELD)
    if (
        _status(record.get("status")) != "retry"
        or _status(record.get("reopened_by")) != "proof_review"
        or type(reviews) is not int
        or reviews <= 0
        or type(last_reopened_iter) is not int
        or last_reopened_iter < 0
        or not isinstance(prior_candidate_sha256, str)
        or _SHA256_RE.fullmatch(prior_candidate_sha256) is None
        or not isinstance(reopen_history, list)
        or not reopen_history
        or certificate != {}
        or not isinstance(projection, Mapping)
    ):
        return {}
    latest_reopen = reopen_history[-1]
    previous_certificate = (
        latest_reopen.get("previous_certificate")
        if isinstance(latest_reopen, Mapping)
        else None
    )
    if (
        not isinstance(latest_reopen, Mapping)
        or _status(latest_reopen.get("previous_status")) != "passed"
        or latest_reopen.get("previous_reviews") != reviews
        or latest_reopen.get("proof_review_iter") != last_reopened_iter
        or not isinstance(previous_certificate, Mapping)
        or previous_certificate.get("candidate_sha256")
        != prior_candidate_sha256
    ):
        return {}
    current_source_binding = _source_binding_from_contract(
        expected_source_contract,
        target_rel=target_rel,
        candidate_sha256=current_candidate_sha256,
    )
    if current_source_binding is None:
        return {}
    receipts = projection.get("receipts")
    if not isinstance(receipts, list) or not receipts:
        return {}
    first_target = (
        receipts[0].get("target")
        if isinstance(receipts[0], Mapping)
        else None
    )
    activation_input_sha256 = (
        first_target.get("candidate_sha256")
        if isinstance(first_target, Mapping)
        else None
    )
    if (
        not isinstance(activation_input_sha256, str)
        or _SHA256_RE.fullmatch(activation_input_sha256) is None
        or activation_input_sha256 == current_candidate_sha256
    ):
        return {}
    raw_parent_lineage = record.get("trusted_bridge_activation_lineage")
    parent_source_binding = (
        raw_parent_lineage.get("problem_source_binding")
        if isinstance(raw_parent_lineage, Mapping)
        else None
    )
    parent_certificate = _single_certificate(previous_certificate)
    parent_certificate_source = (
        parent_certificate.get("source_contract")
        if isinstance(parent_certificate, Mapping)
        else None
    )
    parent_answer_sha256 = (
        parent_certificate_source.get("answer_submission_sha256")
        if isinstance(parent_certificate_source, Mapping)
        else None
    )
    if (
        not _immutable_source_bindings_match(
            parent_source_binding, current_source_binding,
        )
        or not isinstance(parent_answer_sha256, str)
        or _SHA256_RE.fullmatch(parent_answer_sha256) is None
        or not trusted_bridge_lineage_matches_formalization_pass(
            raw_parent_lineage
            if isinstance(raw_parent_lineage, Mapping) else None,
            target_rel=target_rel,
            formalization_pass_candidate_sha256=prior_candidate_sha256,
            passing_certificate=previous_certificate,
        )
    ):
        return {}

    # Validate the parent and the proof-redraft projection against the exact
    # candidate/answer pair that owned them.  The current candidate and answer
    # are a new redraft output; only their immutable problem hashes may be
    # compared before the fresh Formalization Review decides whether they pass.
    parent_contract = dict(expected_source_contract or {})
    parent_contract["candidate_sha256"] = prior_candidate_sha256
    parent_contract["answer_submission_sha256"] = parent_answer_sha256
    parent = _validate_activation_lineage(
        raw_parent_lineage,
        target_rel=target_rel,
        current_candidate_sha256=prior_candidate_sha256,
        expected_source_contract=parent_contract,
    )
    if parent is None:
        return {}
    validated = _validate_activation_projection(
        projection,
        target_rel=target_rel,
        candidate_sha256=activation_input_sha256,
        expected_scope=_FORMALIZATION_REDRAFT_SCOPE,
        expected_source_binding=parent_source_binding,
        require_lineage_binding=True,
        formalization_pass_candidate_sha256=prior_candidate_sha256,
    )
    if validated is None:
        return {}
    parent_lineage = parent[0]
    parent_target = parent_lineage["target"]
    parent_context = parent_lineage["activation_review_context"]
    expected_lineage_binding = {
        "lineage_receipt_sha256": parent_lineage["lineage_receipt_sha256"],
        "activation_review_context_sha256": parent_context[
            "context_receipt_sha256"
        ],
        "activation_input_candidate_sha256": parent_target[
            "activation_input_candidate_sha256"
        ],
        "formalization_pass_candidate_sha256": parent_target[
            "formalization_pass_candidate_sha256"
        ],
    }
    if any(
        receipt.get("lineage_binding") != expected_lineage_binding
        for receipt, _lookup in validated
    ):
        return {}
    unsigned_context = {
        "schema_version": ACTIVATION_SCHEMA_VERSION,
        "kind": "controller_trusted_bridge_activation_review_context",
        "target": {
            "file": target_rel,
            "activation_input_candidate_sha256": activation_input_sha256,
            "current_candidate_sha256": current_candidate_sha256,
        },
        "trusted_bridge_activations": dict(projection),
        "scope": _REVIEW_AUDIT_SCOPE,
    }
    return {
        **unsigned_context,
        "context_receipt_sha256": hashlib.sha256(
            _canonical_json_bytes(unsigned_context)
        ).hexdigest(),
    }


def _passing_source_certificate(
    certificate: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Accept raw passes or the gate's already-validated narrow projection."""
    status = _status(certificate.get("status"))
    if status not in {"", "passed"}:
        return None
    checks = certificate.get("checks")
    bridges = certificate.get("bridge_obligations")
    source_certificate = (
        certificate
        if status == "passed"
        else certificate.get("blind_review_certificate")
    )
    if (
        certificate.get("schema_version") != 2
        or not isinstance(checks, Mapping)
        or not isinstance(bridges, list)
        or not bridges
        or not isinstance(source_certificate, Mapping)
    ):
        return None
    for name in (
        "source_faithfulness", "derivability", "abstraction_sufficiency",
        "uncertainty_propagation", "branch_orientation",
        "countermodel_resistance",
    ):
        check = checks.get(name)
        check_status = _status(
            check.get("status") if isinstance(check, Mapping) else None
        )
        evidence = check.get("evidence") if isinstance(check, Mapping) else None
        allowed = check_status in {
            "passed", "pass", "approved", "review_passing",
        } or (
            name in {"uncertainty_propagation", "branch_orientation"}
            and check_status in {"not_applicable", "n/a", "na"}
        )
        if not allowed or not isinstance(evidence, str) or not evidence.strip():
            return None
    if any(
        not isinstance(bridge, Mapping)
        or _status(bridge.get("status"))
        not in {"covered", "grounded", "encoded", "proved", "pass", "passed"}
        or not str(
            bridge.get("claim") or bridge.get("source_claim") or ""
        ).strip()
        or not str(
            bridge.get("carrier") or bridge.get("lean_carrier") or ""
        ).strip()
        or not str(
            bridge.get("evidence") or bridge.get("reason") or ""
        ).strip()
        for bridge in bridges
    ):
        return None
    return source_certificate
