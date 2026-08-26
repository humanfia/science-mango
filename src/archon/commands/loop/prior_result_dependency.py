"""Small immutable A4/A5 result JSON consumed only by A6.

This module checks source identity, canonical hashes, the two reviewer statuses,
the current compile/zero-sorry result, and the six concrete answer payloads.
It intentionally has no independent-review receipt, source-contract capability,
exhaustiveness credential, verifier identity, or axiom chain.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import unicodedata
from collections.abc import Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any


SCHEMA_VERSION = 1
RECEIPT_KIND = "a4_a5_results_for_a6_v1"
LINEAGE_KIND = "a4_a5_a6_source_lineage_v1"
ENDPOINT_KIND = "a4_a5_a6_source_endpoint_v1"
SCOPE = "one_a6_consumer_from_reviewed_a4_a5"

_REQUIRED_OUTPUTS = {
    "icho_2026_t1_a4": (
        ("metal_q_identity", "classification", ""),
        ("hydrated_c_formula", "formula", ""),
        ("compound_d_formula", "formula", ""),
    ),
    "icho_2026_t1_a5": (
        ("compound_e_structure", "classification", ""),
        ("compound_f_structure", "classification", ""),
        ("compound_g_structure", "classification", ""),
    ),
}
_SHA_RE = re.compile(r"^[0-9a-f]{64}$", re.ASCII)
_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,255}$", re.ASCII)
_MAX_BYTES = 2 * 1024 * 1024
_MAX_TEXT = 16 * 1024
_REFUSAL_MARKERS = (
    "cannot determine", "can't determine", "unable to determine",
    "cannot conclude", "insufficient evidence", "insufficient information",
    "not enough information", "indeterminate", "undetermined", "unknown",
    "fail-closed", "fail closed", "withheld", "no conclusion",
    "无法确定", "不能确定", "无法判断", "不能判断", "证据不足",
    "信息不足", "不足以", "不确定", "拒绝作答", "拒答",
)

_LINEAGE_FIELDS = frozenset({
    "schema_version", "kind", "problem_id", "problem_pdf_sha256",
    "shared_context_sha256", "producer_bundle_sha256",
    "consumer_bundle_sha256", "producer_inventory_sha256",
    "consumer_inventory_sha256", "source_universe_sha256",
    "validation_lineage_id",
})
_ENDPOINT_FIELDS = frozenset({
    "schema_version", "kind", "phase", "lineage",
})
_REVIEW_FIELDS = frozenset({"status"})
_COMPILE_FIELDS = frozenset({
    "status", "candidate_sha256", "returncode", "sorry_count",
})
_PAYLOAD_FIELDS = frozenset({
    "output_id", "kind", "raw_value", "display_value", "unit",
})
_EXPORT_FIELDS = frozenset({
    "export_id", "result_payload", "result_payload_sha256",
})
_PRODUCER_FIELDS = frozenset({
    "source_id", "source_record_sha256",
    "previous_part_source_ids", "previous_part_source_ids_sha256",
    "source_bundle_sha256", "answer_submission_sha256",
    "official_answer_seen", "module", "module_sha256",
    "formalization_review", "proof_review", "compile_audit",
    "typed_exports",
})
_SNAPSHOT_FIELDS = _PRODUCER_FIELDS | frozenset({
    "schema_version", "controller_binding",
})
_CONSUMER_FIELDS = frozenset({
    "source_id", "target", "source_record_sha256", "previous_parts_sha256",
    "previous_part_source_ids", "source_bundle_sha256",
    "official_answer_seen",
})
_RECEIPT_FIELDS = frozenset({
    "schema_version", "kind", "complete", "lineage", "consumer",
    "producers", "scope", "receipt_sha256",
})
_FORBIDDEN_SOURCE_KEYS = {
    "answer", "answers", "grader", "grading", "rubric", "solution", "solutions",
}


class PriorResultDependencyError(ValueError):
    """The A4/A5 result file or one of its inputs is invalid."""


def _fail(message: str) -> None:
    raise PriorResultDependencyError(message)


def _canonical(value: object) -> bytes:
    try:
        return (
            json.dumps(
                value, ensure_ascii=False, sort_keys=True,
                separators=(",", ":"), allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as exc:
        raise PriorResultDependencyError("value is not finite JSON") from exc


def _hash(value: object) -> str:
    return hashlib.sha256(_canonical(value)).hexdigest()


def canonical_prior_result_value_sha256(value: object) -> str:
    return _hash(value)


def _clone(value: object, label: str) -> Any:
    try:
        return json.loads(_canonical(value))
    except (ValueError, UnicodeDecodeError) as exc:
        raise PriorResultDependencyError(f"{label} is not JSON") from exc


def _exact(value: object, fields: frozenset[str], label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != fields:
        _fail(f"{label} has invalid fields")
    return value


def _sha(value: object, label: str) -> str:
    if not isinstance(value, str) or _SHA_RE.fullmatch(value) is None:
        _fail(f"{label} must be a lowercase SHA-256")
    return value


def _ident(value: object, label: str) -> str:
    if not isinstance(value, str) or _ID_RE.fullmatch(value) is None:
        _fail(f"{label} is invalid")
    return value


def _target(value: object, label: str) -> str:
    if not isinstance(value, str) or not value or len(value) > 500:
        _fail(f"{label} is invalid")
    path = PurePosixPath(value)
    if (
        path.is_absolute() or path.suffix != ".lean" or ".." in path.parts
        or path.as_posix() != value
    ):
        _fail(f"{label} is not a safe relative Lean path")
    return value


def _expected_module(source_id: str) -> str:
    return f"IChO2026Problems/problem_{source_id}.lean"


def _part_number(source_id: str) -> tuple[str, int] | None:
    match = re.fullmatch(r"(.+_a)([0-9]+)", source_id)
    if match is None:
        return None
    return match.group(1), int(match.group(2))


def prior_result_dependency_relative_path(consumer_record_id: str) -> Path:
    consumer_record_id = _ident(consumer_record_id, "consumer_record_id")
    return (
        Path(".archon") / "prior-result-dependencies"
        / f"{consumer_record_id}.json"
    )


def _contains_refusal(value: object) -> bool:
    if isinstance(value, str):
        normalized = " ".join(
            unicodedata.normalize("NFKC", value).casefold().split()
        )
        return any(marker in normalized for marker in _REFUSAL_MARKERS)
    if isinstance(value, Mapping):
        return any(_contains_refusal(item) for item in value.values())
    if isinstance(value, Sequence) and not isinstance(
        value, (str, bytes, bytearray)
    ):
        return any(_contains_refusal(item) for item in value)
    return False


def _concrete(raw_value: object, display_value: object) -> bool:
    if (
        raw_value is None
        or isinstance(raw_value, bool)
        or not isinstance(display_value, str)
        or not display_value.strip()
        or len(display_value.encode("utf-8")) > _MAX_TEXT
        or _contains_refusal(raw_value)
        or _contains_refusal(display_value)
    ):
        return False
    if isinstance(raw_value, str):
        return bool(raw_value.strip()) and len(
            raw_value.encode("utf-8")
        ) <= _MAX_TEXT
    if isinstance(raw_value, (Mapping, Sequence)) and not isinstance(
        raw_value, (str, bytes, bytearray)
    ):
        return bool(raw_value)
    return True


def build_validation_lineage_bindings(
    *,
    problem_id: str,
    problem_pdf_sha256: str,
    shared_context_sha256: str,
    producer_bundle_sha256: str,
    consumer_bundle_sha256: str,
    producer_inventory_sha256: str,
    consumer_inventory_sha256: str,
) -> dict[str, Any]:
    try:
        universe = {
            "problem_id": _ident(problem_id, "problem_id"),
            "problem_pdf_sha256": _sha(
                problem_pdf_sha256, "problem_pdf_sha256"
            ),
            "shared_context_sha256": _sha(
                shared_context_sha256, "shared_context_sha256"
            ),
            "producer_bundle_sha256": _sha(
                producer_bundle_sha256, "producer_bundle_sha256"
            ),
            "consumer_bundle_sha256": _sha(
                consumer_bundle_sha256, "consumer_bundle_sha256"
            ),
        }
        unsigned = {
            "schema_version": SCHEMA_VERSION,
            "kind": LINEAGE_KIND,
            **universe,
            "producer_inventory_sha256": _sha(
                producer_inventory_sha256, "producer_inventory_sha256"
            ),
            "consumer_inventory_sha256": _sha(
                consumer_inventory_sha256, "consumer_inventory_sha256"
            ),
            "source_universe_sha256": _hash(universe),
        }
        lineage = {
            **unsigned,
            "validation_lineage_id": _hash(unsigned),
        }
        common = {
            "schema_version": SCHEMA_VERSION,
            "kind": ENDPOINT_KIND,
            "lineage": lineage,
        }
        return {
            "producer": {**common, "phase": "producer"},
            "consumer": {**common, "phase": "consumer"},
        }
    except PriorResultDependencyError:
        return {}


def _lineage(value: object) -> dict[str, Any]:
    raw = _exact(value, _LINEAGE_FIELDS, "lineage")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
        or raw.get("kind") != LINEAGE_KIND
    ):
        _fail("lineage header is invalid")
    universe = {
        "problem_id": _ident(raw.get("problem_id"), "lineage.problem_id"),
        "problem_pdf_sha256": _sha(
            raw.get("problem_pdf_sha256"), "lineage.problem_pdf_sha256"
        ),
        "shared_context_sha256": _sha(
            raw.get("shared_context_sha256"), "lineage.shared_context_sha256"
        ),
        "producer_bundle_sha256": _sha(
            raw.get("producer_bundle_sha256"),
            "lineage.producer_bundle_sha256",
        ),
        "consumer_bundle_sha256": _sha(
            raw.get("consumer_bundle_sha256"),
            "lineage.consumer_bundle_sha256",
        ),
    }
    unsigned = {
        "schema_version": SCHEMA_VERSION,
        "kind": LINEAGE_KIND,
        **universe,
        "producer_inventory_sha256": _sha(
            raw.get("producer_inventory_sha256"),
            "lineage.producer_inventory_sha256",
        ),
        "consumer_inventory_sha256": _sha(
            raw.get("consumer_inventory_sha256"),
            "lineage.consumer_inventory_sha256",
        ),
        "source_universe_sha256": _sha(
            raw.get("source_universe_sha256"),
            "lineage.source_universe_sha256",
        ),
    }
    if unsigned["source_universe_sha256"] != _hash(universe):
        _fail("source universe hash is stale")
    lineage_id = _sha(
        raw.get("validation_lineage_id"), "lineage.validation_lineage_id"
    )
    if lineage_id != _hash(unsigned):
        _fail("validation lineage hash is stale")
    return {**unsigned, "validation_lineage_id": lineage_id}


def _endpoint(value: object, phase: str) -> dict[str, Any]:
    raw = _exact(value, _ENDPOINT_FIELDS, f"{phase}_binding")
    if (
        type(raw.get("schema_version")) is not int
        or raw.get("schema_version") != SCHEMA_VERSION
        or raw.get("kind") != ENDPOINT_KIND
        or raw.get("phase") != phase
    ):
        _fail(f"{phase} endpoint is invalid")
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": ENDPOINT_KIND,
        "phase": phase,
        "lineage": _lineage(raw.get("lineage")),
    }


def _review(value: object, *, status: str, label: str) -> dict[str, str]:
    raw = _exact(value, _REVIEW_FIELDS, label)
    if raw.get("status") != status:
        _fail(f"{label} did not pass")
    return {"status": status}


def _compile(value: object, module_sha256: str) -> dict[str, Any]:
    raw = _exact(value, _COMPILE_FIELDS, "compile_audit")
    normalized = {
        "status": raw.get("status"),
        "candidate_sha256": _sha(
            raw.get("candidate_sha256"), "compile_audit.candidate_sha256"
        ),
        "returncode": raw.get("returncode"),
        "sorry_count": raw.get("sorry_count"),
    }
    if (
        normalized["status"] != "passed"
        or normalized["candidate_sha256"] != module_sha256
        or type(normalized["returncode"]) is not int
        or normalized["returncode"] != 0
        or type(normalized["sorry_count"]) is not int
        or normalized["sorry_count"] != 0
    ):
        _fail("Lean compile/zero-sorry result did not pass")
    return normalized


def _exports(
    value: object, *, source_id: str,
) -> list[dict[str, Any]]:
    expected = _REQUIRED_OUTPUTS.get(source_id)
    if (
        expected is None
        or not isinstance(value, list)
        or len(value) != len(expected)
    ):
        _fail(f"{source_id} results do not match requested outputs")
    normalized: list[dict[str, Any]] = []
    observed: list[tuple[object, object, object]] = []
    for index, item in enumerate(value):
        raw = _exact(item, _EXPORT_FIELDS, f"typed_exports[{index}]")
        payload_raw = _exact(
            raw.get("result_payload"), _PAYLOAD_FIELDS,
            f"typed_exports[{index}].result_payload",
        )
        payload = _clone(dict(payload_raw), "result_payload")
        output_id = _ident(payload.get("output_id"), "result_payload.output_id")
        expected_export_id = (
            f"certified_prior_result:{source_id}:{output_id}"
        )
        if raw.get("export_id") != expected_export_id:
            _fail(f"typed_exports[{index}] has invalid export_id")
        if _sha(
            raw.get("result_payload_sha256"), "result_payload_sha256"
        ) != _hash(payload):
            _fail(f"typed_exports[{index}] has a stale payload hash")
        observed.append((
            output_id, payload.get("kind"), payload.get("unit")
        ))
        if not _concrete(
            payload.get("raw_value"), payload.get("display_value")
        ):
            _fail(f"{source_id} output {output_id} is not concrete")
        normalized.append({
            "export_id": expected_export_id,
            "result_payload": payload,
            "result_payload_sha256": _hash(payload),
        })
    if observed != list(expected):
        _fail(f"{source_id} results do not match requested outputs")
    return normalized


def _producer_body(
    value: object, *, lineage: Mapping[str, Any],
    expected_source_id: str, consumer_source_id: str,
) -> dict[str, Any]:
    raw = _exact(value, _PRODUCER_FIELDS, "producer")
    source_id = _ident(raw.get("source_id"), "producer.source_id")
    if source_id != expected_source_id:
        _fail("producer order does not match A6")
    module = _target(raw.get("module"), "producer.module")
    if module != _expected_module(source_id):
        _fail("producer module is not source-id bound")
    module_sha256 = _sha(raw.get("module_sha256"), "producer.module_sha256")
    source_record_sha256 = _sha(
        raw.get("source_record_sha256"), "producer.source_record_sha256"
    )
    answer_submission_sha256 = _sha(
        raw.get("answer_submission_sha256"),
        "producer.answer_submission_sha256",
    )
    source_bundle_sha256 = _sha(
        raw.get("source_bundle_sha256"), "producer.source_bundle_sha256"
    )
    if (
        raw.get("official_answer_seen") is not False
        or source_bundle_sha256 != lineage["producer_bundle_sha256"]
    ):
        _fail("producer source binding is invalid")
    previous = raw.get("previous_part_source_ids")
    if (
        not isinstance(previous, list)
        or len(previous) > 16
        or any(not isinstance(item, str) for item in previous)
        or len(previous) != len(set(previous))
    ):
        _fail("producer previous-part list is invalid")
    previous = [
        _ident(item, "producer previous source id") for item in previous
    ]
    if _sha(
        raw.get("previous_part_source_ids_sha256"),
        "producer.previous_part_source_ids_sha256",
    ) != _hash(previous):
        _fail("producer previous-part hash is stale")
    current_part = _part_number(source_id)
    if current_part is None:
        _fail("producer part id is invalid")
    for dependency in previous:
        prior = _part_number(dependency)
        if (
            dependency == consumer_source_id
            or prior is None
            or prior[0] != current_part[0]
            or prior[1] >= current_part[1]
        ):
            _fail("producer dependency order is invalid")
    return {
        "source_id": source_id,
        "source_record_sha256": source_record_sha256,
        "previous_part_source_ids": previous,
        "previous_part_source_ids_sha256": _hash(previous),
        "source_bundle_sha256": source_bundle_sha256,
        "answer_submission_sha256": answer_submission_sha256,
        "official_answer_seen": False,
        "module": module,
        "module_sha256": module_sha256,
        "formalization_review": _review(
            raw.get("formalization_review"),
            status="passed", label="formalization_review",
        ),
        "proof_review": _review(
            raw.get("proof_review"),
            status="solved", label="proof_review",
        ),
        "compile_audit": _compile(
            raw.get("compile_audit"), module_sha256
        ),
        "typed_exports": _exports(
            raw.get("typed_exports"), source_id=source_id
        ),
    }


def _consumer_from_source(
    *, target: object, source_record: object,
    source_record_sha256: object, lineage: Mapping[str, Any],
) -> dict[str, Any]:
    if not isinstance(source_record, Mapping):
        _fail("consumer_source_record must be an object")
    record = _clone(source_record, "consumer_source_record")
    digest = _sha(source_record_sha256, "consumer_source_record_sha256")
    if _hash(record) != digest:
        _fail("consumer source record hash is stale")
    if (
        record.get("official_answer_seen") is not False
        or any(key in record for key in _FORBIDDEN_SOURCE_KEYS)
    ):
        _fail("consumer source record is not answer-blind")
    source_id = _ident(record.get("id"), "consumer source id")
    parsed = _part_number(source_id)
    if parsed is None or parsed[1] != 6:
        _fail("result file accepts only an A6 consumer")
    previous_raw = record.get("previous_parts")
    if not isinstance(previous_raw, list) or len(previous_raw) != 2:
        _fail("A6 must name exactly A4 and A5")
    previous = []
    for index, part in enumerate(previous_raw):
        if not isinstance(part, Mapping):
            _fail(f"previous_parts[{index}] is invalid")
        previous.append(
            _ident(part.get("source_id"), f"previous_parts[{index}].source_id")
        )
    expected = [f"{parsed[0]}4", f"{parsed[0]}5"]
    if previous != expected:
        _fail("A6 previous_parts must be ordered A4 then A5")
    if (
        record.get("problem_id") != lineage["problem_id"]
        or _hash(record.get("shared_context"))
        != lineage["shared_context_sha256"]
    ):
        _fail("consumer problem/shared context is stale")
    assets = record.get("problem_assets")
    pdf_hashes = {
        item.get("sha256") for item in assets
        if isinstance(assets, list) and isinstance(item, Mapping)
        and item.get("kind") == "problem_pdf"
    } if isinstance(assets, list) else set()
    if pdf_hashes != {lineage["problem_pdf_sha256"]}:
        _fail("consumer problem PDF binding is stale")
    target_rel = _target(target, "consumer_target")
    if target_rel != _expected_module(source_id):
        _fail("consumer target is not source-id bound")
    return {
        "source_id": source_id,
        "target": target_rel,
        "source_record_sha256": digest,
        "previous_parts_sha256": _hash(previous_raw),
        "previous_part_source_ids": previous,
        "source_bundle_sha256": lineage["consumer_bundle_sha256"],
        "official_answer_seen": False,
    }


def _consumer_body(
    value: object, *, lineage: Mapping[str, Any]
) -> dict[str, Any]:
    raw = _exact(value, _CONSUMER_FIELDS, "consumer")
    source_id = _ident(raw.get("source_id"), "consumer.source_id")
    parsed = _part_number(source_id)
    expected = (
        [f"{parsed[0]}4", f"{parsed[0]}5"]
        if parsed is not None and parsed[1] == 6 else []
    )
    if raw.get("previous_part_source_ids") != expected:
        _fail("frozen consumer is not exact A6(A4,A5)")
    normalized = {
        "source_id": source_id,
        "target": _target(raw.get("target"), "consumer.target"),
        "source_record_sha256": _sha(
            raw.get("source_record_sha256"), "consumer.source_record_sha256"
        ),
        "previous_parts_sha256": _sha(
            raw.get("previous_parts_sha256"), "consumer.previous_parts_sha256"
        ),
        "previous_part_source_ids": list(expected),
        "source_bundle_sha256": _sha(
            raw.get("source_bundle_sha256"), "consumer.source_bundle_sha256"
        ),
        "official_answer_seen": raw.get("official_answer_seen"),
    }
    if (
        normalized["target"] != _expected_module(source_id)
        or normalized["source_bundle_sha256"]
        != lineage["consumer_bundle_sha256"]
        or normalized["official_answer_seen"] is not False
    ):
        _fail("frozen consumer binding is stale")
    return normalized


def build_prior_result_dependency_context(
    *,
    consumer_target: str,
    consumer_source_record: Mapping[str, Any],
    consumer_source_record_sha256: str,
    consumer_controller_binding: Mapping[str, Any],
    producer_snapshots: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    try:
        consumer_endpoint = _endpoint(
            consumer_controller_binding, "consumer"
        )
        lineage = consumer_endpoint["lineage"]
        consumer = _consumer_from_source(
            target=consumer_target,
            source_record=consumer_source_record,
            source_record_sha256=consumer_source_record_sha256,
            lineage=lineage,
        )
        if (
            not isinstance(producer_snapshots, Sequence)
            or isinstance(producer_snapshots, (str, bytes, bytearray))
            or len(producer_snapshots) != 2
        ):
            _fail("exactly two producer snapshots are required")
        producers = []
        for expected_id, snapshot in zip(
            consumer["previous_part_source_ids"],
            producer_snapshots,
            strict=True,
        ):
            raw = _exact(snapshot, _SNAPSHOT_FIELDS, "producer_snapshot")
            if (
                type(raw.get("schema_version")) is not int
                or raw.get("schema_version") != SCHEMA_VERSION
            ):
                _fail("producer snapshot schema is invalid")
            endpoint = _endpoint(raw.get("controller_binding"), "producer")
            if endpoint["lineage"] != lineage:
                _fail("producer and consumer source lineages differ")
            producers.append(_producer_body(
                {key: raw[key] for key in _PRODUCER_FIELDS},
                lineage=lineage,
                expected_source_id=expected_id,
                consumer_source_id=consumer["source_id"],
            ))
        unsigned = {
            "schema_version": SCHEMA_VERSION,
            "kind": RECEIPT_KIND,
            "complete": True,
            "lineage": lineage,
            "consumer": consumer,
            "producers": producers,
            "scope": SCOPE,
        }
        result = {**unsigned, "receipt_sha256": _hash(unsigned)}
        return (
            result
            if not validate_prior_result_dependency_context_self(result)
            else {}
        )
    except (PriorResultDependencyError, RecursionError):
        return {}


def validate_prior_result_dependency_context_self(context: object) -> str:
    try:
        raw = _exact(context, _RECEIPT_FIELDS, "result")
        if (
            type(raw.get("schema_version")) is not int
            or raw.get("schema_version") != SCHEMA_VERSION
            or raw.get("kind") != RECEIPT_KIND
            or raw.get("complete") is not True
            or raw.get("scope") != SCOPE
        ):
            _fail("result header is invalid")
        lineage = _lineage(raw.get("lineage"))
        consumer = _consumer_body(raw.get("consumer"), lineage=lineage)
        producers_raw = raw.get("producers")
        if not isinstance(producers_raw, list) or len(producers_raw) != 2:
            _fail("result must contain exactly A4 and A5")
        producers = [
            _producer_body(
                producer, lineage=lineage,
                expected_source_id=expected_id,
                consumer_source_id=consumer["source_id"],
            )
            for expected_id, producer in zip(
                consumer["previous_part_source_ids"],
                producers_raw,
                strict=True,
            )
        ]
        unsigned = {
            "schema_version": SCHEMA_VERSION,
            "kind": RECEIPT_KIND,
            "complete": True,
            "lineage": lineage,
            "consumer": consumer,
            "producers": producers,
            "scope": SCOPE,
        }
        digest = _sha(raw.get("receipt_sha256"), "result.receipt_sha256")
        if digest != _hash(unsigned):
            _fail("result hash is stale")
        if dict(raw) != {**unsigned, "receipt_sha256": digest}:
            _fail("result JSON is not canonical")
        return ""
    except (PriorResultDependencyError, RecursionError) as exc:
        return str(exc) or "invalid prior-result JSON"


def validate_prior_result_dependency_context(
    context: object,
    *,
    consumer_target: str,
    consumer_source_record: Mapping[str, Any],
    consumer_source_record_sha256: str,
    consumer_controller_binding: Mapping[str, Any],
    producer_snapshots: Sequence[Mapping[str, Any]],
) -> str:
    expected = build_prior_result_dependency_context(
        consumer_target=consumer_target,
        consumer_source_record=consumer_source_record,
        consumer_source_record_sha256=consumer_source_record_sha256,
        consumer_controller_binding=consumer_controller_binding,
        producer_snapshots=producer_snapshots,
    )
    if not expected:
        return "current artifacts cannot build complete A4/A5 results"
    error = validate_prior_result_dependency_context_self(context)
    if error:
        return error
    if context != expected:
        return "A4/A5 results are stale for current artifacts"
    return ""


def render_prior_result_dependency_prompt(context: object) -> str:
    if validate_prior_result_dependency_context_self(context):
        return ""
    payload = {"certified_prior_result": context}
    return "\n".join([
        "Reviewed A4/A5 results for this A6 only (read-only).",
        "Lean compiled with zero sorry and both semantic reviewer gates passed.",
        "Stable locator: certified_prior_result.producers[i].typed_exports[j].",
        _canonical(payload).decode("utf-8").rstrip("\n"),
    ])


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant {value!r}")


def load_prior_result_dependency_context_checked(
    project_path: Path | str,
    consumer_record_id: str,
    *,
    controller_uid: int | None = None,
) -> tuple[dict[str, Any], str]:
    """Return a receipt and reason after owner, mode, and content checks."""

    try:
        expected_uid = os.geteuid() if controller_uid is None else controller_uid
        if type(expected_uid) is not int or expected_uid < 0:
            return {}, "invalid_controller_uid"
        root = Path(project_path).resolve(strict=True)
        root_metadata = root.lstat()
        if (
            not stat.S_ISDIR(root_metadata.st_mode)
            or root_metadata.st_uid != expected_uid
            or root_metadata.st_mode & 0o022
        ):
            return {}, "unsafe_project_root"
        relative = prior_result_dependency_relative_path(consumer_record_id)
        current = root
        for part in relative.parts[:-1]:
            current /= part
            metadata = current.lstat()
            if (
                stat.S_ISLNK(metadata.st_mode)
                or not stat.S_ISDIR(metadata.st_mode)
                or metadata.st_uid != expected_uid
                or metadata.st_mode & 0o022
            ):
                return {}, "unsafe_receipt_directory"
        path = root / relative
        before = path.lstat()
        if (
            stat.S_ISLNK(before.st_mode)
            or not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or before.st_uid != expected_uid
            or before.st_mode & 0o222
            or before.st_size > _MAX_BYTES
        ):
            return {}, "unsafe_receipt_file"
        flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(path, flags)
        try:
            metadata = os.fstat(descriptor)
            if (
                not stat.S_ISREG(metadata.st_mode)
                or metadata.st_nlink != 1
                or metadata.st_uid != expected_uid
                or metadata.st_mode & 0o222
                or metadata.st_size > _MAX_BYTES
                or (metadata.st_dev, metadata.st_ino)
                != (before.st_dev, before.st_ino)
            ):
                return {}, "unsafe_receipt_file"
            chunks: list[bytes] = []
            remaining = _MAX_BYTES + 1
            while remaining:
                chunk = os.read(descriptor, min(remaining, 1024 * 1024))
                if not chunk:
                    break
                chunks.append(chunk)
                remaining -= len(chunk)
            payload = b"".join(chunks)
        finally:
            os.close(descriptor)
        if len(payload) > _MAX_BYTES:
            return {}, "receipt_too_large"
        try:
            parsed = json.loads(
                payload.decode("utf-8", "strict"),
                object_pairs_hook=_strict_pairs,
                parse_constant=_reject_constant,
            )
        except (ValueError, UnicodeDecodeError, RecursionError):
            return {}, "invalid_receipt_json"
        if not isinstance(parsed, dict):
            return {}, "invalid_receipt_json"
        error = validate_prior_result_dependency_context_self(parsed)
        if error:
            return {}, f"invalid_receipt:{error}"
        return parsed, ""
    except FileNotFoundError:
        return {}, "missing_receipt"
    except (
        OSError, ValueError, UnicodeDecodeError, RecursionError,
        PriorResultDependencyError,
    ):
        return {}, "unsafe_receipt"


def load_prior_result_dependency_context(
    project_path: Path | str,
    consumer_record_id: str,
    *,
    controller_uid: int | None = None,
) -> dict[str, Any]:
    """Load one controller-owned, read-only, self-valid A4/A5 receipt."""

    receipt, _ = load_prior_result_dependency_context_checked(
        project_path,
        consumer_record_id,
        controller_uid=controller_uid,
    )
    return receipt
