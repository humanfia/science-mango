"""Fail-closed semantic certificates for native answer-blind chemistry Review.

The native chemistry workflow deliberately removes the strict, answer-bearing
source-report route before the model loop starts.  Its problem-only JSONL
bundle nevertheless contains a controller-authored requested-output contract.
This module binds an ordinary formalization Review milestone to that contract
without loading (or knowing about) any grader or official-answer artifact.

The checks here are structural.  They ensure that a passing reviewer records a
source-first derivation for every requested output, makes its interpretation
and source locators explicit, and reports exact agreement with the semantic
card and Lean statement.  They do not compare a derived raw value with an
answer key; mathematical correctness remains the responsibility of the
independent derivation and Lean proof.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping

from archon.commands.tooling.domain_profile import load_domain_profile


SCHEMA_VERSION = 1
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
MANIFEST_REL = Path("isolation_manifest.json")
NATIVE_PROFILE = "chemistry-native"
MAX_BUNDLE_BYTES = 16 * 1024 * 1024
MAX_BUNDLE_RECORDS = 4096
MAX_TEXT_CHARS = 1_600
MAX_JSON_VALUE_CHARS = 2_000
MAX_ITEMS_PER_FIELD = 32
MAX_OUTPUT_BYTES = 8 * 1024
MAX_CERTIFICATE_BYTES = 192 * 1024

_TOP_FIELDS = {
    "schema_version", "method", "ambiguity", "requested_outputs",
}
_OUTPUT_FIELDS = {
    "id", "kind", "source_requirement", "quantity_definition",
    "process_scope", "basis", "constants", "dependencies",
    "branch_conditions", "unit", "raw_result", "reporting",
    "lean_carriers", "semantic_card_comparison",
    "lean_statement_comparison", "source_locators", "evidence",
}
_LOCATOR_FIELDS = {"kind", "reference"}
_LOCATOR_KINDS = {
    "problem_text", "problem_image", "previous_parts", "pinned_library",
}
_PROCESS_SCOPES = {
    "cumulative", "overall", "repeated_process", "per_step", "per_cycle",
    "marginal", "instantaneous", "not_applicable", "other",
}
_LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_PINNED_LIBRARY_RE = re.compile(
    r"^(?:Mathlib|Physlib|CRNT)(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_PREVIOUS_PART_RE = re.compile(
    r"^previous_parts\[(?P<index>[0-9]+)\](?:\.[A-Za-z0-9_.-]+)?$"
)
_TEXT_REFERENCE_PREFIXES = (
    "question", "current_question", "shared_context", "requested_outputs[",
    "reporting_policy", "measurement_policy", "candidate_domain_policy",
)


class _CertificateError(ValueError):
    pass


def _error(message: str) -> None:
    raise _CertificateError(message)


def _safe_bundle_path(project_path: Path) -> Path:
    root = project_path.resolve()
    cursor = root
    for part in BUNDLE_REL.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            _error(f"problem-only bundle traverses a symlink: {BUNDLE_REL}")
    try:
        resolved = cursor.resolve()
        resolved.relative_to(root)
    except (OSError, ValueError):
        _error(f"problem-only bundle escapes the project: {BUNDLE_REL}")
    if not resolved.is_file() or resolved.is_symlink():
        _error(f"problem-only bundle is missing or unsafe: {BUNDLE_REL}")
    try:
        size = resolved.stat().st_size
    except OSError:
        _error(f"problem-only bundle is unreadable: {BUNDLE_REL}")
    if size <= 0 or size > MAX_BUNDLE_BYTES:
        _error("problem-only bundle size is outside the bounded native contract")
    return resolved


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _safe_project_file(project_path: Path, relative: str, *, label: str) -> Path:
    if not relative or "\\" in relative:
        _error(f"{label} has an unsafe project path")
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        _error(f"{label} has an unsafe project path")
    root = project_path.resolve()
    cursor = root
    for part in path.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            _error(f"{label} traverses a symlink")
    try:
        resolved = cursor.resolve()
        resolved.relative_to(root)
    except (OSError, ValueError):
        _error(f"{label} escapes the project")
    if not resolved.is_file() or resolved.is_symlink():
        _error(f"{label} is missing or unsafe")
    return resolved


def _load_isolation_manifest(
    project_path: Path,
    *,
    bundle_path: Path,
    rows: list[dict[str, Any]],
) -> tuple[dict[str, Any], str]:
    path = _safe_project_file(
        project_path, MANIFEST_REL.as_posix(), label="isolation manifest",
    )
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        _error("isolation manifest is invalid JSON")
    if not isinstance(value, dict):
        _error("isolation manifest is not an object")
    bundle = value.get("blind_bundle")
    if not isinstance(bundle, Mapping):
        _error("isolation manifest has no blind_bundle object")
    digest = _sha256(bundle_path)
    if (
        bundle.get("path") != BUNDLE_REL.as_posix()
        or bundle.get("sha256") != digest
        or value.get("blind_bundle_sha256") != digest
        or bundle.get("size") != bundle_path.stat().st_size
        or bundle.get("row_count") != len(rows)
    ):
        _error("isolation manifest does not bind the exact problem-only bundle")
    row_ids = sorted(str(row.get("id") or "") for row in rows)
    if value.get("target_ids") != row_ids:
        _error("isolation manifest target_ids do not match the problem-only bundle")
    assets = value.get("assets")
    if not isinstance(assets, Mapping) or not assets:
        _error("isolation manifest has no asset hash inventory")
    for relative, expected_digest in assets.items():
        if (
            not isinstance(relative, str)
            or not isinstance(expected_digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_digest) is None
        ):
            _error("isolation manifest contains an invalid asset hash")
    return value, _sha256(path)


def _safe_asset_path(value: Any) -> str:
    text = str(value or "").strip()
    if (
        not text
        or len(text) > MAX_TEXT_CHARS
        or "\\" in text
        or "://" in text
    ):
        return ""
    path = Path(text)
    if path.is_absolute() or ".." in path.parts:
        return ""
    return path.as_posix().lstrip("./")


def _record_assets(
    row: Mapping[str, Any],
    *,
    project_path: Path,
    manifest_assets: Mapping[str, Any],
) -> tuple[dict[str, str], ...]:
    listed_images: list[str] = []
    images = row.get("images")
    if isinstance(images, list):
        for value in images:
            path = _safe_asset_path(value)
            if path:
                listed_images.append(path)
    else:
        _error("problem row images is not a list")
    assets: dict[str, str] = {}
    records = row.get("problem_assets")
    if isinstance(records, list):
        for record in records:
            if not isinstance(record, Mapping):
                continue
            path = _safe_asset_path(record.get("path"))
            digest = str(record.get("sha256") or "")
            if path and record.get("kind") == "problem_page":
                if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                    _error(f"problem image {path!r} has an invalid declared hash")
                prior = assets.get(path)
                if prior is not None and prior != digest:
                    _error(f"problem image {path!r} has inconsistent hashes")
                assets[path] = digest
    if listed_images != list(assets) or not assets:
        _error("problem row images do not exactly match hashed problem_page assets")
    bound: list[dict[str, str]] = []
    for name, expected_digest in sorted(assets.items()):
        relative = f"icho_2026_source/image/{name}"
        if manifest_assets.get(relative) != expected_digest:
            _error(f"isolation manifest does not bind problem image {name!r}")
        path = _safe_project_file(project_path, relative, label=f"problem image {name}")
        if _sha256(path) != expected_digest:
            _error(f"problem image {name!r} hash does not match its source contract")
        bound.append({"path": name, "sha256": expected_digest})
    return tuple(bound)


def _load_bundle(project_path: Path) -> list[dict[str, Any]]:
    path = _safe_bundle_path(project_path)
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        _error("problem-only bundle is not readable UTF-8")
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        if len(rows) >= MAX_BUNDLE_RECORDS:
            _error("problem-only bundle exceeds the bounded record count")
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            _error(f"problem-only bundle line {line_number} is invalid JSON")
        if not isinstance(value, dict):
            _error(f"problem-only bundle line {line_number} is not an object")
        rows.append(value)
    if not rows:
        _error("problem-only bundle contains no records")
    return rows


def _validate_requested_output(
    raw: Any, *, record_id: str, index: int,
) -> dict[str, Any]:
    if not isinstance(raw, Mapping):
        _error(f"bundle {record_id} requested output {index} is not an object")
    output_id = str(raw.get("id") or "").strip()
    kind = str(raw.get("kind") or "").strip()
    requirement = str(raw.get("source_requirement") or "").strip()
    unit = raw.get("unit")
    policy = raw.get("reporting_policy")
    if not output_id or not kind or not requirement:
        _error(f"bundle {record_id} requested output {index} is incomplete")
    if not isinstance(unit, str):
        _error(f"bundle {record_id}/{output_id} unit is not a string")
    if not isinstance(policy, Mapping) or not policy:
        _error(f"bundle {record_id}/{output_id} reporting policy is missing")
    return {
        "id": output_id,
        "kind": kind,
        "source_requirement": requirement,
        "unit": unit,
        "reporting_policy": copy.deepcopy(dict(policy)),
    }


def build_native_semantic_review_contract(
    *, project_path: Path, target: Path,
) -> dict[str, Any] | None:
    """Build the problem-only expected contract for one native target.

    ``None`` means that the project is not using the native chemistry profile.
    For that profile, every preparation problem becomes an explicit invalid
    contract so a passing milestone can never bypass the gate.
    """
    if load_domain_profile(project_path).name != NATIVE_PROFILE:
        return None
    try:
        root = project_path.resolve()
        target_rel = target.resolve().relative_to(root).as_posix()
    except (OSError, ValueError):
        return {
            "required": True,
            "valid": False,
            "target": "",
            "errors": ["native semantic Review target escapes the project"],
        }

    try:
        bundle_path = _safe_bundle_path(root)
        rows = _load_bundle(root)
        isolation_manifest, manifest_sha256 = _load_isolation_manifest(
            root, bundle_path=bundle_path, rows=rows,
        )
        by_target: dict[str, dict[str, Any]] = {}
        for row in rows:
            record_id = str(row.get("id") or "").strip()
            if not record_id or not re.fullmatch(r"[A-Za-z0-9._-]+", record_id):
                _error("problem-only bundle contains a missing or unsafe id")
            expected_target = f"IChO2026Problems/problem_{record_id}.lean"
            if expected_target in by_target:
                _error(f"problem-only bundle contains duplicate id {record_id}")
            if (
                row.get("evaluation_mode") != "answer_blind"
                or row.get("official_answer_seen") is not False
                or str(row.get("phase") or "solve") != "solve"
            ):
                _error(f"problem-only bundle record {record_id} is not answer-blind")
            by_target[expected_target] = row
        row = by_target.get(target_rel)
        if row is None:
            _error(f"native target {target_rel!r} has no exact problem-only record")
        record_id = str(row["id"])
        raw_outputs = row.get("requested_outputs")
        if not isinstance(raw_outputs, list) or not raw_outputs:
            _error(f"bundle {record_id} has no requested outputs")
        requested = [
            _validate_requested_output(item, record_id=record_id, index=index)
            for index, item in enumerate(raw_outputs, start=1)
        ]
        ids = [item["id"] for item in requested]
        if len(set(ids)) != len(ids):
            _error(f"bundle {record_id} has duplicate requested output ids")
        reporting_policy = row.get("reporting_policy")
        if not isinstance(reporting_policy, Mapping) or not reporting_policy:
            _error(f"bundle {record_id} has no global reporting policy")
        measurement_policy = row.get("measurement_policy")
        if not isinstance(measurement_policy, Mapping) or not measurement_policy:
            _error(f"bundle {record_id} has no measurement policy")
        candidate_domain_policy = row.get("candidate_domain_policy")
        if (
            not isinstance(candidate_domain_policy, Mapping)
            or not candidate_domain_policy
        ):
            _error(f"bundle {record_id} has no candidate-domain policy")
        previous_parts = row.get("previous_parts")
        if not isinstance(previous_parts, list):
            _error(f"bundle {record_id} previous_parts is not a list")
        image_assets = _record_assets(
            row,
            project_path=root,
            manifest_assets=isolation_manifest["assets"],
        )
        return {
            "required": True,
            "valid": True,
            "target": target_rel,
            "record_id": record_id,
            "requested_outputs": requested,
            "reporting_policy": copy.deepcopy(dict(reporting_policy)),
            "bundle_sha256": _sha256(bundle_path),
            "manifest_sha256": manifest_sha256,
            "image_assets": list(image_assets),
            "previous_parts_count": len(previous_parts),
            "problem_evidence": {
                "question": copy.deepcopy(row.get("question")),
                "current_question": copy.deepcopy(row.get("current_question")),
                "shared_context": copy.deepcopy(row.get("shared_context")),
                "previous_parts": copy.deepcopy(previous_parts),
                "measurement_policy": copy.deepcopy(dict(measurement_policy)),
                "candidate_domain_policy": copy.deepcopy(
                    dict(candidate_domain_policy)
                ),
            },
            "errors": [],
        }
    except _CertificateError as exc:
        return {
            "required": True,
            "valid": False,
            "target": target_rel,
            "errors": [str(exc)],
        }


def _schema_example_contract() -> dict[str, Any]:
    """Small problem-only contract used to render the static policy example."""
    return {
        "required": True,
        "valid": True,
        "target": "IChO2026Problems/problem_example.lean",
        "record_id": "example",
        "requested_outputs": [{
            "id": "requested_output_id",
            "kind": "numeric",
            "source_requirement": "copy the exact requested-output text",
            "unit": "mol",
            "reporting_policy": {
                "kind": "significant_figures",
                "digits": 3,
            },
        }],
        "reporting_policy": {
            "intermediate_rounding": "forbidden",
            "final_precision": {
                "kind": "per_requested_output",
                "source": "requested_outputs",
            },
            "tie_rule": "half_away_from_zero",
        },
        "image_assets": [{"path": "problem-page.png", "sha256": "0" * 64}],
        "previous_parts_count": 1,
        "problem_evidence": {
            "question": "problem-only question",
            "current_question": "problem-only current question",
            "shared_context": "problem-only shared context",
            "previous_parts": [{"id": "prior"}],
            "measurement_policy": {"printed_constants": "exact"},
            "candidate_domain_policy": {"underdetermined": "report"},
        },
        "errors": [],
    }


def build_independent_rederivation_example(
    contract: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Build one compact, validator-compatible certificate example.

    The policy prompt and tests share this builder so the documented exact-key
    schema cannot drift independently from machine validation.  Values in a
    live certificate must be independently derived; this function supplies
    only compact structural examples and exact bundle-bound fields.
    """
    selected = contract or _schema_example_contract()
    outputs = selected.get("requested_outputs")
    if not isinstance(outputs, list) or not outputs:
        raise ValueError("semantic Review example requires requested outputs")
    global_policy = selected.get("reporting_policy")
    if not isinstance(global_policy, Mapping) or not global_policy:
        raise ValueError("semantic Review example requires a global policy")
    rendered_outputs: list[dict[str, Any]] = []
    for index, expected in enumerate(outputs, start=1):
        if not isinstance(expected, Mapping):
            raise ValueError("semantic Review example output is invalid")
        unit = str(expected.get("unit") or "")
        rendered_outputs.append({
            "id": str(expected.get("id") or ""),
            "kind": str(expected.get("kind") or ""),
            "source_requirement": str(expected.get("source_requirement") or ""),
            "quantity_definition": "concise exact meaning derived from the source",
            "process_scope": {
                "kind": "overall",
                "description": "overall quantity across the stated process",
            },
            "basis": {
                "status": "not_applicable",
                "numerator": "not_applicable",
                "denominator": "not_applicable",
                "mass_or_composition_basis": "not_applicable",
            },
            "constants": [],
            "dependencies": [],
            "branch_conditions": [],
            "unit": unit,
            "raw_result": {
                "value_or_expression": f"independently_derived_expression_{index}",
                "exact_unrounded": True,
                "derivation": "concise substitution into the source-grounded relation",
            },
            "reporting": {
                "policy": copy.deepcopy(dict(expected.get("reporting_policy") or {})),
                "global_policy": copy.deepcopy(dict(global_policy)),
                "application": "apply the bundle rule once to the final raw result",
            },
            "lean_carriers": {
                "inputs": [f"NativeReview.Output{index}.sourceInputs"],
                "relations": [f"NativeReview.Output{index}.governingRelation"],
                "raw_result": [f"NativeReview.Output{index}.rawResult"],
                "reported_result": [f"NativeReview.Output{index}.reportedResult"],
            },
            "semantic_card_comparison": {
                "status": "matched",
                "evidence": "all semantic-card fields match the source-first derivation",
            },
            "lean_statement_comparison": {
                "status": "matched",
                "evidence": "all Lean carriers match the source-first derivation",
            },
            "source_locators": [{
                "kind": "problem_text",
                "reference": "current_question",
            }],
            "evidence": "source-first derivation agrees with the card and Lean contract",
        })
    return {
        "schema_version": SCHEMA_VERSION,
        "method": "source_first_without_lean",
        "ambiguity": "clear",
        "requested_outputs": rendered_outputs,
    }


def render_independent_rederivation_instructions(
    contract: Mapping[str, Any] | None = None,
) -> str:
    """Render the canonical compact schema for the project Review policy."""
    example = {
        "independent_rederivation": build_independent_rederivation_example(contract)
    }
    return (
        "Use the exact compact schema below. Replace example semantic values "
        "with your source-first derivation, and copy id/kind/source_requirement, "
        "unit, per-output reporting.policy, and reporting.global_policy exactly "
        "from the matching problem-only bundle row. Do not add or omit keys. "
        "Empty constants/dependencies/branch_conditions arrays explicitly mean "
        "none; otherwise each entry carries its own problem-only source locator.\n\n"
        "```json\n"
        + json.dumps(example, ensure_ascii=False, indent=2, sort_keys=True)
        + "\n```\n\n"
        "Every requested output must appear exactly once and in bundle order. "
        "Allowed locator kinds are problem_text, problem_image, previous_parts, "
        "and pinned_library. A problem image reference is its exact allowed asset "
        "path plus #region; previous_parts uses an existing zero-based index; a "
        "pinned library reference is a fully-qualified Mathlib/Physlib/CRNT name. "
        "URLs, absolute paths, '..', grader data, and external workspaces are "
        "forbidden. Keep evidence concise. Raw values are checked for a source "
        "derivation and exact-unrounded attestation, never against an answer key. "
        "Both comparison statuses must be matched for a passing verdict."
    )


def render_native_problem_contract_prompt(contract: Mapping[str, Any]) -> str:
    """Render only the problem evidence available to one native Review worker."""
    if not contract.get("valid"):
        return (
            "NATIVE PROBLEM-ONLY CONTRACT IS INVALID: "
            + json.dumps(contract.get("errors") or [], ensure_ascii=False)
        )
    payload = {
        "record_id": contract.get("record_id"),
        "target": contract.get("target"),
        "evidence_binding": {
            "problem_bundle_sha256": contract.get("bundle_sha256"),
            "isolation_manifest_sha256": contract.get("manifest_sha256"),
        },
        "problem_evidence": contract.get("problem_evidence"),
        "requested_outputs": contract.get("requested_outputs"),
        "reporting_policy": contract.get("reporting_policy"),
        "problem_images": contract.get("image_assets"),
    }
    return (
        "NATIVE ANSWER-BLIND PROBLEM CONTRACT (only source of problem facts):\n"
        + json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
        + "\nOpen and inspect every listed problem image from the workspace's "
        "icho_2026_source/image directory. First fix an independent derivation "
        "using only this problem contract, those images, and pinned general laws. "
        "Do not inspect the Semantic Card, Lean target, task results, blueprint, "
        "or traces until that derivation is fixed. Never seek or read an official "
        "answer, grader, solution, rubric, candidate artifact, or prior run."
    )


def _exact_fields(value: Any, expected: set[str], *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _error(f"{label} must be an object")
    missing = sorted(expected - set(value))
    extra = sorted(set(value) - expected)
    if missing or extra:
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        _error(f"{label} has invalid fields: {'; '.join(details)}")
    return value


def _text(value: Any, *, label: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        _error(f"{label} must be a string")
    normalized = value.strip()
    if (not normalized and not allow_empty) or len(normalized) > MAX_TEXT_CHARS:
        _error(f"{label} is empty or too long")
    return normalized


def _plain_reference(value: Any, *, label: str) -> str:
    text = _text(value, label=label)
    if "\x00" in text or "\\" in text or "://" in text or text.startswith("/"):
        _error(f"{label} contains an external or unsafe locator")
    if ".." in Path(text.split("#", 1)[0]).parts:
        _error(f"{label} contains an external or unsafe locator")
    return text


def _locator(
    value: Any, *, label: str, contract: Mapping[str, Any],
) -> dict[str, str]:
    raw = _exact_fields(value, _LOCATOR_FIELDS, label=label)
    kind = _text(raw.get("kind"), label=f"{label}.kind")
    reference = _plain_reference(raw.get("reference"), label=f"{label}.reference")
    if kind not in _LOCATOR_KINDS:
        _error(f"{label}.kind is unsupported")
    if kind == "problem_image":
        asset, marker, region = reference.partition("#")
        allowed_assets = {
            str(item.get("path") or "")
            for item in contract.get("image_assets") or []
            if isinstance(item, Mapping)
        }
        if (
            not marker
            or not region.strip()
            or asset not in allowed_assets
        ):
            _error(
                f"{label} must reference an allowed problem image as path#region"
            )
    elif kind == "previous_parts":
        match = _PREVIOUS_PART_RE.fullmatch(reference)
        if (
            match is None
            or int(match.group("index")) >= int(
                contract.get("previous_parts_count") or 0
            )
        ):
            _error(f"{label} does not identify an available previous_parts entry")
    elif kind == "pinned_library":
        if _PINNED_LIBRARY_RE.fullmatch(reference) is None:
            _error(f"{label} is not a pinned Mathlib/Physlib/CRNT declaration")
    elif not reference.startswith(_TEXT_REFERENCE_PREFIXES):
        _error(f"{label} does not identify a problem-only text field")
    return {"kind": kind, "reference": reference}


def _locators(
    value: Any, *, label: str, contract: Mapping[str, Any],
) -> list[dict[str, str]]:
    value = _bounded_list(value, label=label, allow_empty=False)
    return [
        _locator(item, label=f"{label}[{index}]", contract=contract)
        for index, item in enumerate(value)
    ]


def _comparison(value: Any, *, label: str) -> dict[str, str]:
    raw = _exact_fields(value, {"status", "evidence"}, label=label)
    status = _text(raw.get("status"), label=f"{label}.status")
    evidence = _text(raw.get("evidence"), label=f"{label}.evidence")
    if status != "matched":
        _error(f"{label}.status must be matched for a passing Review")
    return {"status": status, "evidence": evidence}


def _json_value(value: Any, *, label: str) -> Any:
    if value is None or isinstance(value, bool):
        _error(f"{label} must be a source-derived value or symbolic expression")
    try:
        payload = json.dumps(value, ensure_ascii=False, sort_keys=True)
    except (TypeError, ValueError):
        _error(f"{label} is not JSON serializable")
    if not payload or len(payload) > MAX_JSON_VALUE_CHARS or value in ("", [], {}):
        _error(f"{label} is empty or too long")
    return copy.deepcopy(value)


def _bounded_list(value: Any, *, label: str, allow_empty: bool = True) -> list[Any]:
    if not isinstance(value, list):
        _error(f"{label} must be a list")
    if (not allow_empty and not value) or len(value) > MAX_ITEMS_PER_FIELD:
        _error(f"{label} has an invalid item count")
    return value


def _validate_output(
    raw_value: Any,
    *,
    expected: Mapping[str, Any],
    all_output_ids: set[str],
    contract: Mapping[str, Any],
    index: int,
) -> None:
    label = f"independent_rederivation.requested_outputs[{index}]"
    raw = _exact_fields(raw_value, _OUTPUT_FIELDS, label=label)
    try:
        output_bytes = len(
            json.dumps(raw, ensure_ascii=False, sort_keys=True).encode("utf-8")
        )
    except (TypeError, ValueError):
        _error(f"{label} is not JSON serializable")
    if output_bytes > MAX_OUTPUT_BYTES:
        _error(f"{label} exceeds the compact Review certificate limit")
    for field in ("id", "kind", "source_requirement"):
        actual = _text(raw.get(field), label=f"{label}.{field}")
        if actual != expected.get(field):
            _error(f"{label}.{field} does not exactly match the problem bundle")

    _text(raw.get("quantity_definition"), label=f"{label}.quantity_definition")

    scope = _exact_fields(
        raw.get("process_scope"), {"kind", "description"},
        label=f"{label}.process_scope",
    )
    scope_kind = _text(scope.get("kind"), label=f"{label}.process_scope.kind")
    if scope_kind not in _PROCESS_SCOPES:
        _error(f"{label}.process_scope.kind is unsupported")
    _text(scope.get("description"), label=f"{label}.process_scope.description")

    basis = _exact_fields(
        raw.get("basis"),
        {"status", "numerator", "denominator", "mass_or_composition_basis"},
        label=f"{label}.basis",
    )
    basis_status = _text(basis.get("status"), label=f"{label}.basis.status")
    if basis_status not in {"applicable", "not_applicable"}:
        _error(f"{label}.basis.status is unsupported")
    for field in ("numerator", "denominator", "mass_or_composition_basis"):
        text = _text(basis.get(field), label=f"{label}.basis.{field}")
        if basis_status == "not_applicable" and text != "not_applicable":
            _error(f"{label}.basis.{field} must explicitly be not_applicable")

    constant_items = _bounded_list(
        raw.get("constants"), label=f"{label}.constants"
    )
    for item_index, item in enumerate(constant_items):
        item_label = f"{label}.constants[{item_index}]"
        item_map = _exact_fields(
            item, {"name", "value", "unit", "source_locator"}, label=item_label,
        )
        _text(item_map.get("name"), label=f"{item_label}.name")
        _json_value(item_map.get("value"), label=f"{item_label}.value")
        _text(item_map.get("unit"), label=f"{item_label}.unit")
        _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )

    dependency_items = _bounded_list(
        raw.get("dependencies"), label=f"{label}.dependencies"
    )
    for item_index, item in enumerate(dependency_items):
        item_label = f"{label}.dependencies[{item_index}]"
        item_map = _exact_fields(
            item, {"kind", "reference", "relation", "source_locator"},
            label=item_label,
        )
        dependency_kind = _text(item_map.get("kind"), label=f"{item_label}.kind")
        reference = _text(item_map.get("reference"), label=f"{item_label}.reference")
        if dependency_kind not in {
            "requested_output", "previous_part", "source_quantity",
            "governing_relation",
        }:
            _error(f"{item_label}.kind is unsupported")
        if dependency_kind == "requested_output" and reference not in all_output_ids:
            _error(f"{item_label}.reference is not a requested output id")
        _text(item_map.get("relation"), label=f"{item_label}.relation")
        _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )

    branch_items = _bounded_list(
        raw.get("branch_conditions"), label=f"{label}.branch_conditions"
    )
    for item_index, item in enumerate(branch_items):
        item_label = f"{label}.branch_conditions[{item_index}]"
        item_map = _exact_fields(
            item, {"condition", "source_locator"}, label=item_label,
        )
        _text(item_map.get("condition"), label=f"{item_label}.condition")
        _locator(
            item_map.get("source_locator"),
            label=f"{item_label}.source_locator", contract=contract,
        )

    unit_value = _text(
        raw.get("unit"), label=f"{label}.unit", allow_empty=True,
    )
    if unit_value != expected.get("unit"):
        _error(f"{label}.unit does not exactly match the problem bundle")

    raw_result = _exact_fields(
        raw.get("raw_result"),
        {"value_or_expression", "exact_unrounded", "derivation"},
        label=f"{label}.raw_result",
    )
    _json_value(
        raw_result.get("value_or_expression"),
        label=f"{label}.raw_result.value_or_expression",
    )
    if raw_result.get("exact_unrounded") is not True:
        _error(f"{label}.raw_result.exact_unrounded must be true")
    _text(raw_result.get("derivation"), label=f"{label}.raw_result.derivation")

    reporting = _exact_fields(
        raw.get("reporting"), {"policy", "global_policy", "application"},
        label=f"{label}.reporting",
    )
    if reporting.get("policy") != expected.get("reporting_policy"):
        _error(f"{label}.reporting.policy does not exactly match the bundle")
    if reporting.get("global_policy") != contract.get("reporting_policy"):
        _error(f"{label}.reporting.global_policy does not exactly match the bundle")
    _text(reporting.get("application"), label=f"{label}.reporting.application")

    carriers = _exact_fields(
        raw.get("lean_carriers"),
        {"inputs", "relations", "raw_result", "reported_result"},
        label=f"{label}.lean_carriers",
    )
    for field in ("inputs", "relations", "raw_result", "reported_result"):
        names = carriers.get(field)
        names = _bounded_list(
            names, label=f"{label}.lean_carriers.{field}", allow_empty=False,
        )
        if any(
            not isinstance(name, str) or _LEAN_NAME_RE.fullmatch(name.strip()) is None
            for name in names
        ):
            _error(f"{label}.lean_carriers.{field} has an unsafe declaration")

    _comparison(
        raw.get("semantic_card_comparison"),
        label=f"{label}.semantic_card_comparison",
    )
    _comparison(
        raw.get("lean_statement_comparison"),
        label=f"{label}.lean_statement_comparison",
    )
    _locators(
        raw.get("source_locators"),
        label=f"{label}.source_locators",
        contract=contract,
    )
    _text(raw.get("evidence"), label=f"{label}.evidence")


def validate_independent_rederivation(
    review: Mapping[str, Any],
    contract: Mapping[str, Any] | None,
) -> tuple[str, dict[str, Any]]:
    """Validate one passing native certificate, returning error + normalized.

    Non-native callers pass ``None`` and retain the historical Review schema.
    An invalid native preparation contract always fails closed.
    """
    if contract is None:
        return "", {}
    errors = contract.get("errors")
    errors = errors if isinstance(errors, list) else []
    if not contract.get("valid") or errors:
        detail = "; ".join(str(item) for item in errors) or "unknown contract error"
        return f"native semantic Review contract is invalid: {detail}", {}
    try:
        raw = _exact_fields(
            review.get("independent_rederivation"),
            _TOP_FIELDS,
            label="independent_rederivation",
        )
        if raw.get("schema_version") != SCHEMA_VERSION:
            _error("independent_rederivation.schema_version is unsupported")
        if raw.get("method") != "source_first_without_lean":
            _error("independent_rederivation.method must be source_first_without_lean")
        if raw.get("ambiguity") != "clear":
            _error("independent_rederivation.ambiguity must be clear for a passing Review")
        try:
            certificate_bytes = len(
                json.dumps(raw, ensure_ascii=False, sort_keys=True).encode("utf-8")
            )
        except (TypeError, ValueError):
            _error("independent_rederivation is not JSON serializable")
        if certificate_bytes > MAX_CERTIFICATE_BYTES:
            _error("independent_rederivation exceeds the compact certificate limit")
        actual_outputs = raw.get("requested_outputs")
        expected_outputs = contract.get("requested_outputs")
        if not isinstance(actual_outputs, list) or not isinstance(expected_outputs, list):
            _error("independent_rederivation requested output inventory is invalid")
        expected_ids = [str(item.get("id") or "") for item in expected_outputs]
        actual_ids = [
            str(item.get("id") or "") if isinstance(item, Mapping) else ""
            for item in actual_outputs
        ]
        if actual_ids != expected_ids:
            _error(
                "independent_rederivation must cover the exact ordered requested output ids"
            )
        all_output_ids = set(expected_ids)
        for index, (actual, expected) in enumerate(
            zip(actual_outputs, expected_outputs, strict=True)
        ):
            _validate_output(
                actual,
                expected=expected,
                all_output_ids=all_output_ids,
                contract=contract,
                index=index,
            )
        normalized = copy.deepcopy(dict(raw))
        return "", normalized
    except _CertificateError as exc:
        return str(exc), {}


__all__ = [
    "BUNDLE_REL",
    "NATIVE_PROFILE",
    "SCHEMA_VERSION",
    "build_independent_rederivation_example",
    "build_native_semantic_review_contract",
    "render_independent_rederivation_instructions",
    "render_native_problem_contract_prompt",
    "validate_independent_rederivation",
]
