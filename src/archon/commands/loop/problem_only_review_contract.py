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
import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from .review_source_contract import (
    build_review_source_contract,
    is_answer_blind_contract,
    render_source_contract_prompt,
    source_contract_provenance,
    stored_provenance_matches_current,
    validate_review_source_certificate,
)


NATIVE_CONTRACT_KIND = "native_problem_input_only"
NATIVE_CONTRACT_SCHEMA_VERSION = 1
_BLIND_PROTOCOL = "icho-answer-blind-v1"
_SEED_PROTOCOL = "icho-problem-only-solver-seed-v1"
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_PREFLIGHT_FIELDS = {
    "file",
    "status",
    "compiles",
    "returncode",
    "sorry_count",
    "duration_secs",
    "diagnostics",
}
_PREFLIGHT_STATUSES = {"passed", "failed", "timeout", "error", "missing"}
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


def _validate_preflight(preflight: Mapping[str, Any], rel: str) -> dict[str, Any]:
    if not isinstance(preflight, Mapping):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight is missing"
        )
    if set(preflight) != _PREFLIGHT_FIELDS:
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
    if status == "passed" and (compiles is not True or returncode != 0):
        raise ProblemOnlyReviewContractError(
            "passing deterministic Lean preflight is contradictory"
        )
    if status != "passed" and compiles is not False:
        raise ProblemOnlyReviewContractError(
            "failing deterministic Lean preflight is contradictory"
        )
    if returncode is not None and (
        isinstance(returncode, bool) or not isinstance(returncode, int)
    ):
        raise ProblemOnlyReviewContractError(
            "deterministic Lean preflight returncode is invalid"
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
    preflight_row = (
        _validate_preflight(preflight, rel) if preflight is not None else None
    )
    bundle_path, bundle_payload, manifest, rows = _load_bundle(project_path)
    row = rows.get(record_id)
    if row is None:
        raise ProblemOnlyReviewContractError(
            "Lean candidate has no unique questions-only record"
        )
    _validate_problem_row(row, record_id)
    record_sha256 = _sha256_bytes(_canonical_json_bytes(row))
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
        "previous_parts": row["previous_parts"],
        "requested_outputs": row["requested_outputs"],
        "reporting_policy": row["reporting_policy"],
        "measurement_policy": row["measurement_policy"],
        "candidate_domain_policy": row["candidate_domain_policy"],
    }
    return {
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
        "source_bundle_sha256": _sha256_bytes(bundle_payload),
        "source_record_id": record_id,
        "source_record_sha256": record_sha256,
        "source_report": report_path.relative_to(project_path).as_posix(),
        "source_report_sha256": _sha256_bytes(report_payload),
        "candidate": rel,
        "candidate_sha256": (
            _sha256_bytes(target_path.read_bytes())
            if require_candidate else None
        ),
        "preflight_sha256": (
            _value_sha256(preflight_row) if preflight_row is not None else None
        ),
        "question_sha256": _value_sha256(evidence["question"]),
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
        "images": images,
        "problem_evidence": evidence,
        "preflight": preflight_row,
        "errors": [],
    }


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
    return args


def is_native_problem_only_contract(contract: Mapping[str, Any] | None) -> bool:
    return bool(contract) and contract.get("contract_kind") == NATIVE_CONTRACT_KIND


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
        "source_report",
        "source_report_sha256",
        "candidate",
        "candidate_sha256",
        "question_sha256",
        "previous_parts_sha256",
        "requested_outputs_sha256",
        "reporting_policy_sha256",
        "measurement_policy_sha256",
        "candidate_domain_policy_sha256",
        "images",
    )
    return {key: contract.get(key) for key in keys}


def render_native_source_contract_prompt(contract: Mapping[str, Any]) -> str:
    if not is_native_problem_only_contract(contract):
        return render_source_contract_prompt(contract)
    evidence = contract.get("problem_evidence")
    if not isinstance(evidence, Mapping):
        raise ProblemOnlyReviewContractError(
            "native problem-only contract has no problem evidence"
        )
    return (
        "NATIVE PROBLEM-INPUT-ONLY CONTRACT (immutable evidence):\n"
        "- Authority: problem-only\n"
        "- Evaluation mode: answer_blind\n"
        "- Required persisted provenance (echo exactly): "
        + json.dumps(
            native_source_contract_provenance(contract),
            ensure_ascii=False,
            sort_keys=True,
        )
        + "\n- Problem evidence: "
        + json.dumps(evidence, ensure_ascii=False, sort_keys=True)
        + "\nThe source bundle/report locators and digests above are validation "
        "metadata only; do not open those files. Treat only the inline problem "
        "evidence and listed problem images as source facts. Treat the current "
        "Lean candidate as untrusted output to audit. Do not open any unlisted "
        "project artifact. Every requested output, reporting rule, tolerance, "
        "and candidate-domain restriction must be derived from the bound "
        "problem evidence. Missing or ambiguous evidence fails closed.\n"
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
        "blueprint": "",
        "blueprint_sha256": "",
        "source_report": contract.get("source_report"),
        "source_sha256": contract.get("source_report_sha256"),
        "entry_id": contract.get("source_record_id"),
        "blind_record_sha256": contract.get("source_record_sha256"),
        "blind_candidate_record": contract.get("candidate"),
        "blind_candidate_sha256": contract.get("candidate_sha256"),
        "lean_result_contracts_sha256": None,
        "requested_outputs": evidence.get("requested_outputs", []),
        "question_field": "question",
        "question_sha256": contract.get("question_sha256"),
        "previous_blind_sha256": contract.get("previous_parts_sha256"),
        "previous_blind_hashes": [],
        "images": contract.get("images", []),
        "errors": [],
    }


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
    expected_requirements = [
        item.get("source_requirement")
        for item in expected_outputs
        if isinstance(item, Mapping)
    ]
    if (
        len(expected_requirements) != len(expected_outputs)
        or len(set(expected_requirements)) != len(expected_requirements)
        or len(actual_outputs) != len(expected_outputs)
    ):
        return "requested_outputs do not exactly cover the bound problem outputs"
    actual_requirements: list[Any] = []
    for index, item in enumerate(actual_outputs, start=1):
        if not isinstance(item, Mapping):
            return f"requested output {index} is not an object"
        requirement = item.get("source_requirement")
        actual_requirements.append(requirement)
        if requirement not in expected_requirements:
            return (
                f"requested output {index} source_requirement is not bound "
                "problem evidence"
            )
        if passing and str(item.get("status") or "").strip().lower() != "covered":
            return f"passing verdict leaves requested output {index} uncovered"
    if (
        len(set(actual_requirements)) != len(actual_requirements)
        or set(actual_requirements) != set(expected_requirements)
    ):
        return "requested_outputs do not exactly cover the bound problem outputs"
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
        row = _validate_preflight(raw, candidate)
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
    """Validate durable provenance, with a source-only formalization mode."""
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
        expected = native_source_contract_provenance(
            _build_native_contract(
                project_path=project_path,
                target=target,
                preflight=None,
            )
        )
    except ProblemOnlyReviewContractError as exc:
        return False, str(exc)
    if not isinstance(provenance, Mapping):
        return False, "stored Review certificate has no source_contract provenance"
    actual = dict(provenance)
    if set(actual) != set(expected):
        return False, "stored native Review provenance fields are stale or ambiguous"
    for key, value in expected.items():
        if not bind_candidate and key == "candidate_sha256":
            continue
        if actual.get(key) != value:
            return False, f"stored native Review certificate is stale: {key} changed"
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
            rows[rel] = _validate_preflight(raw, rel)
        except ProblemOnlyReviewContractError as exc:
            return str(exc)
    expected = sorted(set(expected_rels))
    if sorted(rows) != expected:
        return (
            "native pipelined Review preflight target mismatch: "
            f"expected={expected!r}, actual={sorted(rows)!r}"
        )
    summary = preflight.get("summary")
    passed = sum(row["compiles"] is True for row in rows.values())
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
