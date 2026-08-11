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
from pathlib import Path
from typing import Any, Mapping

from archon.commands.tooling.domain_profile import (
    DomainProfile,
    load_domain_profile,
)


SOURCE_CONTRACT_SCHEMA_VERSION = 1
SOURCE_AUTHORITY = (
    "official source/rubric/images > blueprint > generated reports"
)
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
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = project_path / path
    return path.resolve()


def _source_report_path(
    *, project_path: Path, target: Path, blueprint_path: Path,
) -> tuple[Path | None, list[str]]:
    errors: list[str] = []
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
    report_path = _resolve_project_path(project_path, matches[0])
    if not report_path.is_file():
        errors.append(f"source report is missing: {report_path}")
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
    target = target.resolve()
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
    answer = entry.get("answer")
    previous_parts = entry.get("previous_parts")
    if not isinstance(current_question, str) or not current_question.strip():
        errors.append("source report entry.current_question is missing")
        current_question = ""
    if not isinstance(answer, str) or not answer.strip():
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
        image_path = _resolve_project_path(project_path, text)
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

    return {
        "schema_version": SOURCE_CONTRACT_SCHEMA_VERSION,
        "required": required,
        "available": available,
        "valid": not errors and (available or not required),
        "domain": profile.name,
        "authority": SOURCE_AUTHORITY,
        "target": rel,
        "lean_sha256": lean_sha256,
        "blueprint": _project_locator(blueprint_path, project_path),
        "blueprint_sha256": blueprint_sha256,
        "source_report": (
            _project_locator(report_path, project_path) if report_path else ""
        ),
        "source_sha256": source_sha256,
        "current_question_sha256": _value_sha256(current_question),
        "answer_sha256": _value_sha256(answer),
        "previous_parts_sha256": _value_sha256(previous_parts),
        "images": images,
        "errors": errors,
        "official_evidence": {
            "current_question": current_question,
            "answer": answer,
            "previous_parts": previous_parts,
        },
    }


def source_contract_provenance(contract: Mapping[str, Any]) -> dict[str, Any]:
    """Return the exact, compact provenance object a certificate must echo."""
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
        "the official question to make generated artifacts self-consistent.\n"
    )


def _status_and_evidence(value: Any) -> tuple[str, str]:
    if not isinstance(value, Mapping):
        return "", ""
    return (
        str(value.get("status") or "").strip().lower(),
        str(value.get("evidence") or value.get("reason") or "").strip(),
    )


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
    required = bool(expected_contract.get("required"))
    available = bool(expected_contract.get("available"))
    actual = review.get("source_contract")
    # Preserve legacy non-chemistry certificates.  New non-chemistry workers
    # still emit and bind provenance when a source bundle exists, but an older
    # certificate that predates this field remains admissible.
    if not required and (not available or not isinstance(actual, Mapping)):
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
    for key in (
        "schema_version", "authority", "target", "lean_sha256", "blueprint",
        "blueprint_sha256", "source_report", "source_sha256",
        "current_question_sha256", "answer_sha256", "previous_parts_sha256",
    ):
        if actual.get(key) != expected.get(key):
            return f"source_contract {key} does not match authoritative evidence"
    actual_images = actual.get("images")
    if actual_images != expected["images"]:
        return "source_contract image paths or hashes are stale/mismatched"

    if not required:
        return ""

    for group_name, names in (
        ("independent_source_audit", _INDEPENDENT_SOURCE_CHECKS),
        ("contract_audit", _CONTRACT_AUDIT_CHECKS),
    ):
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
        return "requested_outputs must contain every official requested output"
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

    alignment = review.get("official_answer_alignment")
    status, evidence = _status_and_evidence(alignment)
    if status not in _PASS | _FAIL or not evidence:
        return "official_answer_alignment status/evidence is missing"
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
        if conflict_status not in {
            "resolved_in_favor_of_official_source", "unresolved", "failed",
        }:
            return f"blueprint conflict {index} has invalid status"
        if passing and conflict_status != "resolved_in_favor_of_official_source":
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
