"""Persistent per-target gate between autoformalization and proving.

The review agent records a semantic verdict for every autoformalized target.
Failed targets are retried in ``autoformalize`` up to a configured limit.
Targets that still fail are quarantined as ``review_exhausted`` and are never
dispatched in the ``prover`` stage.  The state is deliberately independent of
``PROGRESS.md`` so ``--stage prover`` / ``--from prover`` cannot bypass it.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping

from archon.commands.tooling.domain_profile import load_domain_profile
from archon.state import parse_objective_files
from archon.state.progress import write_stage

from .review_source_contract import (
    build_review_source_contract,
    provenance_from_review,
    normalized_review_source_certificate,
    source_assessment_from_review,
    stored_provenance_matches_current,
    validate_review_source_certificate,
)
from .sorry_count import file_open_sorry_count


STATE_FILENAME = "formalization-review-gate.json"
REPORT_FILENAME = "FORMALIZATION_REVIEW_GATE.md"
STATE_VERSION = 2
REVIEW_SCHEMA_VERSION = 2

_PASS_WORDS = {"pass", "passed", "approved", "review-passing", "review_passing"}
_FAIL_WORDS = {
    "fail", "failed", "blocked", "partial", "needs_redraft", "needs redraft",
    "not_started", "not started", "failed_retry", "rejected",
}
_NOT_APPLICABLE_WORDS = {
    "not_applicable", "not applicable", "n/a", "na",
}
_REQUIRED_REVIEW_CHECKS = (
    "source_faithfulness",
    "derivability",
    "abstraction_sufficiency",
    "uncertainty_propagation",
    "branch_orientation",
    "countermodel_resistance",
)
_NOT_APPLICABLE_CHECKS = {
    "uncertainty_propagation",
    "branch_orientation",
}
_BRIDGE_PASS_WORDS = {
    "covered", "grounded", "encoded", "proved", "pass", "passed",
}


@dataclass(frozen=True)
class GateResult:
    passed: tuple[str, ...]
    retry: tuple[str, ...]
    exhausted: tuple[str, ...]
    reviewed: tuple[str, ...]


@dataclass(frozen=True)
class TargetFormalizationReviewUpdate:
    """One idempotent formalization Review transition."""

    rel: str
    status: str
    reviews: int
    reason: str
    passed: bool
    applied: bool


def state_path(state_dir: Path) -> Path:
    return state_dir / STATE_FILENAME


def load_gate_state(state_dir: Path) -> dict[str, Any] | None:
    path = state_path(state_dir)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(data, dict) or not isinstance(data.get("targets", {}), dict):
        return None
    if data.get("version") != STATE_VERSION:
        return None
    return data


def _utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _file_sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _task_result_fingerprints(state_dir: Path, rel: str) -> dict[str, str]:
    slug = "_".join(Path(rel).with_suffix("").parts)
    result_root = state_dir / "task_results"
    candidates = {
        result_root / f"{rel}.md",
        result_root / f"{Path(rel).name}.md",
        result_root / f"{slug}.lean.md",
        result_root / f"{slug}.md",
    }
    fingerprints: dict[str, str] = {}
    for path in candidates:
        digest = _file_sha256(path)
        if digest:
            fingerprints[str(path)] = digest
    return fingerprints


def _int_or(value: Any, default: int) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _relative_file(raw: str, project_path: Path) -> str:
    if not raw:
        return ""
    path = Path(raw)
    try:
        if path.is_absolute():
            path = path.resolve().relative_to(project_path.resolve())
    except (OSError, ValueError):
        return ""
    normalized = path.as_posix().lstrip("./")
    if not normalized.endswith(".lean") or normalized.startswith("../"):
        return ""
    return normalized


def _status_and_evidence(raw: Any) -> tuple[str, str]:
    if not isinstance(raw, dict):
        return "", ""
    status = str(raw.get("status") or raw.get("verdict") or "").strip().lower()
    evidence = str(raw.get("evidence") or raw.get("reason") or "").strip()
    return status, evidence


def _validate_structured_review(
    raw: dict[str, Any],
    expected_source_contract: Mapping[str, Any] | None = None,
) -> tuple[bool, str, dict[str, Any]]:
    """Validate and normalize the machine-checkable Review certificate."""
    failures: list[str] = []
    normalized_checks: dict[str, dict[str, str]] = {}
    checks = raw.get("checks")
    if not isinstance(checks, dict):
        failures.append("missing structured formalization Review checks")
        checks = {}

    for name in _REQUIRED_REVIEW_CHECKS:
        status, evidence = _status_and_evidence(checks.get(name))
        allowed = status in _PASS_WORDS
        if name in _NOT_APPLICABLE_CHECKS:
            allowed = allowed or status in _NOT_APPLICABLE_WORDS
        if not allowed:
            failures.append(f"{name} is missing or not passing")
        if not evidence:
            failures.append(f"{name} is missing evidence")
        normalized_checks[name] = {"status": status, "evidence": evidence}

    normalized_bridges: list[dict[str, str]] = []
    bridges = raw.get("bridge_obligations")
    if not isinstance(bridges, list):
        failures.append("missing bridge_obligations list")
        bridges = []
    elif not bridges:
        failures.append("bridge_obligations must contain a source-to-target bridge")
    for index, bridge in enumerate(bridges, start=1):
        if not isinstance(bridge, dict):
            failures.append(f"bridge obligation {index} is not an object")
            continue
        claim = str(bridge.get("claim") or bridge.get("source_claim") or "").strip()
        carrier = str(bridge.get("carrier") or bridge.get("lean_carrier") or "").strip()
        status = str(bridge.get("status") or "").strip().lower()
        evidence = str(bridge.get("evidence") or bridge.get("reason") or "").strip()
        if not claim:
            failures.append(f"bridge obligation {index} is missing claim")
        if not carrier:
            failures.append(f"bridge obligation {index} is missing carrier")
        if status not in _BRIDGE_PASS_WORDS:
            failures.append(
                f"bridge obligation {index} is blocked or has invalid status"
            )
        if not evidence:
            failures.append(f"bridge obligation {index} is missing evidence")
        normalized_bridges.append({
            "claim": claim,
            "carrier": carrier,
            "status": status,
            "evidence": evidence,
        })

    certificate = {
        "schema_version": REVIEW_SCHEMA_VERSION,
        "checks": normalized_checks,
        "bridge_obligations": normalized_bridges,
        "source_contract": provenance_from_review(raw),
        "blind_review_certificate": normalized_review_source_certificate(raw),
        **source_assessment_from_review(raw),
    }
    source_error = validate_review_source_certificate(
        raw,
        expected_source_contract,
        passing=True,
    )
    if source_error:
        failures.append(source_error)
    if failures:
        return False, "; ".join(dict.fromkeys(failures))[:2000], certificate
    return True, "structured formalization Review certificate passed", certificate


def _decision_from_milestone(
    item: dict[str, Any],
    expected_source_contract: Mapping[str, Any] | None = None,
) -> tuple[str, str, dict[str, Any]]:
    """Return ``(passed|failed, reason, certificate)``; fail closed."""
    raw: Any = item.get("formalization_review")
    if raw is None:
        findings = item.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("formalization_review")

    reason = ""
    status = ""
    if isinstance(raw, dict):
        status = str(raw.get("status") or raw.get("verdict") or "").strip().lower()
        reason = str(raw.get("reason") or "").strip()
    elif raw is not None:
        status = str(raw).strip().lower()

    if status in _PASS_WORDS:
        if not isinstance(raw, dict):
            return "failed", "bare formalization Review pass lacks structured checks", {}
        valid, validation_reason, certificate = _validate_structured_review(
            raw, expected_source_contract,
        )
        if not valid:
            return "failed", validation_reason, certificate
        return "passed", reason or validation_reason, certificate
    if status in _FAIL_WORDS:
        # A failing certificate is still valuable audit evidence.  In
        # particular, its failed checks explain which part of the statement
        # needs redrafting.  It cannot authorize prover dispatch because the
        # decision remains failed, so preserve the complete payload rather
        # than replacing it with an empty object.
        certificate = dict(raw) if isinstance(raw, dict) else {}
        return "failed", reason or "formalization Review failed", certificate

    legacy = str(item.get("status") or "").strip().lower()
    findings = item.get("findings")
    blocker = ""
    if isinstance(findings, dict):
        blocker = str(findings.get("blocker") or "").strip()
    if legacy == "solved":
        return "failed", "legacy solved milestone lacks structured Review certificate", {}
    return "failed", blocker or "missing explicit formalization Review pass verdict", {}


def formalization_review_decision(
    row: dict[str, Any],
) -> tuple[str, str, dict[str, Any]]:
    """Public, side-effect-free formalization Review normalization."""
    return _decision_from_milestone(row)


def _milestone_target_file(item: Mapping[str, Any], project_path: Path) -> str:
    """Normalize current and legacy milestone target encodings.

    Review schema v2 writes ``target`` as an object containing ``file``.
    Early parallel formalization Review sessions wrote the Lean path directly
    as a string. Both forms identify the same target and pass through the same
    path-safety normalization.
    """
    target = item.get("target")
    if isinstance(target, Mapping):
        raw_file = target.get("file")
    elif isinstance(target, str):
        raw_file = target
    else:
        return ""
    return _relative_file(str(raw_file or ""), project_path)


def _load_milestone_decisions(
    session_dir: Path,
    project_path: Path,
) -> dict[str, tuple[str, str, dict[str, Any]]]:
    path = session_dir / "milestones.jsonl"
    decisions: dict[str, list[tuple[str, str, dict[str, Any]]]] = {}
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return {}
    for line in lines:
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(item, dict):
            continue
        rel = _milestone_target_file(item, project_path)
        if not rel:
            continue
        source_contract = build_review_source_contract(
            project_path=project_path,
            target=project_path / rel,
        )
        decisions.setdefault(rel, []).append(
            _decision_from_milestone(item, source_contract)
        )

    aggregated: dict[str, tuple[str, str, dict[str, Any]]] = {}
    for rel, verdicts in decisions.items():
        if len(verdicts) != 1:
            aggregated[rel] = (
                "failed",
                f"expected exactly one target-bound formalization Review milestone; found {len(verdicts)}",
                {"schema_version": REVIEW_SCHEMA_VERSION, "milestones": []},
            )
            continue
        failures = [
            reason for status, reason, _certificate in verdicts
            if status != "passed"
        ]
        item_certificate = verdicts[0][2]
        certificate = {
            "schema_version": REVIEW_SCHEMA_VERSION,
            "milestones": [item_certificate],
            "source_contract": item_certificate.get("source_contract"),
            "blind_review_certificate": item_certificate.get(
                "blind_review_certificate"
            ),
        }
        if failures:
            aggregated[rel] = (
                "failed", "; ".join(dict.fromkeys(failures))[:2000], certificate,
            )
        else:
            aggregated[rel] = (
                "passed", "all formalization Review entries passed", certificate,
            )
    return aggregated


def _doctor_failures(
    blockers: Iterable[dict[str, str]],
    project_path: Path,
) -> tuple[dict[str, list[dict[str, str]]], list[dict[str, str]]]:
    """Map every deterministic blocker to a file or the global scope.

    Keep structured, de-duplicated findings instead of a single reason per
    file.  A target can simultaneously fail semantic Review and have more
    than one blueprint-doctor finding; neither source may overwrite another.
    """
    per_file: dict[str, list[dict[str, str]]] = {}
    global_blockers: list[dict[str, str]] = []
    seen: set[tuple[str, str, str, str]] = set()
    for item in blockers:
        rel = _relative_file(str(item.get("file") or ""), project_path)
        reason = str(item.get("reason") or item.get("kind") or "physics Review blocker")
        finding = {
            "source": str(item.get("source") or "review-gate"),
            "kind": str(item.get("kind") or "blocker"),
            "reason": reason,
        }
        key = (rel, finding["source"], finding["kind"], reason)
        if key in seen:
            continue
        seen.add(key)
        if rel:
            per_file.setdefault(rel, []).append(finding)
        elif item.get("source") in {
            "review-agent",
            "physics-reviewer",
            "chemistry-reviewer",
        }:
            global_blockers.append(finding)
    return per_file, global_blockers


def _merge_review_failure_reasons(
    semantic_decision: str,
    semantic_reason: str,
    blockers: Iterable[Mapping[str, str]],
) -> str:
    """Render all independent gate inputs for the next planner/redrafter."""
    parts = [
        f"semantic Review {semantic_decision}: "
        f"{semantic_reason or 'no semantic reason was recorded'}"
    ]
    for blocker in blockers:
        source = str(blocker.get("source") or "review-gate")
        kind = str(blocker.get("kind") or "blocker")
        reason = str(blocker.get("reason") or "Review blocker")
        parts.append(f"Review blocker [{source}/{kind}]: {reason}")
    return "; ".join(parts)


def _initial_state(max_iterations: int) -> dict[str, Any]:
    return {
        "version": STATE_VERSION,
        "max_iterations": max_iterations,
        "updated_at": _utcnow(),
        "targets": {},
    }


def _write_state(state_dir: Path, data: dict[str, Any]) -> None:
    path = state_path(state_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = (json.dumps(data, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    tmp = path.with_suffix(path.suffix + ".tmp")
    try:
        tmp.write_bytes(payload)
        tmp.replace(path)
        return
    except PermissionError:
        # An answer-blind workspace deliberately keeps `.archon/` owned by
        # the trusted controller while pre-creating this one state inode as
        # solver-owned.  That layout prevents a solver from replacing config
        # or inventing peer state files, but it also makes the usual
        # write-temp-and-rename operation impossible.  In that one narrowly
        # defined case, update the existing regular inode in place.  Never use
        # this fallback when the temporary file was created: a later rename
        # failure must remain fail-closed.
        if tmp.exists() or tmp.is_symlink():
            raise
        try:
            metadata = path.lstat()
        except OSError:
            raise
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
            raise
        flags = os.O_WRONLY | os.O_TRUNC | os.O_CLOEXEC
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        descriptor = os.open(path, flags)
        try:
            with os.fdopen(descriptor, "wb", closefd=False) as stream:
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
        finally:
            os.close(descriptor)


def _replace_objectives(progress_file: Path, lines: list[str]) -> None:
    if not progress_file.exists():
        return
    text = progress_file.read_text(encoding="utf-8")
    body = "## Current Objectives\n\n" + "\n".join(lines).rstrip() + "\n\n"
    pattern = re.compile(
        r"^## Current Objectives\s*\n.*?(?=^## |\Z)",
        flags=re.MULTILINE | re.DOTALL,
    )
    if pattern.search(text):
        text = pattern.sub(body, text, count=1)
    else:
        text = text.rstrip() + "\n\n" + body
    progress_file.write_text(text, encoding="utf-8")


def _write_report(state_dir: Path, data: dict[str, Any]) -> None:
    targets = data.get("targets", {})
    buckets: dict[str, list[tuple[str, dict[str, Any]]]] = {
        "passed": [], "retry": [], "review_exhausted": [],
    }
    for rel, record in sorted(targets.items()):
        status = str(record.get("status") or "retry")
        buckets.setdefault(status, []).append((rel, record))

    lines = [
        "# Formalization Review Gate",
        "",
        f"- Maximum Review iterations per target: {data.get('max_iterations', 0)}",
        f"- Passed: {len(buckets.get('passed', []))}",
        f"- Retry: {len(buckets.get('retry', []))}",
        f"- Review exhausted (prover forbidden): {len(buckets.get('review_exhausted', []))}",
        "",
    ]
    for status, title in (
        ("retry", "Retry in autoformalize"),
        ("review_exhausted", "Review exhausted — blocked from prover"),
        ("passed", "Passed — eligible for prover"),
    ):
        lines.extend([f"## {title}", ""])
        entries = buckets.get(status, [])
        if not entries:
            lines.append("- None")
        for rel, record in entries:
            reason = str(record.get("reason") or "").replace("\n", " ")
            lines.append(
                f"- `{rel}` — reviews {record.get('reviews', 0)}/"
                f"{data.get('max_iterations', 0)}; {reason}"
            )
        lines.append("")
    (state_dir / REPORT_FILENAME).write_text("\n".join(lines), encoding="utf-8")


def reopen_formalization_targets(
    *,
    state_dir: Path,
    project_path: Path,
    progress_file: Path,
    redrafts: Mapping[str, Mapping[str, Any] | str],
    iter_num: int,
    max_iterations: int,
    completed_redrafts: Mapping[str, Mapping[str, Any]] | None = None,
    route_progress: bool = True,
    enforce_budget: bool = False,
) -> tuple[str, ...]:
    """Revoke prior pass certificates and route exact targets to redrafting.

    The old certificate remains only in ``reopen_history`` for auditability;
    dispatch gating sees the live ``retry`` status and therefore permits the
    target in autoformalize while forbidding it in prover.
    """
    max_iterations = max(1, int(max_iterations))
    data = load_gate_state(state_dir) or _initial_state(max_iterations)
    data["max_iterations"] = max_iterations
    targets: dict[str, Any] = data.setdefault("targets", {})
    reopened: list[str] = []
    objective_details: dict[str, tuple[str, str]] = {}
    completed_redrafts = completed_redrafts or {}

    for raw_rel, raw_proof_record in redrafts.items():
        rel = _relative_file(str(raw_rel), project_path)
        if not rel:
            continue
        proof_record = (
            dict(raw_proof_record)
            if isinstance(raw_proof_record, Mapping)
            else {"reason": str(raw_proof_record)}
        )
        old = targets.get(rel) if isinstance(targets.get(rel), dict) else {}
        reopen_history = old.get("reopen_history")
        reopen_history = (
            list(reopen_history) if isinstance(reopen_history, list) else []
        )
        reason = " ".join(str(proof_record.get("reason") or "").split())
        if not reason:
            reason = "proof Review found a statement/modeling defect"
        redraft_kind = str(
            proof_record.get("redraft_kind") or "other_modeling_defect"
        ).strip()
        prior_reviews = int(old.get("reviews") or 0)
        budget_exhausted = enforce_budget and prior_reviews >= max_iterations
        pipeline_event_id = str(
            proof_record.get("pipeline_event_id") or ""
        ).strip()
        if (
            pipeline_event_id
            and old.get("last_reopen_event_id") == pipeline_event_id
        ):
            objective_details[rel] = (redraft_kind, reason[:800])
            reopened.append(rel)
            continue
        reopen_history.append({
            "reopened_at": _utcnow(),
            "proof_review_iter": iter_num,
            "proof_review_reason": reason,
            "redraft_kind": redraft_kind,
            "previous_status": old.get("status"),
            "previous_reviews": int(old.get("reviews") or 0),
            "previous_reason": old.get("reason"),
            "previous_certificate": old.get("certificate"),
        })
        next_record = {
            **old,
            "status": "review_exhausted" if budget_exhausted else "retry",
            "reason": (
                "proof Review requested redraft, but maximum formalization "
                f"Review attempts were already reached ({prior_reviews}/"
                f"{max_iterations}): {reason}"
                if budget_exhausted
                else f"proof Review requested redraft: {reason}"
            ),
            "updated_at": _utcnow(),
            "review_schema_version": REVIEW_SCHEMA_VERSION,
            "certificate": {},
            "certificate_revoked_at": _utcnow(),
            "reopened_by": "proof_review",
            "last_reopened_iter": iter_num,
            "last_reopen_event_id": pipeline_event_id or None,
            "redraft_kind": redraft_kind,
            "reopen_history": reopen_history[-20:],
        }
        # A target-scoped formalizer may already have materialized this
        # redraft while peer provers/Reviewers were still running. Carry a
        # hash-bound hand-off into the gate so the next autoformalize phase
        # can skip duplicate model work and proceed directly to Review.
        raw_handoff = completed_redrafts.get(rel)
        handoff = dict(raw_handoff) if isinstance(raw_handoff, Mapping) else {}
        digest = str(handoff.get("lean_sha256") or "").strip().lower()
        current_digest = _file_sha256(project_path / rel)
        raw_result_fingerprints = handoff.get("task_result_fingerprints")
        result_fingerprints = (
            {
                str(path): str(value).strip().lower()
                for path, value in raw_result_fingerprints.items()
            }
            if isinstance(raw_result_fingerprints, Mapping) else {}
        )
        current_result_fingerprints = _task_result_fingerprints(state_dir, rel)
        preflight = handoff.get("preflight")
        if (
            str(handoff.get("status") or "") == "materialized"
            and str(handoff.get("file") or "").lstrip("./") == rel
            and handoff.get("changed") is True
            and handoff.get("task_result_updated") is True
            and isinstance(preflight, Mapping)
            and preflight.get("compiles") is True
            and len(digest) == 64
            and digest == current_digest
            and bool(result_fingerprints)
            and result_fingerprints == current_result_fingerprints
        ):
            next_record["materialized_redraft"] = {
                "status": "ready_for_review",
                "source_iter": _int_or(handoff.get("iteration"), iter_num),
                "lean_sha256": digest,
                "task_result_fingerprints": result_fingerprints,
                "review_attempt": _int_or(handoff.get("review_attempt"), 0),
                "redraft_kind": redraft_kind,
                "reason": reason[:2000],
                "runner_ok": bool(handoff.get("runner_ok")),
                "recorded_at": _utcnow(),
            }
        else:
            next_record.pop("materialized_redraft", None)
        targets[rel] = next_record
        objective_details[rel] = (redraft_kind, reason[:800])
        reopened.append(rel)

    if not reopened:
        return ()
    data["last_reopened_iter"] = iter_num
    data["updated_at"] = _utcnow()
    _write_state(state_dir, data)
    _write_report(state_dir, data)
    if route_progress:
        formalize_mode = (
            load_domain_profile(project_path).mode_for_stage("autoformalize")
            or "physics-formalize"
        )
        write_stage(progress_file, "autoformalize")
        _replace_objectives(progress_file, [
            f"- **`{rel}`** — Proof Review routed this target to statement redraft "
            f"({objective_details[rel][0]}): {objective_details[rel][1]} "
            f"[prover-mode: {formalize_mode}]"
            for rel in sorted(set(reopened))
        ])
    return tuple(sorted(set(reopened)))


def apply_formalization_review(
    *,
    state_dir: Path,
    project_path: Path,
    progress_file: Path,
    session_dir: Path,
    iter_num: int,
    reviewed_objectives: Iterable[Path],
    max_iterations: int,
    blockers: Iterable[dict[str, str]] = (),
) -> GateResult:
    """Persist one autoformalization Review and route the next stage."""
    max_iterations = max(1, int(max_iterations))
    data = load_gate_state(state_dir) or _initial_state(max_iterations)
    data["max_iterations"] = max_iterations
    targets: dict[str, Any] = data.setdefault("targets", {})

    decisions = _load_milestone_decisions(session_dir, project_path)
    objective_rels = {
        rel for p in reviewed_objectives
        if (rel := _relative_file(str(p), project_path))
    }
    # The journal may cover more targets than the final PROGRESS objective
    # section (large batch reviews do this); every concrete milestone belongs
    # to the gate. Conversely, a dispatched objective missing from the journal
    # fails closed.
    review_scope = objective_rels | set(decisions)
    per_file_blockers, global_blockers = _doctor_failures(blockers, project_path)

    for rel in sorted(review_scope):
        semantic_decision, semantic_reason, certificate = decisions.get(
            rel, ("failed", "review output omitted this dispatched target", {})
        )
        target_blockers = [
            *per_file_blockers.get(rel, []),
            *global_blockers,
        ]
        if target_blockers:
            decision = "failed"
            reason = _merge_review_failure_reasons(
                semantic_decision,
                semantic_reason,
                target_blockers,
            )
        else:
            decision = semantic_decision
            reason = semantic_reason

        old = targets.get(rel) if isinstance(targets.get(rel), dict) else {}
        reviews = int(old.get("reviews") or 0)
        if (
            reviews < max_iterations
            and int(old.get("last_review_iter") or -1) != iter_num
        ):
            reviews += 1
        if decision == "passed":
            status = "passed"
        elif reviews >= max_iterations:
            status = "review_exhausted"
        else:
            status = "retry"
        next_record = {
            **old,
            "status": status,
            "reviews": reviews,
            "last_review_iter": iter_num,
            "reason": reason,
            "updated_at": _utcnow(),
            "review_schema_version": REVIEW_SCHEMA_VERSION,
            "certificate": certificate,
        }
        materialized = old.get("materialized_redraft")
        if isinstance(materialized, dict):
            next_record["materialized_redraft"] = {
                **materialized,
                "status": "reviewed",
                "reviewed_iter": iter_num,
            }
        targets[rel] = next_record

    data["last_review_iter"] = iter_num
    data["updated_at"] = _utcnow()
    _write_state(state_dir, data)
    _write_report(state_dir, data)

    passed = tuple(sorted(k for k, v in targets.items() if v.get("status") == "passed"))
    retry = tuple(sorted(k for k, v in targets.items() if v.get("status") == "retry"))
    exhausted = tuple(sorted(
        k for k, v in targets.items() if v.get("status") == "review_exhausted"
    ))

    # A proof Review redraft quarantine is released only by a fresh structured
    # formalization pass. Import locally to keep the two persisted gates
    # independently loadable.
    if passed:
        from .proof_review_gate import reset_proof_review_targets_after_redraft

        reset_proof_review_targets_after_redraft(
            state_dir=state_dir,
            targets=passed,
            iter_num=iter_num,
        )

    if retry:
        formalize_mode = (
            load_domain_profile(project_path).mode_for_stage("autoformalize")
            or "physics-formalize"
        )
        write_stage(progress_file, "autoformalize")
        _replace_objectives(progress_file, [
            f"- **`{rel}`** — Redraft after failed formalization Review "
            f"({targets[rel]['reviews']}/{max_iterations} used). "
            f"[prover-mode: {formalize_mode}]"
            for rel in retry
        ])
    else:
        write_stage(progress_file, "prover")
        proof_ready = []
        for rel in passed:
            count = file_open_sorry_count(project_path / rel)
            if count is None or count > 0:
                proof_ready.append(rel)
        if proof_ready:
            proof_mode = (
                load_domain_profile(project_path).mode_for_stage("prover")
                or "physics"
            )
            _replace_objectives(progress_file, [
                f"- **`{rel}`** — Formalization Review passed; prove remaining "
                f"obligations. [prover-mode: {proof_mode}]"
                for rel in proof_ready
            ])
        else:
            _replace_objectives(progress_file, [
                "(no prover dispatch this iter — no Review-passed target has open proof obligations)"
            ])

    return GateResult(
        passed=passed,
        retry=retry,
        exhausted=exhausted,
        reviewed=tuple(sorted(review_scope)),
    )


def apply_target_formalization_review(
    *,
    state_dir: Path,
    project_path: Path,
    target: Path,
    milestone: dict[str, Any],
    iter_num: int,
    max_iterations: int,
    event_id: str,
) -> TargetFormalizationReviewUpdate:
    """Apply one semantic formalization verdict without routing PROGRESS.

    Unlike the batch transition, distinct target events in the same outer
    iteration each consume one formalization Review opportunity.  Stable event
    ids keep crash/resume replay from consuming an opportunity twice.
    """
    max_iterations = max(1, int(max_iterations))
    rel = _relative_file(str(target), project_path)
    milestone_rel = _milestone_target_file(milestone, project_path)
    if not rel or milestone_rel != rel:
        raise ValueError(
            f"formalization Review milestone target {milestone_rel!r} != {rel!r}"
        )
    if not event_id.strip():
        raise ValueError("formalization Review pipeline event_id is required")

    data = load_gate_state(state_dir) or _initial_state(max_iterations)
    data["max_iterations"] = max_iterations
    targets: dict[str, Any] = data.setdefault("targets", {})
    old = targets.get(rel) if isinstance(targets.get(rel), dict) else {}
    events = old.get("review_events")
    events = list(events) if isinstance(events, list) else []
    for entry in events:
        if isinstance(entry, dict) and entry.get("event_id") == event_id:
            status = str(old.get("status") or "retry")
            return TargetFormalizationReviewUpdate(
                rel=rel,
                status=status,
                reviews=int(old.get("reviews") or 0),
                reason=str(old.get("reason") or ""),
                passed=status == "passed",
                applied=False,
            )

    reviews = int(old.get("reviews") or 0)
    if reviews >= max_iterations:
        status = "review_exhausted"
        reason = (
            f"maximum formalization Review attempts already reached "
            f"({reviews}/{max_iterations})"
        )
        certificate: dict[str, Any] = {}
        decision = "failed"
    else:
        source_contract = build_review_source_contract(
            project_path=project_path,
            target=target,
        )
        decision, reason, certificate = _decision_from_milestone(
            milestone, source_contract,
        )
        reviews += 1
        if decision == "passed":
            status = "passed"
        elif reviews >= max_iterations:
            status = "review_exhausted"
        else:
            status = "retry"

    events.append({
        "event_id": event_id,
        "iter": iter_num,
        "decision": decision,
        "resulting_status": status,
        "attempt": reviews,
        "reason": reason,
        "reviewed_at": _utcnow(),
    })
    next_record = {
        **old,
        "status": status,
        "reviews": reviews,
        "last_review_iter": iter_num,
        "reason": reason,
        "updated_at": _utcnow(),
        "review_schema_version": REVIEW_SCHEMA_VERSION,
        "certificate": certificate,
        "review_events": events[-50:],
    }
    materialized = old.get("materialized_redraft")
    if isinstance(materialized, dict):
        next_record["materialized_redraft"] = {
            **materialized,
            "status": "reviewed",
            "reviewed_iter": iter_num,
        }
    targets[rel] = next_record
    data["last_review_iter"] = iter_num
    data["updated_at"] = _utcnow()
    _write_state(state_dir, data)
    _write_report(state_dir, data)

    if status == "passed":
        from .proof_review_gate import reset_proof_review_targets_after_redraft

        reset_proof_review_targets_after_redraft(
            state_dir=state_dir,
            targets=(rel,),
            iter_num=iter_num,
        )

    return TargetFormalizationReviewUpdate(
        rel=rel,
        status=status,
        reviews=reviews,
        reason=reason,
        passed=status == "passed",
        applied=True,
    )


def _certificate_source_provenance(certificate: Any) -> dict[str, Any] | None:
    if not isinstance(certificate, Mapping):
        return None
    direct = certificate.get("source_contract")
    if isinstance(direct, Mapping):
        return dict(direct)
    milestones = certificate.get("milestones")
    if isinstance(milestones, list):
        for item in milestones:
            found = _certificate_source_provenance(item)
            if found is not None:
                return found
    return None


def _invalidate_stale_passes(
    *,
    state_dir: Path,
    project_path: Path,
    state: dict[str, Any] | None,
) -> dict[str, Any] | None:
    """Reopen chemistry passes whose bound Lean/source inputs changed."""
    if state is None or load_domain_profile(project_path).name != "chemistry":
        return state
    targets = state.get("targets")
    if not isinstance(targets, dict):
        return state
    changed = False
    for rel, raw_record in list(targets.items()):
        if not isinstance(raw_record, dict) or raw_record.get("status") != "passed":
            continue
        provenance = _certificate_source_provenance(
            raw_record.get("certificate")
        )
        fresh, reason = stored_provenance_matches_current(
            project_path=project_path,
            target=project_path / rel,
            provenance=provenance,
        )
        if fresh:
            continue
        reopen_history = raw_record.get("reopen_history")
        reopen_history = (
            list(reopen_history) if isinstance(reopen_history, list) else []
        )
        reopen_history.append({
            "reopened_at": _utcnow(),
            "reopened_by": "source_contract_freshness",
            "previous_status": "passed",
            "previous_reviews": int(raw_record.get("reviews") or 0),
            "previous_reason": raw_record.get("reason"),
            "previous_certificate": raw_record.get("certificate"),
            "reason": reason,
        })
        targets[rel] = {
            **raw_record,
            "status": "retry",
            "reviews": 0,
            "reason": f"formalization Review certificate invalidated: {reason}",
            "certificate": {},
            "certificate_revoked_at": _utcnow(),
            "reopened_by": "source_contract_freshness",
            "reopen_history": reopen_history[-20:],
            "updated_at": _utcnow(),
        }
        changed = True
    if changed:
        state["targets"] = targets
        state["updated_at"] = _utcnow()
        _write_state(state_dir, state)
        _write_report(state_dir, state)
    return state


def filter_objectives_for_review_gate(
    objectives: Iterable[Path],
    *,
    state_dir: Path,
    project_path: Path,
    stage: str,
    enabled: bool,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    """Apply the persisted gate before any formalizer/prover dispatch."""
    items = list(objectives)
    if not enabled:
        return items, []
    state = _invalidate_stale_passes(
        state_dir=state_dir,
        project_path=project_path,
        state=load_gate_state(state_dir),
    )
    canonical = stage.strip().lower()
    targets = state.get("targets", {}) if state else {}
    shared_paths: set[str] = set()
    if canonical.startswith(("prover", "polish")):
        # Shared infrastructure is a prerequisite build objective, not a
        # source-problem formalization target, so it has no target semantic
        # certificate to present at this gate.
        from .shared_infrastructure import pending_shared_infrastructure_objectives

        shared_paths = {
            item.module_path
            for item in pending_shared_infrastructure_objectives(
                state_dir=state_dir, project_path=project_path,
            )
        }
    kept: list[Path] = []
    dropped: list[tuple[Path, str]] = []
    for path in items:
        rel = _relative_file(str(path), project_path)
        if rel in shared_paths:
            kept.append(path)
            continue
        record = targets.get(rel) if rel else None
        status = str(record.get("status") or "") if isinstance(record, dict) else ""
        if canonical.startswith("autoformalize"):
            if status in {"passed", "review_exhausted"}:
                dropped.append((path, status))
            else:
                kept.append(path)
            continue

        if canonical.startswith(("prover", "polish")):
            if status == "passed":
                kept.append(path)
            else:
                reason = status or "missing formalization Review certificate"
                dropped.append((path, reason))
            continue

        kept.append(path)
    return kept, dropped


def filter_materialized_redrafts_for_dispatch(
    objectives: Iterable[Path],
    *,
    state_dir: Path,
    project_path: Path,
    stage: str,
    enabled: bool,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    """Skip hash-identical early redrafts but leave them in PROGRESS.

    The caller must not rewrite ``PROGRESS.md`` from the returned list:
    skipped targets still need the immediately following formalization
    Review. A changed/missing file fails open to a normal formalizer run.
    """
    items = list(objectives)
    if not enabled or not stage.strip().lower().startswith("autoformalize"):
        return items, []
    state = load_gate_state(state_dir)
    targets = state.get("targets", {}) if state else {}
    kept: list[Path] = []
    skipped: list[tuple[Path, str]] = []
    for path in items:
        rel = _relative_file(str(path), project_path)
        record = targets.get(rel) if isinstance(targets, dict) else None
        marker = (
            record.get("materialized_redraft")
            if isinstance(record, dict) else None
        )
        digest = (
            str(marker.get("lean_sha256") or "").strip().lower()
            if isinstance(marker, dict) else ""
        )
        result_fingerprints = (
            marker.get("task_result_fingerprints")
            if isinstance(marker, dict) else None
        )
        if (
            isinstance(record, dict)
            and record.get("status") == "retry"
            and isinstance(marker, dict)
            and marker.get("status") == "ready_for_review"
            and len(digest) == 64
            and digest == _file_sha256(project_path / rel)
            and isinstance(result_fingerprints, dict)
            and bool(result_fingerprints)
            and result_fingerprints == _task_result_fingerprints(state_dir, rel)
        ):
            skipped.append((
                path,
                "pipelined redraft already materialized; awaiting "
                "formalization Review",
            ))
        else:
            kept.append(path)
    return kept, skipped


def enforce_progress_review_gate(
    *,
    progress_file: Path,
    state_dir: Path,
    project_path: Path,
    stage: str,
    enabled: bool,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    """Filter PROGRESS objectives in place before a worker can dispatch."""
    objectives = parse_objective_files(progress_file, project_path)
    kept, dropped = filter_objectives_for_review_gate(
        objectives,
        state_dir=state_dir,
        project_path=project_path,
        stage=stage,
        enabled=enabled,
    )
    if not dropped:
        return kept, dropped

    if kept:
        mode = load_domain_profile(project_path).mode_for_stage(stage)
        mode_tag = f" [prover-mode: {mode}]" if mode else ""
        _replace_objectives(progress_file, [
            f"- **`{_relative_file(str(path), project_path)}`** — "
            f"eligible under the formalization Review gate.{mode_tag}"
            for path in kept
        ])
    else:
        _replace_objectives(progress_file, [
            "(no dispatch — every target is blocked by the formalization Review gate)"
        ])
    return kept, dropped
