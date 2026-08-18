"""Per-target proof Review routing, retry accounting, and dispatch gating.

The outer Archon loop is project-scoped, so ``max_iterations`` cannot express
"give every theorem at most N reviewed proof attempts". This module persists
that missing per-file state and distinguishes a tactic-level retry from a
statement/modeling redraft or a genuine infrastructure blocker.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping

from .problem_only_review_contract import (
    ProblemOnlyReviewContractError,
    resolve_target_review_source_contract,
    stored_review_provenance_matches_current,
    validate_native_review_source_certificate,
)
from .review_source_contract import (
    normalized_review_source_certificate,
    provenance_from_review,
    source_assessment_from_review,
)
from .review_feedback import build_feedback_event, build_repair_task
from .shared_infrastructure import register_shared_infrastructure_request


STATE_FILENAME = "proof-review-gate.json"
REPORT_FILENAME = "PROOF_REVIEW_GATE.md"
AUTO_NOTES_FILENAME = "AUTO_NOTES.md"
STATE_VERSION = 2
PROOF_REVIEW_SCHEMA_VERSION = 1
PASS_STATUSES = {
    "solved", "passed", "pass", "complete", "completed", "success", "closed",
}
PROOF_REVIEW_ROUTES = {
    "solved", "retry_proof", "needs_redraft", "blocked_infrastructure",
}
REDRAFT_KINDS = {
    "underdetermined_contract",
    "answer_as_assumption",
    "missing_uncertainty",
    "branch_ambiguous",
    "missing_foundational_bridge",
    "wrong_or_weakened_target",
    "other_modeling_defect",
    "not_applicable",
}
_ROUTE_ALIASES = {
    "pass": "solved",
    "passed": "solved",
    "retry": "retry_proof",
    "proof_retry": "retry_proof",
    "redraft": "needs_redraft",
    "blocked_on_modeling": "needs_redraft",
    "blocked_on_grounding": "needs_redraft",
    "infrastructure": "blocked_infrastructure",
    "infrastructure_blocked": "blocked_infrastructure",
    "blocked_on_infrastructure": "blocked_infrastructure",
}
_NON_DISPATCH_STATUSES = {
    "solved", "proof_review_exhausted", "needs_redraft",
    "blocked_infrastructure",
}


@dataclass(frozen=True)
class ProofReviewResult:
    solved: tuple[str, ...]
    retry: tuple[str, ...]
    needs_redraft: tuple[str, ...]
    blocked_infrastructure: tuple[str, ...]
    exhausted: tuple[str, ...]
    reviewed: tuple[str, ...]


@dataclass(frozen=True)
class TargetProofReviewUpdate:
    """One idempotent proof Review transition used by target pipelines."""

    rel: str
    status: str
    route: str
    attempts: int
    reason: str
    redraft_kind: str
    applied: bool


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _relative_file(value: str, project_path: Path) -> str:
    """Return a safe project-relative Lean target, or ``""``.

    Relative milestone paths are rooted at the reviewed project, not at the
    controller's current working directory.  Resolving before ``relative_to``
    also rejects absolute paths and symlink/traversal paths that escape the
    project.  This matches the target-safety contract used by the
    formalization Review gate.
    """
    if not value:
        return ""
    path = Path(value)
    try:
        root = project_path.resolve()
        resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
        relative = resolved.relative_to(root)
    except (OSError, RuntimeError, ValueError):
        return ""
    normalized = relative.as_posix()
    if not normalized.endswith(".lean"):
        return ""
    return normalized


def load_proof_review_state(state_dir: Path) -> dict:
    path = state_dir / STATE_FILENAME
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _write_state(state_dir: Path, state: dict[str, Any]) -> None:
    path = state_dir / STATE_FILENAME
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = (json.dumps(state, ensure_ascii=False, indent=2) + "\n").encode(
        "utf-8"
    )
    tmp = path.with_suffix(path.suffix + ".tmp")
    try:
        tmp.write_bytes(payload)
        tmp.replace(path)
        return
    except PermissionError:
        # See formalization_review_gate._write_state.  The only supported
        # non-atomic layout is a controller-owned parent with this exact,
        # pre-created solver-writable regular inode.
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


def _normalize_token(value: Any) -> str:
    return str(value or "").strip().lower().replace("-", "_").replace(" ", "_")


def _finding_text(row: dict[str, Any], key: str) -> str:
    findings = row.get("findings")
    if not isinstance(findings, dict):
        return ""
    return str(findings.get(key) or "").strip()


def _proof_review_decision(
    row: dict[str, Any] | None,
) -> tuple[str, str, str, str, bool]:
    """Return route, reason, evidence, redraft kind, and schema presence.

    Legacy milestones remain compatible: a legacy pass is solved and every
    other legacy verdict is a proof retry. An explicit semantic failure always
    wins over a contradictory top-level ``solved`` status.
    """
    if not isinstance(row, dict):
        return (
            "retry_proof", "missing proof Review milestone", "",
            "not_applicable", False,
        )

    top_status = _normalize_token(row.get("status"))
    raw: Any = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")

    if raw is None:
        if top_status in PASS_STATUSES:
            return (
                "solved", f"legacy proof Review status={top_status or 'solved'}",
                "", "not_applicable", False,
            )
        blocker = _finding_text(row, "blocker")
        return (
            "retry_proof",
            blocker or f"legacy proof Review status={top_status or 'missing verdict'}",
            "", "not_applicable", False,
        )

    if isinstance(raw, dict):
        raw_route = raw.get("route") or raw.get("status") or raw.get("verdict")
        reason = str(raw.get("reason") or "").strip()
        evidence = str(raw.get("evidence") or "").strip()
        redraft_kind = _normalize_token(raw.get("redraft_kind"))
    else:
        raw_route = raw
        reason = ""
        evidence = ""
        redraft_kind = ""

    route_key = _normalize_token(raw_route)
    route = _ROUTE_ALIASES.get(route_key, route_key)
    fallback_reason = _finding_text(row, "blocker") or str(
        row.get("next_steps") or ""
    ).strip()
    if route not in PROOF_REVIEW_ROUTES:
        return (
            "retry_proof",
            reason or fallback_reason or f"invalid proof Review route={route_key or 'missing'}",
            evidence, "not_applicable", True,
        )
    if route == "solved" and top_status not in PASS_STATUSES:
        return (
            "retry_proof",
            reason or fallback_reason or (
                f"inconsistent proof Review: route=solved but status={top_status or 'missing'}"
            ),
            evidence, "not_applicable", True,
        )

    if route == "needs_redraft":
        if redraft_kind not in REDRAFT_KINDS or redraft_kind == "not_applicable":
            redraft_kind = "other_modeling_defect"
    else:
        redraft_kind = "not_applicable"
    if not reason:
        reason = fallback_reason or f"proof Review route={route}"
    return route, reason, evidence, redraft_kind, True


def proof_review_decision(
    row: dict[str, Any] | None,
) -> tuple[str, str, str, str, bool]:
    """Public, side-effect-free proof Review route normalization."""
    return _proof_review_decision(row)


def _source_validated_proof_review_decision(
    row: dict[str, Any] | None,
    *,
    project_path: Path,
    target: Path,
    expected_source_contract: Mapping[str, Any] | None = None,
) -> tuple[str, str, str, str, bool]:
    decision = _proof_review_decision(row)
    # A missing target-bound Review row is an output failure, not evidence of
    # a statement defect.  Preserve the decision contract's auditable proof
    # retry instead of trying to validate a source certificate that does not
    # exist (and potentially misrouting it as a redraft).
    if not isinstance(row, dict):
        return decision
    route, reason, evidence, _redraft_kind, _explicit = decision
    try:
        expected = (
            expected_source_contract
            if expected_source_contract is not None
            else resolve_target_review_source_contract(
                project_path=project_path,
                target=target,
                preflight=None,
            )
        )
    except ProblemOnlyReviewContractError as exc:
        error = str(exc)
        return (
            "needs_redraft",
            f"problem-only source contract validation failed: {error}",
            evidence or error,
            "other_modeling_defect",
            True,
        )
    raw: Any = row.get("proof_review") if isinstance(row, dict) else None
    if raw is None and isinstance(row, dict):
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    error = validate_native_review_source_certificate(
        raw if isinstance(raw, dict) else {},
        expected,
        passing=route == "solved",
    )
    if not error:
        return decision
    label = (
        "problem-only source contract validation failed"
        if isinstance(expected, Mapping)
        and expected.get("contract_kind") == "native_problem_input_only"
        else "official source contract validation failed"
    )
    return (
        "needs_redraft",
        f"{label}: {error}",
        evidence or error,
        "other_modeling_defect",
        True,
    )


def _milestone_source_provenance(row: dict[str, Any] | None) -> dict | None:
    if not isinstance(row, dict):
        return None
    raw: Any = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    return provenance_from_review(raw)


def _milestone_source_assessment(row: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(row, dict):
        return source_assessment_from_review(None)
    raw: Any = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    return source_assessment_from_review(raw)


def _raw_infrastructure_request(row: dict[str, Any] | None) -> Any:
    """Read the optional schema extension without breaking legacy rows."""
    if not isinstance(row, dict):
        return None
    raw = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    if not isinstance(raw, dict):
        return None
    return raw.get("infrastructure_request")


def _milestone_target_file(row: Mapping[str, Any], project_path: Path) -> str:
    """Normalize current object and legacy string target encodings."""
    target = row.get("target")
    if isinstance(target, Mapping):
        raw_file = target.get("file")
    elif isinstance(target, str):
        raw_file = target
    else:
        return ""
    return _relative_file(str(raw_file or ""), project_path)


def _load_milestones(
    session_dir: Path,
    project_path: Path,
) -> dict[str, tuple[dict[str, Any], ...]]:
    path = session_dir / "milestones.jsonl"
    rows: dict[str, list[dict[str, Any]]] = {}
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {}
    for line in lines:
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(row, dict):
            continue
        rel = _milestone_target_file(row, project_path)
        if rel:
            rows.setdefault(rel, []).append(row)
    # Preserve multiplicity so the caller can reject duplicate target-bound
    # verdicts instead of silently accepting the last one in the journal.
    return {rel: tuple(target_rows) for rel, target_rows in rows.items()}


def _write_report(state_dir: Path, state: dict) -> None:
    targets = state.get("targets", {})
    buckets: dict[str, list[str]] = {
        "solved": [],
        "retry": [],
        "needs_redraft": [],
        "blocked_infrastructure": [],
        "proof_review_exhausted": [],
    }
    for rel, record in sorted(targets.items()):
        if isinstance(record, dict):
            buckets.setdefault(
                str(record.get("status") or "retry"), []
            ).append(rel)
    lines = [
        "# Proof Review Gate",
        "",
        f"- State version: {state.get('version', STATE_VERSION)}",
        f"- Maximum reviewed proof attempts per target: {state.get('max_iterations', 3)}",
        f"- Solved: {len(buckets.get('solved', []))}",
        f"- Retry proof: {len(buckets.get('retry', []))}",
        f"- Needs statement redraft: {len(buckets.get('needs_redraft', []))}",
        f"- Infrastructure blocked: {len(buckets.get('blocked_infrastructure', []))}",
        f"- Review exhausted: {len(buckets.get('proof_review_exhausted', []))}",
        "",
    ]
    for key, title in (
        ("retry", "Retry in the next proof batch"),
        ("needs_redraft", "Return to autoformalize"),
        ("blocked_infrastructure", "Infrastructure blocked — report, do not retry"),
        ("proof_review_exhausted", "Proof Review exhausted"),
    ):
        values = buckets.get(key, [])
        if values:
            lines.extend([f"## {title}", ""])
            for rel in values:
                record = targets[rel]
                suffix = ""
                if key == "needs_redraft":
                    suffix = f"; kind={record.get('redraft_kind', 'other_modeling_defect')}"
                lines.append(
                    f"- `{rel}` — attempts {record.get('attempts', 0)}/"
                    f"{state.get('max_iterations', 3)}; "
                    f"{record.get('reason', '')}{suffix}"
                )
            lines.append("")
    (state_dir / REPORT_FILENAME).write_text(
        "\n".join(lines).rstrip() + "\n", encoding="utf-8",
    )


def _write_routing_notes(state_dir: Path, state: dict[str, Any]) -> None:
    targets = state.get("targets", {})
    if not isinstance(targets, dict):
        return
    by_status: dict[str, list[str]] = {}
    for rel, record in sorted(targets.items()):
        if isinstance(record, dict):
            by_status.setdefault(str(record.get("status") or ""), []).append(rel)
    retry = by_status.get("retry", [])
    redraft = by_status.get("needs_redraft", [])
    infrastructure = by_status.get("blocked_infrastructure", [])
    exhausted = by_status.get("proof_review_exhausted", [])
    if not retry and not redraft and not infrastructure and not exhausted:
        return

    max_iterations = int(state.get("max_iterations") or 3)
    lines = [
        "# Automated proof Review routing notes",
        "",
        "These notes are generated by the per-target proof Review gate.",
    ]
    if retry:
        lines.extend([
            "",
            "## Mandatory proof retries",
            "",
            "Schedule these tactic/lemma-level Review failures first in the next "
            "proof batch, then fill remaining concurrency slots with new targets:",
        ])
        for rel in retry:
            record = targets[rel]
            lines.append(
                f"- `{rel}` — reviewed attempt {record.get('attempts', 0)}/"
                f"{max_iterations}: {record.get('reason', '')}"
            )
    if redraft:
        lines.extend([
            "",
            "## Mandatory statement redrafts",
            "",
            "Do not send these targets back to the prover. Revoke their prior "
            "formalization pass and repair their contracts in autoformalize:",
        ])
        for rel in redraft:
            record = targets[rel]
            lines.append(
                f"- `{rel}` — {record.get('redraft_kind', 'other_modeling_defect')}: "
                f"{record.get('reason', '')}"
            )
    if infrastructure:
        lines.extend([
            "",
            "## Infrastructure blocked",
            "",
            "Do not retry these automatically; surface the missing external "
            "capability to the user:",
        ])
        for rel in infrastructure:
            lines.append(f"- `{rel}` — {targets[rel].get('reason', '')}")
    if exhausted:
        lines.extend([
            "",
            "## Proof Review exhausted",
            "",
            "Do not schedule these targets again:",
        ])
        lines.extend(f"- `{rel}`" for rel in exhausted)
    (state_dir / AUTO_NOTES_FILENAME).write_text(
        "\n".join(lines).rstrip() + "\n", encoding="utf-8",
    )


def apply_proof_review(
    *,
    state_dir: Path,
    project_path: Path,
    session_dir: Path,
    iter_num: int,
    reviewed_objectives: Iterable[Path],
    max_iterations: int,
) -> ProofReviewResult:
    """Consume one proof Review verdict for every dispatched objective."""
    max_iterations = max(1, int(max_iterations))
    state = _invalidate_stale_solved_records(
        state_dir=state_dir,
        project_path=project_path,
        state=load_proof_review_state(state_dir),
    )
    targets = state.get("targets")
    if not isinstance(targets, dict):
        targets = {}
    milestones = _load_milestones(session_dir, project_path)
    solved: list[str] = []
    retry: list[str] = []
    needs_redraft: list[str] = []
    blocked_infrastructure: list[str] = []
    exhausted: list[str] = []
    reviewed: list[str] = []
    seen: set[str] = set()
    for objective in reviewed_objectives:
        rel = _relative_file(str(objective), project_path)
        if not rel or rel in seen:
            continue
        seen.add(rel)
        previous = targets.get(rel)
        if not isinstance(previous, dict):
            previous = {}
        if str(previous.get("status") or "") in _NON_DISPATCH_STATUSES:
            continue

        milestone_rows = milestones.get(rel, ())
        row = milestone_rows[0] if len(milestone_rows) == 1 else None
        raw_status = str(row.get("status") or "") if row else ""
        if len(milestone_rows) > 1:
            route = "retry_proof"
            reason = (
                "expected exactly one target-bound proof Review milestone; "
                f"found {len(milestone_rows)}"
            )
            evidence = "duplicate target-bound milestones rejected by proof Review gate"
            redraft_kind = "not_applicable"
            explicit_route = False
        else:
            route, reason, evidence, redraft_kind, explicit_route = (
                _source_validated_proof_review_decision(
                    row,
                    project_path=project_path,
                    target=project_path / rel,
                )
            )
        try:
            prior_attempts = int(previous.get("attempts") or 0)
        except (TypeError, ValueError):
            prior_attempts = 0
        attempts = prior_attempts + 1

        if route == "solved":
            status = "solved"
            solved.append(rel)
        elif route == "needs_redraft":
            status = "needs_redraft"
            needs_redraft.append(rel)
        elif route == "blocked_infrastructure":
            status = "blocked_infrastructure"
            blocked_infrastructure.append(rel)
        elif attempts >= max_iterations:
            status = "proof_review_exhausted"
            reason = f"{reason}; maximum proof attempts reached"
            exhausted.append(rel)
        else:
            status = "retry"
            retry.append(rel)

        history = previous.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "iter": iter_num,
            "route": route,
            "resulting_status": status,
            "top_level_status": raw_status,
            "attempt": attempts,
            "reason": reason,
            "evidence": evidence,
            "redraft_kind": redraft_kind,
            "explicit_route": explicit_route,
            "reviewed_at": _utcnow(),
        })
        infrastructure_request = None
        infrastructure_request_error = ""
        if route == "blocked_infrastructure":
            infrastructure_request, infrastructure_request_error = (
                register_shared_infrastructure_request(
                    state_dir=state_dir,
                    project_path=project_path,
                    target_rel=rel,
                    raw_request=_raw_infrastructure_request(row),
                    reason=reason,
                    evidence=evidence,
                    iter_num=iter_num,
                )
            )
        targets[rel] = {
            **previous,
            "status": status,
            "attempts": attempts,
            "last_review_iter": iter_num,
            "reason": reason,
            "evidence": evidence,
            "redraft_kind": redraft_kind,
            "proof_review_schema_version": PROOF_REVIEW_SCHEMA_VERSION,
            "proof_review_route": route,
            "source_contract": _milestone_source_provenance(row),
            "blind_review_certificate": normalized_review_source_certificate(
                (
                    row.get("proof_review")
                    if isinstance(row.get("proof_review"), dict)
                    else (
                        row.get("findings", {}).get("proof_review")
                        if isinstance(row.get("findings"), dict)
                        else None
                    )
                )
                if isinstance(row, dict)
                else None
            ),
            **_milestone_source_assessment(row),
            "infrastructure_request": infrastructure_request,
            "infrastructure_request_error": infrastructure_request_error,
            "history": history[-50:],
            "updated_at": _utcnow(),
        }
        reviewed.append(rel)

    state = {
        **state,
        "version": STATE_VERSION,
        "max_iterations": max_iterations,
        "last_review_iter": iter_num,
        "updated_at": _utcnow(),
        "targets": targets,
    }
    _write_state(state_dir, state)
    _write_report(state_dir, state)
    _write_routing_notes(state_dir, state)
    return ProofReviewResult(
        solved=tuple(sorted(solved)),
        retry=tuple(sorted(retry)),
        needs_redraft=tuple(sorted(needs_redraft)),
        blocked_infrastructure=tuple(sorted(blocked_infrastructure)),
        exhausted=tuple(sorted(exhausted)),
        reviewed=tuple(sorted(reviewed)),
    )


def apply_target_proof_review(
    *,
    state_dir: Path,
    project_path: Path,
    target: Path,
    milestone: dict[str, Any],
    iter_num: int,
    max_iterations: int,
    event_id: str,
    expected_source_contract: Mapping[str, Any] | None = None,
    preflight: Mapping[str, Any] | None = None,
) -> TargetProofReviewUpdate:
    """Apply one proof Review event exactly once without routing PROGRESS.

    A target can be reviewed more than once in one outer iteration after a
    statement redraft.  A stable event id makes that sequence idempotent on
    crash/resume while preserving the normal proof-attempt budget.
    """
    max_iterations = max(1, int(max_iterations))
    rel = _relative_file(str(target), project_path)
    milestone_rel = _milestone_target_file(milestone, project_path)
    if not rel or milestone_rel != rel:
        raise ValueError(
            f"proof Review milestone target {milestone_rel!r} != {rel!r}"
        )
    if not event_id.strip():
        raise ValueError("proof Review pipeline event_id is required")

    state = _invalidate_stale_solved_records(
        state_dir=state_dir,
        project_path=project_path,
        state=load_proof_review_state(state_dir),
    )
    targets = state.get("targets")
    if not isinstance(targets, dict):
        targets = {}
    previous = targets.get(rel)
    if not isinstance(previous, dict):
        previous = {}
    history = previous.get("history")
    history = list(history) if isinstance(history, list) else []
    for entry in history:
        if isinstance(entry, dict) and entry.get("event_id") == event_id:
            return TargetProofReviewUpdate(
                rel=rel,
                status=str(previous.get("status") or "retry"),
                route=str(entry.get("route") or "retry_proof"),
                attempts=int(previous.get("attempts") or 0),
                reason=str(previous.get("reason") or ""),
                redraft_kind=str(
                    previous.get("redraft_kind") or "not_applicable"
                ),
                applied=False,
            )

    prior_status = str(previous.get("status") or "")
    if prior_status in _NON_DISPATCH_STATUSES:
        raise ValueError(
            f"proof Review target {rel} is not dispatchable: {prior_status}"
        )

    raw_status = str(milestone.get("status") or "")
    route, reason, evidence, redraft_kind, explicit_route = (
        _source_validated_proof_review_decision(
            milestone,
            project_path=project_path,
            target=target,
            expected_source_contract=expected_source_contract,
        )
    )
    try:
        prior_attempts = int(previous.get("attempts") or 0)
    except (TypeError, ValueError):
        prior_attempts = 0
    attempts = prior_attempts + 1
    if route == "solved":
        status = "solved"
    elif route == "needs_redraft":
        status = "needs_redraft"
    elif route == "blocked_infrastructure":
        status = "blocked_infrastructure"
    elif attempts >= max_iterations:
        status = "proof_review_exhausted"
        reason = f"{reason}; maximum proof attempts reached"
    else:
        status = "retry"

    source_provenance = _milestone_source_provenance(milestone)
    raw_certificate = milestone.get("proof_review")
    if not isinstance(raw_certificate, dict):
        findings = milestone.get("findings")
        raw_certificate = (
            findings.get("proof_review") if isinstance(findings, dict) else None
        )
    blind_certificate = normalized_review_source_certificate(raw_certificate)
    candidate_sha256 = hashlib.sha256(target.read_bytes()).hexdigest()
    feedback_event = build_feedback_event(
        review_kind="proof",
        candidate_sha256=candidate_sha256,
        event_id=event_id,
        iteration=iter_num,
        attempt=attempts,
        resulting_status=status,
        certificate=blind_certificate,
        route=route,
        redraft_kind=redraft_kind,
        preflight=preflight,
    )
    repair_events = previous.get("repair_events")
    repair_events = list(repair_events) if isinstance(repair_events, list) else []
    repair_events.append(feedback_event)

    history.append({
        "event_id": event_id,
        "iter": iter_num,
        "route": route,
        "resulting_status": status,
        "top_level_status": raw_status,
        "attempt": attempts,
        "reason": reason,
        "evidence": evidence,
        "redraft_kind": redraft_kind,
        "explicit_route": explicit_route,
        "reviewed_at": _utcnow(),
    })
    infrastructure_request = None
    infrastructure_request_error = ""
    if route == "blocked_infrastructure":
        infrastructure_request, infrastructure_request_error = (
            register_shared_infrastructure_request(
                state_dir=state_dir,
                project_path=project_path,
                target_rel=rel,
                raw_request=_raw_infrastructure_request(milestone),
                reason=reason,
                evidence=evidence,
                iter_num=iter_num,
            )
        )
    next_record = {
        **previous,
        "status": status,
        "attempts": attempts,
        "last_review_iter": iter_num,
        "reason": reason,
        "evidence": evidence,
        "redraft_kind": redraft_kind,
        "proof_review_schema_version": PROOF_REVIEW_SCHEMA_VERSION,
        "proof_review_route": route,
        "candidate_sha256": candidate_sha256,
        "source_contract": source_provenance,
        "blind_review_certificate": blind_certificate,
        **_milestone_source_assessment(milestone),
        "infrastructure_request": infrastructure_request,
        "infrastructure_request_error": infrastructure_request_error,
        "history": history[-50:],
        "repair_events": repair_events[-20:],
        "updated_at": _utcnow(),
    }
    next_record["repair_handoff"] = build_repair_task(
        next_record,
        review_kind="proof",
        worker_stage=("formalization" if route == "needs_redraft" else "proof"),
        candidate_sha256=candidate_sha256,
        preflight=preflight,
    )
    targets[rel] = next_record
    state = {
        **state,
        "version": STATE_VERSION,
        "max_iterations": max_iterations,
        "last_review_iter": iter_num,
        "updated_at": _utcnow(),
        "targets": targets,
    }
    _write_state(state_dir, state)
    _write_report(state_dir, state)
    _write_routing_notes(state_dir, state)
    return TargetProofReviewUpdate(
        rel=rel,
        status=status,
        route=route,
        attempts=attempts,
        reason=reason,
        redraft_kind=redraft_kind,
        applied=True,
    )


def reset_proof_review_targets_after_redraft(
    *,
    state_dir: Path,
    targets: Iterable[str],
    iter_num: int,
) -> tuple[str, ...]:
    """Re-enable proof Review only after a requested redraft passes its gate."""
    state = load_proof_review_state(state_dir)
    records = state.get("targets")
    if not isinstance(records, dict):
        return ()
    reset: list[str] = []
    for raw_rel in targets:
        rel = Path(str(raw_rel)).as_posix().lstrip("./")
        record = records.get(rel)
        if not isinstance(record, dict) or record.get("status") != "needs_redraft":
            continue
        history = record.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "iter": iter_num,
            "event": "formalization_redraft_passed",
            "prior_attempts": int(record.get("attempts") or 0),
            "reviewed_at": _utcnow(),
        })
        target = state_dir.parent / rel
        if not target.is_file():
            continue
        candidate_sha256 = hashlib.sha256(target.read_bytes()).hexdigest()
        repair_events = record.get("repair_events")
        repair_events = (
            list(repair_events) if isinstance(repair_events, list) else []
        )
        repair_events.append(build_feedback_event(
            review_kind="proof",
            candidate_sha256=candidate_sha256,
            event_id=(
                f"pipeline:{iter_num}:{rel}:formalization-redraft-passed"
            ),
            iteration=iter_num,
            attempt=0,
            resulting_status="retry",
            certificate={},
            route="retry_proof",
            redraft_kind="not_applicable",
            transition="formalization_redraft_passed",
        ))
        records[rel] = {
            **record,
            "status": "retry",
            "attempts": 0,
            "reason": (
                f"formalization redraft passed at iter {iter_num}; "
                "proof attempt budget reset"
            ),
            "evidence": "",
            "redraft_kind": "not_applicable",
            "proof_review_route": "retry_proof",
            "blind_review_certificate": {},
            "candidate_sha256": candidate_sha256,
            "source_contract": None,
            "repair_events": repair_events[-20:],
            "repair_handoff": {},
            "redraft_resolved_iter": iter_num,
            "history": history[-50:],
            "updated_at": _utcnow(),
        }
        reset.append(rel)
    if not reset:
        return ()
    state["version"] = STATE_VERSION
    state["updated_at"] = _utcnow()
    state["targets"] = records
    _write_state(state_dir, state)
    _write_report(state_dir, state)
    _write_routing_notes(state_dir, state)
    return tuple(sorted(reset))


def reopen_exhausted_proof_review_targets(
    *,
    state_dir: Path,
    targets: Iterable[str],
    iter_num: int,
    max_iterations: int,
    reason: str,
) -> tuple[str, ...]:
    """Reopen exhausted targets after an explicit proof-budget extension.

    This is an administrative transition, not a fresh proof certificate.  It
    preserves the consumed-attempt count and full Review history, records why
    the target was reopened, and requires the new budget to exceed every
    reopened target's prior attempt count.
    """
    if max_iterations < 1:
        raise ValueError("max_iterations must be positive")
    audit_reason = reason.strip()
    if not audit_reason:
        raise ValueError("reason must be non-empty")

    state = load_proof_review_state(state_dir)
    records = state.get("targets")
    if not isinstance(records, dict):
        return ()

    candidates: list[tuple[str, dict[str, Any], int]] = []
    for raw_rel in targets:
        rel = Path(str(raw_rel)).as_posix().lstrip("./")
        record = records.get(rel)
        if not isinstance(record, dict):
            continue
        if record.get("status") != "proof_review_exhausted":
            continue
        try:
            attempts = int(record.get("attempts") or 0)
        except (TypeError, ValueError):
            attempts = 0
        if max_iterations <= attempts:
            raise ValueError(
                f"new proof Review budget {max_iterations} must exceed "
                f"the {attempts} attempt(s) already used by {rel}"
            )
        candidates.append((rel, record, attempts))

    if not candidates:
        return ()

    reopened_at = _utcnow()
    reopened: list[str] = []
    for rel, record, attempts in candidates:
        history = record.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "iter": iter_num,
            "event": "proof_review_budget_extended",
            "prior_status": "proof_review_exhausted",
            "prior_attempts": attempts,
            "new_max_iterations": max_iterations,
            "reason": audit_reason,
            "reviewed_at": reopened_at,
        })
        records[rel] = {
            **record,
            "status": "retry",
            "reason": (
                f"proof Review budget extended to {max_iterations}: "
                f"{audit_reason}"
            ),
            "evidence": "",
            "history": history[-50:],
            "budget_extended_iter": iter_num,
            "updated_at": reopened_at,
        }
        reopened.append(rel)

    state["version"] = STATE_VERSION
    state["max_iterations"] = max_iterations
    state["updated_at"] = reopened_at
    state["targets"] = records
    _write_state(state_dir, state)
    _write_report(state_dir, state)
    _write_routing_notes(state_dir, state)
    return tuple(sorted(reopened))


def _invalidate_stale_solved_records(
    *,
    state_dir: Path,
    project_path: Path,
    state: dict[str, Any],
) -> dict[str, Any]:
    """Reopen chemistry proof passes after any bound input changes."""
    records = state.get("targets")
    if not isinstance(records, dict):
        return state
    changed = False
    for rel, raw_record in list(records.items()):
        if not isinstance(raw_record, dict) or raw_record.get("status") != "solved":
            continue
        fresh, reason = stored_review_provenance_matches_current(
            project_path=project_path,
            target=project_path / rel,
            provenance=raw_record.get("source_contract"),
            bind_candidate=True,
        )
        if fresh:
            continue
        history = raw_record.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "event": "source_contract_freshness_invalidated",
            "prior_status": "solved",
            "prior_attempts": int(raw_record.get("attempts") or 0),
            "reason": reason,
            "previous_official_answer_alignment": raw_record.get(
                "official_answer_alignment"
            ),
            "previous_source_inconsistency": raw_record.get(
                "source_inconsistency"
            ),
            "reviewed_at": _utcnow(),
        })
        records[rel] = {
            **raw_record,
            "status": "retry",
            "attempts": 0,
            "reason": f"proof Review certificate invalidated: {reason}",
            "evidence": "",
            "source_contract": None,
            "official_answer_alignment": None,
            "source_inconsistency": None,
            "history": history[-50:],
            "updated_at": _utcnow(),
        }
        changed = True
    if changed:
        state["targets"] = records
        state["updated_at"] = _utcnow()
        _write_state(state_dir, state)
        _write_report(state_dir, state)
        _write_routing_notes(state_dir, state)
    return state


def filter_objectives_for_proof_review_gate(
    objectives: Iterable[Path],
    *,
    state_dir: Path,
    project_path: Path,
    enabled: bool,
    stage: str | None = None,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    items = list(objectives)
    canonical_stage = str(stage or "").strip().lower()
    if not enabled or (
        stage is not None
        and not canonical_stage.startswith(("prover", "polish"))
    ):
        return items, []
    state = _invalidate_stale_solved_records(
        state_dir=state_dir,
        project_path=project_path,
        state=load_proof_review_state(state_dir),
    )
    targets = state.get("targets", {}) if state else {}
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
        record = targets.get(rel) if isinstance(targets, dict) else None
        status = str(record.get("status") or "") if isinstance(record, dict) else ""
        if status in _NON_DISPATCH_STATUSES:
            dropped.append((path, status))
        else:
            kept.append(path)
    return kept, dropped


def proof_review_prompt_block(
    *,
    state_dir: Path,
    max_iterations: int,
    enabled: bool,
) -> str:
    if not enabled:
        return ""
    state = load_proof_review_state(state_dir)
    targets = state.get("targets", {}) if state else {}
    retry = [
        (rel, record)
        for rel, record in sorted(targets.items())
        if isinstance(record, dict) and record.get("status") == "retry"
    ]
    redraft = [
        rel for rel, record in sorted(targets.items())
        if isinstance(record, dict) and record.get("status") == "needs_redraft"
    ]
    infrastructure = [
        rel for rel, record in sorted(targets.items())
        if isinstance(record, dict)
        and record.get("status") == "blocked_infrastructure"
    ]
    exhausted = [
        rel for rel, record in sorted(targets.items())
        if isinstance(record, dict)
        and record.get("status") == "proof_review_exhausted"
    ]
    lines = [
        "",
        "## Per-target proof Review routing gate",
        "",
        f"Each target may receive at most {max_iterations} reviewed proof attempts.",
        "Schedule retry targets first, then fill the batch with new eligible targets.",
        "Never schedule needs_redraft targets in prover; they stay quarantined until "
        "a new formalization Review pass resets them.",
        "Never schedule blocked_infrastructure or proof_review_exhausted targets.",
        f"Current retry targets: {len(retry)}; redraft targets: {len(redraft)}; "
        f"infrastructure blocked: {len(infrastructure)}; exhausted: {len(exhausted)}.",
    ]
    for rel, record in retry:
        lines.append(
            f"- RETRY `{rel}` — {record.get('attempts', 0)}/{max_iterations} "
            f"used; {record.get('reason', '')}"
        )
    if redraft:
        lines.append("- REDRAFT (autoformalize only): " + ", ".join(
            f"`{rel}`" for rel in redraft
        ))
    if infrastructure:
        lines.append("- INFRASTRUCTURE BLOCKED: " + ", ".join(
            f"`{rel}`" for rel in infrastructure
        ))
    if exhausted:
        lines.append(
            "- EXHAUSTED: " + ", ".join(f"`{rel}`" for rel in exhausted)
        )
    return "\n".join(lines) + "\n"
