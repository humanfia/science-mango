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
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping

from archon.state import parse_objective_files
from archon.state.progress import write_stage

from .foundation_build_gate import foundation_build_is_dispatchable
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
    rel_path = Path(rel)
    candidates = {
        result_root / f"{rel}.md",
        result_root / f"{rel_path.with_suffix('')}.md",
        result_root / f"{rel_path.name}.md",
        result_root / f"{rel_path.stem}.md",
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
    }
    if failures:
        return False, "; ".join(dict.fromkeys(failures))[:2000], certificate
    return True, "structured formalization Review certificate passed", certificate


def _decision_from_milestone(
    item: dict[str, Any],
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
        valid, validation_reason, certificate = _validate_structured_review(raw)
        if not valid:
            return "failed", validation_reason, certificate
        return "passed", reason or validation_reason, certificate
    if status in _FAIL_WORDS:
        return "failed", reason or "formalization Review failed", {}

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
        decisions.setdefault(rel, []).append(_decision_from_milestone(item))

    aggregated: dict[str, tuple[str, str, dict[str, Any]]] = {}
    for rel, verdicts in decisions.items():
        failures = [
            reason for status, reason, _certificate in verdicts
            if status != "passed"
        ]
        certificate = {
            "schema_version": REVIEW_SCHEMA_VERSION,
            "milestones": [item_certificate for _, _, item_certificate in verdicts],
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
) -> tuple[dict[str, str], bool]:
    """Map deterministic blockers to files; return whether any is global."""
    per_file: dict[str, str] = {}
    global_blocker = False
    for item in blockers:
        rel = _relative_file(str(item.get("file") or ""), project_path)
        reason = str(item.get("reason") or item.get("kind") or "physics Review blocker")
        if rel:
            per_file[rel] = reason
        elif item.get("source") in {"review-agent", "physics-reviewer"}:
            global_blocker = True
    return per_file, global_blocker


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
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    tmp.replace(path)


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
        write_stage(progress_file, "autoformalize")
        _replace_objectives(progress_file, [
            f"- **`{rel}`** — Proof Review routed this target to statement redraft "
            f"({objective_details[rel][0]}): {objective_details[rel][1]} "
            "[prover-mode: physics-formalize]"
            for rel in sorted(set(reopened))
        ])
    return tuple(sorted(set(reopened)))


def reset_formalization_review_budget_after_foundation(
    *,
    state_dir: Path,
    project_path: Path,
    target: Path,
    foundation_record: Mapping[str, Any],
    iter_num: int,
    max_iterations: int,
    event_id: str,
) -> bool:
    """Open a fresh semantic-Review budget after validated foundation work."""
    if not event_id.strip():
        raise ValueError("foundation budget-reset event_id is required")
    rel = _relative_file(str(target), project_path)
    if not rel:
        raise ValueError("foundation budget-reset target is required")
    foundation_rel = _relative_file(
        str(foundation_record.get("foundation_file") or ""), project_path,
    )
    target_digest = str(foundation_record.get("target_sha256") or "")
    foundation_digest = str(
        foundation_record.get("foundation_sha256") or ""
    )
    if not (
        foundation_record.get("status") == "materialized"
        and foundation_rel
        and len(target_digest) == 64
        and len(foundation_digest) == 64
        and _file_sha256(project_path / rel) == target_digest
        and _file_sha256(project_path / foundation_rel) == foundation_digest
    ):
        raise ValueError(
            "foundation budget reset requires a current digest-bound "
            "materialized hand-off"
        )
    max_iterations = max(1, int(max_iterations))
    data = load_gate_state(state_dir) or _initial_state(max_iterations)
    data["max_iterations"] = max_iterations
    targets: dict[str, Any] = data.setdefault("targets", {})
    old = targets.get(rel)
    old = dict(old) if isinstance(old, dict) else {}
    if old.get("last_foundation_reset_event_id") == event_id:
        return False

    reset_history = old.get("budget_reset_history")
    reset_history = (
        list(reset_history) if isinstance(reset_history, list) else []
    )
    reset_history.append({
        "event_id": event_id,
        "iter": iter_num,
        "reset_at": _utcnow(),
        "cause": "validated_foundation_build",
        "previous_status": old.get("status"),
        "previous_reviews": int(old.get("reviews") or 0),
        "previous_reason": old.get("reason"),
        "previous_certificate": old.get("certificate"),
        "foundation_file": foundation_record.get("foundation_file"),
        "foundation_sha256": foundation_record.get("foundation_sha256"),
        "target_sha256": foundation_record.get("target_sha256"),
    })
    targets[rel] = {
        **old,
        "status": "retry",
        "reviews": 0,
        "reason": (
            "validated shared foundation materialized; formalization Review "
            "budget reset before target semantic re-review"
        ),
        "certificate": {},
        "redraft_kind": "missing_foundational_bridge",
        "foundation_handoff": dict(foundation_record),
        "last_foundation_reset_event_id": event_id,
        "last_foundation_reset_iter": iter_num,
        "budget_reset_history": reset_history[-20:],
        "updated_at": _utcnow(),
    }
    data["updated_at"] = _utcnow()
    _write_state(state_dir, data)
    _write_report(state_dir, data)
    return True


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
    per_file_blockers, global_blocker = _doctor_failures(blockers, project_path)

    for rel in sorted(review_scope):
        decision, reason, certificate = decisions.get(
            rel, ("failed", "review output omitted this dispatched target", {})
        )
        if rel in per_file_blockers:
            decision = "failed"
            reason = per_file_blockers[rel]
        elif global_blocker:
            decision = "failed"
            reason = "global physics Review blocker; no per-target pass certificate"

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
        write_stage(progress_file, "autoformalize")
        _replace_objectives(progress_file, [
            f"- **`{rel}`** — Redraft after failed formalization Review "
            f"({targets[rel]['reviews']}/{max_iterations} used). "
            f"[prover-mode: physics-formalize]"
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
            _replace_objectives(progress_file, [
                f"- **`{rel}`** — Formalization Review passed; prove remaining obligations."
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
        decision, reason, certificate = _decision_from_milestone(milestone)
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


def filter_objectives_for_review_gate(
    objectives: Iterable[Path],
    *,
    state_dir: Path,
    project_path: Path,
    stage: str,
    enabled: bool,
    foundation_build_enabled: bool = False,
    foundation_build_max_iterations: int = 3,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    """Apply the persisted gate before any formalizer/prover dispatch."""
    items = list(objectives)
    if not enabled:
        return items, []
    state = load_gate_state(state_dir)
    canonical = stage.strip().lower()
    targets = state.get("targets", {}) if state else {}
    kept: list[Path] = []
    dropped: list[tuple[Path, str]] = []
    for path in items:
        rel = _relative_file(str(path), project_path)
        record = targets.get(rel) if rel else None
        status = str(record.get("status") or "") if isinstance(record, dict) else ""
        if foundation_build_enabled and foundation_build_is_dispatchable(
            state_dir=state_dir,
            project_path=project_path,
            target_rel=rel,
            max_iterations=foundation_build_max_iterations,
        ):
            kept.append(path)
            continue
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
    foundation_build_enabled: bool = False,
    foundation_build_max_iterations: int = 3,
) -> tuple[list[Path], list[tuple[Path, str]]]:
    """Filter PROGRESS objectives in place before a worker can dispatch."""
    objectives = parse_objective_files(progress_file, project_path)
    kept, dropped = filter_objectives_for_review_gate(
        objectives,
        state_dir=state_dir,
        project_path=project_path,
        stage=stage,
        enabled=enabled,
        foundation_build_enabled=foundation_build_enabled,
        foundation_build_max_iterations=foundation_build_max_iterations,
    )
    if not dropped:
        return kept, dropped

    if kept:
        _replace_objectives(progress_file, [
            f"- **`{_relative_file(str(path), project_path)}`** — "
            "eligible under the formalization Review gate."
            for path in kept
        ])
    else:
        _replace_objectives(progress_file, [
            "(no dispatch — every target is blocked by the formalization Review gate)"
        ])
    return kept, dropped
