"""Persistent per-target gate between autoformalization and proving.

The review agent records a semantic verdict for every autoformalized target.
Failed targets are retried in ``autoformalize`` up to a configured limit.
Targets that still fail are quarantined as ``review_exhausted`` and are never
dispatched in the ``prover`` stage.  The state is deliberately independent of
``PROGRESS.md`` so ``--stage prover`` / ``--from prover`` cannot bypass it.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from archon.state import parse_objective_files
from archon.state.progress import write_stage

from .sorry_count import file_open_sorry_count


STATE_FILENAME = "formalization-review-gate.json"
REPORT_FILENAME = "FORMALIZATION_REVIEW_GATE.md"
STATE_VERSION = 1

_PASS_WORDS = {"pass", "passed", "approved", "review-passing", "review_passing"}
_FAIL_WORDS = {
    "fail", "failed", "blocked", "partial", "needs_redraft", "needs redraft",
    "not_started", "not started", "failed_retry", "rejected",
}


@dataclass(frozen=True)
class GateResult:
    passed: tuple[str, ...]
    retry: tuple[str, ...]
    exhausted: tuple[str, ...]
    reviewed: tuple[str, ...]


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
    return data


def _utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


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


def _decision_from_milestone(item: dict[str, Any]) -> tuple[str, str]:
    """Return ``(passed|failed, reason)``; missing verdict fails closed."""
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
        return "passed", reason or "formalization Review passed"
    if status in _FAIL_WORDS:
        return "failed", reason or "formalization Review failed"

    # Backward-compatible, deliberately strict fallback for old journals.
    # A legacy ``solved`` milestone is the only status strong enough to act as
    # a semantic certificate; every other/missing status stays out of proving.
    legacy = str(item.get("status") or "").strip().lower()
    findings = item.get("findings")
    blocker = ""
    if isinstance(findings, dict):
        blocker = str(findings.get("blocker") or "").strip()
    if legacy == "solved":
        return "passed", "legacy solved milestone (no explicit formalization_review field)"
    return "failed", blocker or "missing explicit formalization Review pass verdict"


def _load_milestone_decisions(
    session_dir: Path,
    project_path: Path,
) -> dict[str, tuple[str, str]]:
    path = session_dir / "milestones.jsonl"
    decisions: dict[str, list[tuple[str, str]]] = {}
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
        target = item.get("target")
        if not isinstance(target, dict):
            continue
        rel = _relative_file(str(target.get("file") or ""), project_path)
        if not rel:
            continue
        decisions.setdefault(rel, []).append(_decision_from_milestone(item))

    aggregated: dict[str, tuple[str, str]] = {}
    for rel, verdicts in decisions.items():
        failures = [reason for status, reason in verdicts if status != "passed"]
        if failures:
            aggregated[rel] = ("failed", "; ".join(dict.fromkeys(failures))[:2000])
        else:
            aggregated[rel] = ("passed", "all formalization Review entries passed")
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
        decision, reason = decisions.get(
            rel, ("failed", "review output omitted this dispatched target")
        )
        if rel in per_file_blockers:
            decision = "failed"
            reason = per_file_blockers[rel]
        elif global_blocker:
            decision = "failed"
            reason = "global physics Review blocker; no per-target pass certificate"

        old = targets.get(rel) if isinstance(targets.get(rel), dict) else {}
        reviews = int(old.get("reviews") or 0)
        if int(old.get("last_review_iter") or -1) != iter_num:
            reviews += 1
        if decision == "passed":
            status = "passed"
        elif reviews >= max_iterations:
            status = "review_exhausted"
        else:
            status = "retry"
        targets[rel] = {
            "status": status,
            "reviews": reviews,
            "last_review_iter": iter_num,
            "reason": reason,
            "updated_at": _utcnow(),
        }

    data["last_review_iter"] = iter_num
    data["updated_at"] = _utcnow()
    _write_state(state_dir, data)
    _write_report(state_dir, data)

    passed = tuple(sorted(k for k, v in targets.items() if v.get("status") == "passed"))
    retry = tuple(sorted(k for k, v in targets.items() if v.get("status") == "retry"))
    exhausted = tuple(sorted(
        k for k, v in targets.items() if v.get("status") == "review_exhausted"
    ))

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
    state = load_gate_state(state_dir)
    canonical = stage.strip().lower()
    targets = state.get("targets", {}) if state else {}
    kept: list[Path] = []
    dropped: list[tuple[Path, str]] = []
    for path in items:
        rel = _relative_file(str(path), project_path)
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
