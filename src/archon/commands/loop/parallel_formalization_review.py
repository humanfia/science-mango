"""Target-scoped parallel semantic Review for autoformalization."""

from __future__ import annotations

import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from archon.agent import ClaudeBackend, build_runner
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.commands.tooling.project_config import HarnessDescriptor

from .formalization_review_gate import (
    REVIEW_SCHEMA_VERSION,
    normalize_foundation_request,
)
from .parallel_review import TargetReviewOutcome, TargetReviewSpec


FORMALIZATION_REVIEW_REPORT_FILENAME = "parallel-formalization-review.json"
_REQUIRED_CHECKS = (
    "source_faithfulness",
    "derivability",
    "abstraction_sufficiency",
    "uncertainty_propagation",
    "branch_orientation",
    "countermodel_resistance",
)
_NOT_APPLICABLE_CHECKS = {"uncertainty_propagation", "branch_orientation"}
_PASS = {"pass", "passed", "approved", "review-passing", "review_passing"}
_FAIL = {
    "fail", "failed", "blocked", "partial", "needs_redraft",
    "needs redraft", "rejected",
}
_NOT_APPLICABLE = {"not_applicable", "not applicable", "n/a", "na"}
_BRIDGE_PASS = {"covered", "grounded", "encoded", "proved", "pass", "passed"}
_BRIDGE_FAIL = {"blocked", "failed", "missing", "partial", "needs_redraft"}
_FAILED_ROUTES = {"redraft", "foundation_build"}
_REDRAFT_KINDS = {
    "underdetermined_contract",
    "answer_as_assumption",
    "missing_uncertainty",
    "branch_ambiguous",
    "missing_foundational_bridge",
    "wrong_or_weakened_target",
    "other_modeling_defect",
}


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _formalization_review(row: dict) -> dict | None:
    raw = row.get("formalization_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("formalization_review")
    return raw if isinstance(raw, dict) else None


def _validate_certificate(row: dict) -> str:
    """Validate one explicit pass/fail certificate without judging its verdict."""
    top_status = str(row.get("status") or "").strip().lower()
    if top_status not in {"solved", "blocked"}:
        return f"unsupported milestone status {top_status!r}"
    raw = _formalization_review(row)
    if raw is None:
        return "formalization_review certificate is missing"
    try:
        schema = int(raw.get("schema_version") or 0)
    except (TypeError, ValueError):
        schema = 0
    if schema != REVIEW_SCHEMA_VERSION:
        return f"unsupported formalization_review schema_version {schema!r}"
    verdict = str(raw.get("status") or raw.get("verdict") or "").strip().lower()
    if verdict not in _PASS | _FAIL:
        return f"unsupported formalization_review status {verdict!r}"
    if not str(raw.get("reason") or "").strip():
        return "formalization_review reason is missing"
    if verdict in _PASS and top_status != "solved":
        return "passing formalization_review requires milestone status=solved"
    if verdict in _FAIL and top_status != "blocked":
        return "failed formalization_review requires milestone status=blocked"

    checks = raw.get("checks")
    if not isinstance(checks, dict):
        return "formalization_review checks are missing"
    has_failure = False
    for name in _REQUIRED_CHECKS:
        check = checks.get(name)
        if not isinstance(check, dict):
            return f"{name} check is missing"
        status = str(check.get("status") or "").strip().lower()
        evidence = str(check.get("evidence") or check.get("reason") or "").strip()
        allowed = _PASS | _FAIL
        if name in _NOT_APPLICABLE_CHECKS:
            allowed = allowed | _NOT_APPLICABLE
        if status not in allowed:
            return f"{name} has unsupported status {status!r}"
        if not evidence:
            return f"{name} evidence is missing"
        if status in _FAIL:
            has_failure = True

    bridges = raw.get("bridge_obligations")
    if not isinstance(bridges, list) or not bridges:
        return "bridge_obligations must contain at least one entry"
    for index, bridge in enumerate(bridges, start=1):
        if not isinstance(bridge, dict):
            return f"bridge obligation {index} is not an object"
        for key in ("claim", "carrier", "status", "evidence"):
            if not str(bridge.get(key) or "").strip():
                return f"bridge obligation {index} is missing {key}"
        status = str(bridge.get("status") or "").strip().lower()
        if status not in _BRIDGE_PASS | _BRIDGE_FAIL:
            return f"bridge obligation {index} has unsupported status {status!r}"
        if status in _BRIDGE_FAIL:
            has_failure = True

    route = str(
        raw.get("route") or ("proof" if verdict in _PASS else "redraft")
    ).strip().lower()
    redraft_kind = str(
        raw.get("redraft_kind")
        or ("not_applicable" if verdict in _PASS else "other_modeling_defect")
    ).strip().lower()
    if verdict in _PASS:
        if route != "proof":
            return "passing formalization_review requires route=proof"
        if redraft_kind != "not_applicable":
            return (
                "passing formalization_review requires "
                "redraft_kind=not_applicable"
            )
        for name in _REQUIRED_CHECKS:
            status = str(checks[name].get("status") or "").strip().lower()
            if status not in _PASS and not (
                name in _NOT_APPLICABLE_CHECKS and status in _NOT_APPLICABLE
            ):
                return f"passing verdict contradicts {name}={status!r}"
        for index, bridge in enumerate(bridges, start=1):
            status = str(bridge.get("status") or "").strip().lower()
            if status not in _BRIDGE_PASS:
                return f"passing verdict contradicts bridge {index}={status!r}"
    else:
        if route not in _FAILED_ROUTES:
            return f"failed formalization_review has unsupported route {route!r}"
        if redraft_kind not in _REDRAFT_KINDS:
            return f"unsupported redraft_kind {redraft_kind!r}"
        if route == "foundation_build":
            if redraft_kind != "missing_foundational_bridge":
                return (
                    "foundation_build requires "
                    "redraft_kind=missing_foundational_bridge"
                )
            for name in _REQUIRED_CHECKS:
                if name == "derivability":
                    continue
                status = str(
                    checks[name].get("status") or ""
                ).strip().lower()
                contract_check_passes = status in _PASS
                if name in _NOT_APPLICABLE_CHECKS:
                    contract_check_passes = (
                        contract_check_passes
                        or status in _NOT_APPLICABLE
                    )
                if not contract_check_passes:
                    return (
                        "foundation_build requires a sound target contract; "
                        f"{name} cannot be {status!r}"
                    )
            if not any(
                str(bridge.get("status") or "").strip().lower()
                in _BRIDGE_FAIL
                for bridge in bridges
            ):
                return "foundation_build requires a blocked bridge obligation"
            _request, request_error = normalize_foundation_request(
                raw.get("foundation_request")
            )
            if request_error:
                return request_error
        elif raw.get("foundation_request") not in (None, {}):
            return "foundation_request is only valid with route=foundation_build"
        if not has_failure:
            return "failed verdict has no failed check or blocked bridge"
    return ""


def load_target_formalization_milestone(
    path: Path,
    expected_rel: str,
) -> tuple[dict | None, str]:
    """Load exactly one target-bound, structurally valid semantic certificate."""
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError as exc:
        return None, f"milestone missing: {exc}"
    rows: list[dict] = []
    for line in lines:
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            return None, f"invalid milestone JSON: {exc}"
        if not isinstance(row, dict):
            return None, "milestone row is not an object"
        target = row.get("target")
        if not isinstance(target, dict):
            return None, "milestone target is missing"
        rel = str(target.get("file") or "").lstrip("./")
        if rel != expected_rel:
            return None, f"milestone target {rel!r} != {expected_rel!r}"
        error = _validate_certificate(row)
        if error:
            return None, error
        rows.append(row)
    if len(rows) != 1:
        return None, f"expected exactly one milestone row, found {len(rows)}"
    return rows[0], ""


def _result_evidence(state_dir: Path, rel: str) -> list[dict]:
    slug = "_".join(Path(rel).with_suffix("").parts)
    root = state_dir / "task_results"
    rel_path = Path(rel)
    candidates = {
        root / f"{rel_path.stem}.md",
        root / f"physics-grounding-{slug}.md",
        root / f"{rel}.md",
        root / f"{rel_path.with_suffix('')}.md",
        root / f"{rel_path.name}.md",
        root / f"{slug}.lean.md",
        root / f"{slug}.md",
    }
    existing = sorted(
        (path for path in candidates if path.is_file()),
        key=lambda path: (-path.stat().st_mtime_ns, str(path)),
    )
    return [
        {
            "path": str(path),
            "mtime_ns": path.stat().st_mtime_ns,
            "size": path.stat().st_size,
        }
        for path in existing
    ]


def build_target_formalization_review_prompt(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    target: Path,
    output_dir: Path,
    preflight: dict,
    prior_gate_record: dict | None,
) -> str:
    rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    slug = "_".join(Path(rel).with_suffix("").parts)
    chapter = project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"
    traces = [
        path for path in (
            iter_dir / "provers" / f"{slug}.jsonl",
            iter_dir / "formalizers" / f"{slug}.jsonl",
        ) if path.is_file()
    ]
    milestone = output_dir / "milestones.jsonl"
    summary = output_dir / "summary.md"
    profile = load_domain_profile(project_path)
    return f"""You are one target-scoped formalization Review worker for Archon iteration {iter_num}.

Assigned target (review only this target):
  {rel}

Read these bounded sources completely:
- Lean formalization: {target}
- {profile.display_name.title()} blueprint: {chapter}
- Formalizer traces: {json.dumps([str(path) for path in traces], ensure_ascii=False)}
- Matching task results, newest first: {json.dumps(_result_evidence(state_dir, rel), ensure_ascii=False)}
- Deterministic Lean preflight: {json.dumps(preflight, ensure_ascii=False)}
- Prior formalization gate record: {json.dumps(prior_gate_record or {}, ensure_ascii=False)}

This is semantic formalization Review, not proof Review. `sorry` proof bodies are
allowed. Decide whether the statements faithfully and derivably encode the
source without smuggling the requested answer into assumptions.

Audit all six checks independently: source_faithfulness, derivability,
abstraction_sufficiency, uncertainty_propagation, branch_orientation, and
countermodel_resistance. Every check needs concrete evidence. Only uncertainty
and branch checks may be not_applicable. Inventory every nontrivial source-to-
Lean bridge with a named carrier; a pass requires every bridge to be covered.

Choose exactly one route. A passing certificate uses route=proof. An ordinary
statement/modeling defect uses route=redraft. Use route=foundation_build only
when the intended source contract is already sound but a blocked bridge needs
one or more reusable local Lean lemmas that the current library does not
provide. Never use foundation_build to repair a weakened/wrong statement,
answer-as-assumption, missing uncertainty, or ambiguous branch.

For foundation_build, set redraft_kind=missing_foundational_bridge and provide
a target-local acyclic dependency graph. Every node needs a stable identifier,
natural-language claim, precise Lean goal/signature, dependencies, and evidence
from this target. root_nodes must identify the nodes that directly unlock the
reviewed target. The blocked bridge and dependency graph are authorization for
a separate foundation-build budget before this same target is semantically
reviewed again.

The deterministic preflight already ran. Do not run lake, Lean, leandag, broad
searches, or other agents unless preflight reports timeout/error. Do not edit
Lean, blueprint, PROGRESS.md, gate files, journals, AUTO_NOTES.md, or TO_USER.md.
Write permissions are restricted to:
- {milestone}
- {summary}

Write exactly one JSON object line to {milestone}:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<main declaration>"}},
  "status": "solved|blocked",
  "formalization_review": {{
    "schema_version": {REVIEW_SCHEMA_VERSION},
    "status": "passed|failed",
    "reason": "<specific semantic verdict>",
    "route": "proof|redraft|foundation_build",
    "redraft_kind": "not_applicable|underdetermined_contract|answer_as_assumption|missing_uncertainty|branch_ambiguous|missing_foundational_bridge|wrong_or_weakened_target|other_modeling_defect",
    "foundation_request": null,
    "checks": {{
      "source_faithfulness": {{"status": "passed|failed", "evidence": "..."}},
      "derivability": {{"status": "passed|failed", "evidence": "..."}},
      "abstraction_sufficiency": {{"status": "passed|failed", "evidence": "..."}},
      "uncertainty_propagation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "branch_orientation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "countermodel_resistance": {{"status": "passed|failed", "evidence": "..."}}
    }},
    "bridge_obligations": [{{"claim": "...", "carrier": "...", "status": "covered|blocked", "evidence": "..."}}]
  }},
  "attempts": [{{"attempt": 1, "strategy": "formalization-review", "code_tried": "", "lean_error": "", "goal_before": "", "goal_after": "", "result": "success|failed", "insight": "..."}}],
  "findings": {{"blocker": "<empty iff passed>", "verification": "...", "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-formalization-review"}},
  "next_steps": "<empty iff passed; exact redraft otherwise>"
}}

Use top-level status=solved only with formalization_review.status=passed;
otherwise use status=blocked. A failed verdict must identify at least one failed
check or blocked bridge. For route=foundation_build replace foundation_request
null with {{"root_claim": "...", "root_nodes": ["root"], "nodes":
[{{"id": "root", "claim": "...", "lean_goal": "...", "depends_on": [],
"evidence": "..."}}]}}. For all other routes leave foundation_request null.
Also write a <=12-line summary to {summary}. Return only after both files are
durable.
"""


def _run_formalization_review_worker(
    spec: TargetReviewSpec,
    *,
    project_path: Path,
    verbose_logs: bool,
    model: str | None,
    backend: ClaudeBackend,
    harness: HarnessDescriptor,
) -> TargetReviewOutcome:
    output_dir = Path(spec.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    runner_ok = False
    error = ""
    try:
        runner_ok = build_runner(
            role="review", model=model, descriptor=harness, backend=backend,
        ).run(
            spec.prompt,
            cwd=project_path,
            log_base=Path(spec.log_base),
            verbose_logs=verbose_logs,
        )
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
    milestone, validation_error = load_target_formalization_milestone(
        output_dir / "milestones.jsonl", spec.rel,
    )
    if validation_error:
        error = "; ".join(part for part in (error, validation_error) if part)
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=runner_ok,
        milestone=milestone,
        error=error,
    )


def _write_session(
    *,
    session_dir: Path,
    iter_num: int,
    outcomes: dict[str, TargetReviewOutcome],
) -> None:
    session_dir.mkdir(parents=True, exist_ok=True)
    rows = [outcomes[rel].milestone for rel in sorted(outcomes)]
    if any(row is None for row in rows):
        raise ValueError("cannot aggregate incomplete formalization Reviews")
    milestone_tmp = session_dir / "milestones.jsonl.tmp"
    milestone_tmp.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )
    milestone_tmp.replace(session_dir / "milestones.jsonl")
    passed = sum(
        str((_formalization_review(row) or {}).get("status") or "").lower() in _PASS
        for row in rows
    )
    (session_dir / "summary.md").write_text(
        f"# Parallel formalization Review session {iter_num}\n\n"
        f"- Targets: {len(rows)}\n- Passed: {passed}\n"
        f"- Failed: {len(rows) - passed}\n"
        "- Isolated per-target certificates; atomic parent aggregation.\n",
        encoding="utf-8",
    )
    recommendations = ["# Recommendations", ""]
    for rel in sorted(outcomes):
        row = outcomes[rel].milestone or {}
        raw = _formalization_review(row) or {}
        if str(raw.get("status") or "").lower() in _PASS:
            continue
        recommendations.append(f"- `{rel}` — {str(raw.get('reason') or 'redraft required')}")
    if len(recommendations) == 2:
        recommendations.append("- No formalization redrafts requested.")
    (session_dir / "recommendations.md").write_text(
        "\n".join(recommendations) + "\n", encoding="utf-8",
    )


def run_parallel_formalization_reviews(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    objectives: list[Path],
    preflight: dict,
    prior_gate_targets: dict,
    requested_jobs: int,
    max_attempts: int,
    backoff_sec: float,
    verbose_logs: bool,
    model: str | None,
    backend: ClaudeBackend,
    harness: HarnessDescriptor,
    worker_fn: Callable[..., TargetReviewOutcome] = _run_formalization_review_worker,
    executor_factory=ProcessPoolExecutor,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> dict:
    """Review formalizations concurrently and atomically publish a full batch."""
    targets = sorted({
        path.resolve().relative_to(project_path.resolve()).as_posix(): path
        for path in objectives
    }.items())
    preflight_rows = {
        str(row.get("file") or ""): row
        for row in preflight.get("targets", []) if isinstance(row, dict)
    }
    pending = {rel: path for rel, path in targets}
    outcomes: dict[str, TargetReviewOutcome] = {}
    rounds: list[dict] = []
    jobs = max(1, min(int(requested_jobs), len(pending) or 1))
    max_attempts = max(1, int(max_attempts))

    for attempt in range(1, max_attempts + 1):
        if not pending:
            break
        round_jobs = min(jobs, len(pending))
        specs: list[TargetReviewSpec] = []
        for rel, target in sorted(pending.items()):
            slug = "_".join(Path(rel).with_suffix("").parts)
            output_dir = (
                iter_dir / "formalization-review-targets" / slug
                / f"attempt-{attempt}"
            )
            specs.append(TargetReviewSpec(
                rel=rel,
                prompt=build_target_formalization_review_prompt(
                    project_path=project_path,
                    state_dir=state_dir,
                    iter_dir=iter_dir,
                    iter_num=iter_num,
                    target=target,
                    output_dir=output_dir,
                    preflight=preflight_rows.get(rel, {}),
                    prior_gate_record=prior_gate_targets.get(rel),
                ),
                output_dir=str(output_dir),
                log_base=str(output_dir / "agent"),
                attempt=attempt,
            ))
        failed: dict[str, Path] = {}
        with executor_factory(max_workers=round_jobs) as pool:
            futures = {
                pool.submit(
                    worker_fn,
                    spec,
                    project_path=project_path,
                    verbose_logs=verbose_logs,
                    model=model,
                    backend=backend,
                    harness=harness,
                ): (spec, pending[spec.rel])
                for spec in specs
            }
            for future in as_completed(futures):
                spec, target = futures[future]
                try:
                    outcome = future.result()
                except Exception as exc:
                    outcome = TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=attempt,
                        runner_ok=False,
                        milestone=None,
                        error=f"{type(exc).__name__}: {exc}",
                    )
                if outcome.milestone is None:
                    failed[spec.rel] = target
                else:
                    outcomes[spec.rel] = outcome
        rounds.append({
            "attempt": attempt,
            "jobs": round_jobs,
            "submitted": len(specs),
            "completed": len(specs) - len(failed),
            "failed": len(failed),
        })
        pending = failed
        if pending and attempt < max_attempts:
            jobs = max(1, jobs // 2)
            sleep_fn(max(0.0, float(backoff_sec)) * attempt)

    complete = not pending and len(outcomes) == len(targets)
    session_dir = state_dir / "proof-journal" / "sessions" / f"session_{iter_num}"
    if complete:
        _write_session(
            session_dir=session_dir, iter_num=iter_num, outcomes=outcomes,
        )
    report = {
        "complete": complete,
        "requested_jobs": requested_jobs,
        "targets": len(targets),
        "reviewed": len(outcomes),
        "unresolved": sorted(pending),
        "rounds": rounds,
        "session_dir": str(session_dir),
    }
    report_path = iter_dir / FORMALIZATION_REVIEW_REPORT_FILENAME
    tmp = report_path.with_suffix(report_path.suffix + ".tmp")
    tmp.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    tmp.replace(report_path)
    return report
