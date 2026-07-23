"""Target-scoped parallel Review with deterministic aggregation."""

from __future__ import annotations

import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from archon.agent import ClaudeBackend, build_runner
from archon.commands.tooling.project_config import HarnessDescriptor


@dataclass(frozen=True)
class TargetReviewSpec:
    rel: str
    prompt: str
    output_dir: str
    log_base: str
    attempt: int


@dataclass(frozen=True)
class TargetReviewOutcome:
    rel: str
    attempt: int
    runner_ok: bool
    milestone: dict | None
    error: str = ""


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def load_target_milestone(path: Path, expected_rel: str) -> tuple[dict | None, str]:
    """Load exactly one well-formed milestone for ``expected_rel``."""
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
        status = str(row.get("status") or "").strip().lower()
        if status not in {"solved", "partial", "blocked", "not_started"}:
            return None, f"unsupported milestone status {status!r}"
        rows.append(row)
    if len(rows) != 1:
        return None, f"expected exactly one milestone row, found {len(rows)}"
    return rows[0], ""


def build_target_review_prompt(
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
    prover_log = iter_dir / "provers" / f"{slug}.jsonl"
    result_root = state_dir / "task_results"
    result_candidates = {
        result_root / f"{rel}.md",
        result_root / f"{Path(rel).name}.md",
        result_root / f"{slug}.lean.md",
        result_root / f"{slug}.md",
    }
    existing_results = sorted(
        (path for path in result_candidates if path.is_file()),
        key=lambda path: (-path.stat().st_mtime, str(path)),
    )
    result_evidence = [
        {
            "path": str(path),
            "mtime_ns": path.stat().st_mtime_ns,
            "size": path.stat().st_size,
        }
        for path in existing_results
    ]
    milestone = output_dir / "milestones.jsonl"
    summary = output_dir / "summary.md"
    return f"""You are one target-scoped proof Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

Read these bounded sources completely:
- Lean statement/proof: {target}
- Physics blueprint: {chapter}
- Prover trace: {prover_log}
- Matching prover task results, newest first:
  {json.dumps(result_evidence, ensure_ascii=False)}
- Deterministic Lean preflight: {json.dumps(preflight, ensure_ascii=False)}
- Prior proof Review record: {json.dumps(prior_gate_record or {}, ensure_ascii=False)}

Review the actual theorem contract and proof for:
1. direct Lean compilation and zero active sorry/admit/axiom laundering,
2. signature preservation and no weakened/trivialized statement,
3. faithful physical semantics relative to the source comments and blueprint,
4. honest use of hypotheses, units, answer choice, and numerical tolerance,
5. whether the current prover trace and newest matching task result support
   the claimed proof.

Task-result layouts can be nested or flattened. Prefer the newest matching
artifact whose contents agree with this iteration's trace. Do not fail a target
solely because an older alternate-path artifact is stale or missing. If no
matching artifact exists, use the current prover trace as primary evidence and
report the missing result as a process warning, not a semantic proof failure.

The deterministic preflight already ran. Do not run lake, Lean, leandag, or
repository-wide searches unless the supplied preflight reports timeout/error.

Write permissions are restricted to:
- {milestone}
- {summary}
Do not edit Lean, blueprint, PROGRESS.md, gate files, AUTO_NOTES.md, TO_USER.md,
or any shared journal/state file.

Write exactly one JSON object line to {milestone}. Required shape:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<reviewed declaration>"}},
  "status": "solved|partial|blocked|not_started",
  "attempts": [{{"attempt": 1, "strategy": "review", "code_tried": "",
    "lean_error": "", "goal_before": "", "goal_after": "",
    "result": "success|partial|failed", "insight": "<specific evidence>"}}],
  "findings": {{"blocker": "<empty iff solved>",
    "verification": "<concise semantic and proof audit>",
    "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-review"}},
  "next_steps": "<empty iff solved; otherwise exact repair>"
}}

Use status=solved only when all five checks pass. Missing or ambiguous evidence
must fail closed as partial/blocked. Also write a <=12-line summary to {summary}.
Return only after both files are durable on disk.
"""


def _run_review_worker(
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
    except Exception as exc:  # worker isolation; parent decides whether to retry
        error = f"{type(exc).__name__}: {exc}"
    milestone, validation_error = load_target_milestone(
        output_dir / "milestones.jsonl", spec.rel,
    )
    if validation_error:
        error = "; ".join(x for x in (error, validation_error) if x)
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=runner_ok,
        milestone=milestone,
        error=error,
    )


def write_parallel_review_session(
    *,
    session_dir: Path,
    iter_num: int,
    outcomes: dict[str, TargetReviewOutcome],
) -> None:
    """Atomically materialize the one global journal consumed by Review gates."""
    session_dir.mkdir(parents=True, exist_ok=True)
    rows = [outcomes[rel].milestone for rel in sorted(outcomes)]
    if any(row is None for row in rows):
        raise ValueError("cannot aggregate incomplete target Review outcomes")
    milestone_tmp = session_dir / "milestones.jsonl.tmp"
    milestone_tmp.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )
    milestone_tmp.replace(session_dir / "milestones.jsonl")
    counts: dict[str, int] = {}
    for row in rows:
        status = str(row.get("status") or "not_started")
        counts[status] = counts.get(status, 0) + 1
    summary = [
        f"# Parallel Review session {iter_num}",
        "",
        f"- Targets: {len(rows)}",
        "- " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())),
        "- One isolated Reviewer per target; deterministic parent aggregation.",
    ]
    (session_dir / "summary.md").write_text(
        "\n".join(summary) + "\n", encoding="utf-8",
    )
    recommendations = [
        "# Recommendations",
        "",
    ]
    for rel in sorted(outcomes):
        row = outcomes[rel].milestone or {}
        if str(row.get("status") or "") == "solved":
            continue
        findings = row.get("findings")
        blocker = (
            str(findings.get("blocker") or "")
            if isinstance(findings, dict) else ""
        )
        recommendations.append(f"- `{rel}` — {blocker or 'Review did not pass.'}")
    if len(recommendations) == 2:
        recommendations.append("- No proof retries requested.")
    (session_dir / "recommendations.md").write_text(
        "\n".join(recommendations) + "\n", encoding="utf-8",
    )


def run_parallel_target_reviews(
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
    worker_fn: Callable[..., TargetReviewOutcome] = _run_review_worker,
    executor_factory=ProcessPoolExecutor,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> dict:
    """Review targets concurrently, halving concurrency after infrastructure failures."""
    targets = sorted(
        {p.resolve().relative_to(project_path.resolve()).as_posix(): p for p in objectives}.items()
    )
    preflight_rows = {
        str(row.get("file") or ""): row
        for row in preflight.get("targets", [])
        if isinstance(row, dict)
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
            attempt_dir = iter_dir / "review-targets" / slug / f"attempt-{attempt}"
            prompt = build_target_review_prompt(
                project_path=project_path,
                state_dir=state_dir,
                iter_dir=iter_dir,
                iter_num=iter_num,
                target=target,
                output_dir=attempt_dir,
                preflight=preflight_rows.get(rel, {}),
                prior_gate_record=prior_gate_targets.get(rel),
            )
            specs.append(TargetReviewSpec(
                rel=rel,
                prompt=prompt,
                output_dir=str(attempt_dir),
                log_base=str(attempt_dir / "agent"),
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
                        rel=spec.rel, attempt=attempt, runner_ok=False,
                        milestone=None, error=f"{type(exc).__name__}: {exc}",
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
        write_parallel_review_session(
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
    report_path = iter_dir / "parallel-review.json"
    tmp = report_path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    tmp.replace(report_path)
    return report
