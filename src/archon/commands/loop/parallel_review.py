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
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.commands.tooling.project_config import HarnessDescriptor

from .proof_review_gate import (
    PROOF_REVIEW_ROUTES,
    PROOF_REVIEW_SCHEMA_VERSION,
    REDRAFT_KINDS,
)
from .shared_infrastructure import load_shared_infrastructure_policy

PIPELINED_REVIEW_REPORT_FILENAME = "pipelined-review.json"
PIPELINED_REVIEW_SCHEMA_VERSION = 1


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


@dataclass(frozen=True)
class PipelinedTargetReviewConfig:
    """Configuration for Review/redraft work sharing the prover pool."""

    requested_jobs: int
    max_attempts: int = 3
    backoff_sec: float = 5.0
    preflight_timeout_sec: int = 300
    harness: HarnessDescriptor | None = None
    formalizer_harness: HarnessDescriptor | None = None
    formalization_review_enabled: bool = False
    formalization_review_max_attempts: int = 3
    formalization_review_backoff_sec: float = 5.0
    formalization_review_max_iterations: int = 3
    proof_review_max_iterations: int = 3


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _validate_proof_review_route(row: dict, status: str) -> str:
    raw = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    if not isinstance(raw, dict):
        return "milestone proof_review routing certificate is missing"
    try:
        schema_version = int(raw.get("schema_version"))
    except (TypeError, ValueError):
        schema_version = 0
    if schema_version != PROOF_REVIEW_SCHEMA_VERSION:
        return f"unsupported proof_review schema_version {schema_version!r}"
    route = str(raw.get("route") or "").strip().lower().replace("-", "_")
    if route not in PROOF_REVIEW_ROUTES:
        return f"unsupported proof_review route {route!r}"
    if not str(raw.get("reason") or "").strip():
        return "proof_review reason is missing"
    if not str(raw.get("evidence") or "").strip():
        return "proof_review evidence is missing"
    redraft_kind = str(raw.get("redraft_kind") or "").strip().lower()
    if redraft_kind not in REDRAFT_KINDS:
        return f"unsupported proof_review redraft_kind {redraft_kind!r}"
    if route == "needs_redraft" and redraft_kind == "not_applicable":
        return "needs_redraft requires a concrete redraft_kind"
    if route != "needs_redraft" and redraft_kind != "not_applicable":
        return f"route {route!r} requires redraft_kind=not_applicable"
    if route == "solved" and status != "solved":
        return "proof_review route=solved requires milestone status=solved"
    if route != "solved" and status == "solved":
        return f"proof_review route={route} contradicts milestone status=solved"
    if route in {"needs_redraft", "blocked_infrastructure"} and status != "blocked":
        return f"proof_review route={route} requires milestone status=blocked"
    if route == "retry_proof" and status not in {"partial", "blocked"}:
        return "proof_review route=retry_proof requires status=partial|blocked"
    return ""


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
        route_error = _validate_proof_review_route(row, status)
        if route_error:
            return None, route_error
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
    profile = load_domain_profile(project_path)
    shared_policy = load_shared_infrastructure_policy(project_path)
    shared_roots = [path.as_posix() for path in shared_policy.module_roots]
    blueprint_label = f"{profile.display_name.title()} blueprint"
    if profile.enforce_classical_physics_modeling:
        semantic_checks = (
            "3. faithful physical semantics relative to the source comments and blueprint,\n"
            "4. honest use of hypotheses, units, answer choice, and numerical tolerance,"
        )
    else:
        semantic_checks = (
            f"3. faithful {profile.display_name} semantics relative to the natural-language source and blueprint,\n"
            "4. honest use of every binder, hypothesis, side condition, convention, bound, and requested conclusion,"
        )
    return f"""You are one target-scoped proof Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

Read these bounded sources completely:
- Lean statement/proof: {target}
- {blueprint_label}: {chapter}
- Prover trace: {prover_log}
- Matching prover task results, newest first:
  {json.dumps(result_evidence, ensure_ascii=False)}
- Deterministic Lean preflight: {json.dumps(preflight, ensure_ascii=False)}
- Prior proof Review record: {json.dumps(prior_gate_record or {}, ensure_ascii=False)}

Review the actual theorem contract and proof for:
1. direct Lean compilation and zero active sorry/admit/axiom laundering,
2. signature preservation and no weakened/trivialized statement,
{semantic_checks}
5. whether the current prover trace and newest matching task result support
   the claimed proof.

Task-result layouts can be nested or flattened. Prefer the newest matching
artifact whose contents agree with this iteration's trace. Do not fail a target
solely because an older alternate-path artifact is stale or missing. If no
matching artifact exists, use the current prover trace as primary evidence and
report the missing result as a process warning, not a semantic proof failure.

The deterministic preflight already ran. Do not run lake, Lean, leandag, or
repository-wide searches unless the supplied preflight reports timeout/error.
The mechanical \\leanok marker sync may run after this target-scoped Review.
Judge proof validity from the Lean source and preflight; do not fail a target
solely because a blueprint \\leanok marker is temporarily stale.

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
  "proof_review": {{
    "schema_version": {PROOF_REVIEW_SCHEMA_VERSION},
    "route": "solved|retry_proof|needs_redraft|blocked_infrastructure",
    "reason": "<specific root cause>",
    "evidence": "<Lean goal/error plus contract evidence>",
    "redraft_kind": "not_applicable|underdetermined_contract|answer_as_assumption|missing_uncertainty|branch_ambiguous|missing_foundational_bridge|wrong_or_weakened_target|other_modeling_defect",
    "infrastructure_request": null
  }},
  "attempts": [{{"attempt": 1, "strategy": "review", "code_tried": "",
    "lean_error": "", "goal_before": "", "goal_after": "",
    "result": "success|partial|failed", "insight": "<specific evidence>"}}],
  "findings": {{"blocker": "<empty iff solved>",
    "verification": "<concise semantic and proof audit>",
    "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-review"}},
  "next_steps": "<empty iff solved; otherwise exact repair>"
}}

Classify root cause, not just the last Lean error:
- route=retry_proof only when the contract is faithful and derivable and the
  remaining issue is tactics, lemma search, arithmetic, elaboration, or budget;
- route=needs_redraft for an underdetermined/wrong/weakened contract,
  answer-as-assumption, missing requested output, uncertainty/branch omission,
  opaque relation without an eliminator, or missing foundational bridge;
- route=blocked_infrastructure when an indispensable gap is either a reusable
  cross-target project-local module or an unavailable external capability.
  Project-local automatic builds are enabled={shared_policy.enabled} and the
  only allowed module roots are {json.dumps(shared_roots)}. For an allowlisted
  local gap use
  {{"kind":"project_local_shared_module","module":"<root/File.lean>","declarations":["Name"]}};
  for an external package/tool use
  {{"kind":"external_dependency","package":"name"}}. The loop records but
  never installs external dependencies. Keep the optional field null/absent
  for every other route. A target-local helper is retry_proof; a missing
  statement/modeling bridge normally routes to needs_redraft. Use
  redraft_kind=not_applicable for every route except needs_redraft.

Use status=solved only when all five checks pass and route=solved. Use
status=blocked for needs_redraft or blocked_infrastructure, and partial/blocked
for retry_proof. Missing or ambiguous evidence must fail closed. Also write a
<=12-line summary to {summary}.
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


def validate_parallel_review_session(
    *,
    session_dir: Path,
    expected_rels: list[str],
) -> str:
    """Validate the durable aggregate before Review consumes it."""
    milestone_path = session_dir / "milestones.jsonl"
    try:
        lines = milestone_path.read_text(
            encoding="utf-8", errors="ignore",
        ).splitlines()
    except OSError as exc:
        return f"pipelined Review session is missing: {exc}"

    rows: dict[str, dict] = {}
    for line in lines:
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            return f"invalid pipelined Review milestone JSON: {exc}"
        if not isinstance(row, dict):
            return "pipelined Review milestone row is not an object"
        target = row.get("target")
        if not isinstance(target, dict):
            return "pipelined Review milestone target is missing"
        rel = str(target.get("file") or "").lstrip("./")
        if not rel:
            return "pipelined Review milestone file is missing"
        if rel in rows:
            return f"duplicate pipelined Review milestone for {rel!r}"
        status = str(row.get("status") or "").strip().lower()
        if status not in {"solved", "partial", "blocked", "not_started"}:
            return f"unsupported pipelined Review status {status!r}"
        route_error = _validate_proof_review_route(row, status)
        if route_error:
            return f"{rel}: {route_error}"
        rows[rel] = row

    expected = sorted(set(expected_rels))
    actual = sorted(rows)
    if actual != expected:
        return (
            "pipelined Review target mismatch: "
            f"expected={expected!r}, actual={actual!r}"
        )
    return ""


def write_pipelined_review_report(*, iter_dir: Path, report: dict) -> Path:
    """Atomically publish the hand-off consumed by :class:`ReviewPhase`."""
    path = iter_dir / PIPELINED_REVIEW_REPORT_FILENAME
    payload = {
        "schema_version": PIPELINED_REVIEW_SCHEMA_VERSION,
        **report,
    }
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(path)
    return path


def load_pipelined_review_report(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    objectives: list[Path],
) -> tuple[dict | None, str]:
    """Load a complete, exact-target pipeline hand-off or fail closed."""
    path = iter_dir / PIPELINED_REVIEW_REPORT_FILENAME
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        return None, f"pipelined Review report unavailable: {exc}"
    except json.JSONDecodeError as exc:
        return None, f"invalid pipelined Review report: {exc}"
    if not isinstance(report, dict):
        return None, "pipelined Review report is not an object"
    try:
        schema_version = int(report.get("schema_version") or 0)
        report_iteration = int(report.get("iteration") or 0)
    except (TypeError, ValueError):
        return None, "pipelined Review report has invalid numeric metadata"
    if schema_version != PIPELINED_REVIEW_SCHEMA_VERSION:
        return None, "unsupported pipelined Review report schema"
    if report_iteration != int(iter_num):
        return None, "pipelined Review report iteration mismatch"
    if report.get("complete") is not True:
        return None, "pipelined Review report is incomplete"

    expected: list[str] = []
    for objective in objectives:
        try:
            rel = objective.resolve().relative_to(project_path.resolve()).as_posix()
        except ValueError:
            rel = str(objective)
        expected.append(rel.lstrip("./"))
    expected = sorted(set(expected))
    raw_targets = report.get("target_files")
    if not isinstance(raw_targets, list):
        return None, "pipelined Review report target_files is not a list"
    actual = sorted(
        set(str(x).lstrip("./") for x in raw_targets)
    )
    if actual != expected:
        return None, (
            "pipelined Review report target mismatch: "
            f"expected={expected!r}, actual={actual!r}"
        )

    proof_expected = expected
    if str(report.get("pipeline_mode") or "") == "target_lifecycle":
        raw_settled = report.get("settled_target_files")
        if not isinstance(raw_settled, list):
            return None, "target lifecycle report settled_target_files is not a list"
        settled = sorted({
            str(item).lstrip("./") for item in raw_settled
            if str(item).strip()
        })
        if settled != expected:
            return None, (
                "target lifecycle settled-target mismatch: "
                f"expected={expected!r}, actual={settled!r}"
            )
        raw_proof_targets = report.get("proof_review_target_files")
        if not isinstance(raw_proof_targets, list):
            return None, (
                "target lifecycle report proof_review_target_files is not a list"
            )
        proof_expected = sorted({
            str(item).lstrip("./") for item in raw_proof_targets
            if str(item).strip()
        })
        if any(rel not in expected for rel in proof_expected):
            return None, "target lifecycle proof Review target is out of scope"

    session_dir = state_dir / "proof-journal" / "sessions" / f"session_{iter_num}"
    error = validate_parallel_review_session(
        session_dir=session_dir,
        expected_rels=proof_expected,
    )
    if error:
        return None, error
    return report, ""


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
