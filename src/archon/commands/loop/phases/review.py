"""Review phase: extract attempts, run review agent, validate output."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

from archon import log
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.commands.tooling.iteration import commit_phase
from archon.commands.tooling.project_config import (
    load_project_config,
    resolve_recent_iter_window,
    resolve_subagents_enabled,
)
from archon.prompt_compression import (
    PromptCompressionConfig,
    compress_prompt,
    write_prompt_compression_report,
)
from archon.phase_input_summary import build_review_input_pack
from archon.prompts import build_review_prompt
from archon.state import normalize_stage_for_prompt_path, parse_objective_files
from archon.state import write_meta
from archon.state.progress import is_complete, write_stage
from archon.state.progress import read_stage
from archon.subagents.audit import check_mandatory_dispatched

from ..formalization_review_gate import (
    GateResult,
    _replace_objectives,
    apply_formalization_review,
    load_gate_state as load_formalization_review_state,
    reopen_formalization_targets,
)
from ..parallel_formalization_review import (
    FORMALIZATION_REVIEW_REPORT_FILENAME,
    run_parallel_formalization_reviews,
)
from ..parallel_review import (
    load_pipelined_review_report,
    run_parallel_target_reviews,
)
from ..numeric_reporting_guard import numeric_reporting_blockers
from ..proof_review_gate import (
    ProofReviewResult,
    apply_proof_review,
    load_proof_review_state,
)
from ..review_preflight import (
    deterministic_review_prompt_prefix,
    run_parallel_review_preflight,
    write_deterministic_review_pack,
)
from ..resume import REVIEW_CONTINUE, persist_session_id, pick_resume_session
from ..utils import data_path
from .base import Phase, PhaseResult


PHYSICS_DOCTOR_BLOCKER_KEYS = (
    "physics_modeling_problems",
    "physics_grounding_problems",
)
PHYSICS_REVIEWER_BLOCKING_VERDICTS = (
    "BLOCKED ON MODELING",
    "BLOCKED ON GROUNDING",
    "NEEDS REDRAFT",
)
PHYSICS_REVIEWER = "physics-reviewer"
CHEMISTRY_REVIEWER = "chemistry-reviewer"
AUTO_NOTES_FILENAME = "AUTO_NOTES.md"


def _load_physics_doctor_blockers(
    state_dir: Path,
    iter_num: int,
) -> list[dict[str, str]]:
    """Load current-iter physics doctor blockers from the JSON sidecar."""
    json_path = state_dir / "logs" / f"iter-{iter_num:03d}" / "blueprint-doctor.json"
    try:
        data = json.loads(json_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    if not isinstance(data, dict):
        return []

    blockers: list[dict[str, str]] = []
    for key in PHYSICS_DOCTOR_BLOCKER_KEYS:
        raw_items = data.get(key, []) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            blockers.append({
                "source": key,
                "file": str(item.get("file") or ""),
                "kind": str(item.get("kind") or ""),
                "reason": str(item.get("reason") or ""),
            })
    return blockers


def _markdown_section_lines(text: str, heading: str) -> list[str]:
    target = heading.strip().lower()
    lines: list[str] = []
    in_section = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.lower() == target:
            in_section = True
            continue
        if in_section and stripped.startswith("## "):
            break
        if in_section:
            lines.append(line)
    return lines


def _first_nonempty(lines: list[str]) -> str:
    for line in lines:
        stripped = line.strip()
        if stripped:
            return stripped
    return ""


def _extract_physics_reviewer_verdict(text: str) -> str:
    verdict_line = _first_nonempty(
        _markdown_section_lines(text, "## Overall verdict")
    )
    return _find_blocking_verdict(verdict_line)


def _find_blocking_verdict(text: str) -> str:
    upper = text.upper()
    for verdict in PHYSICS_REVIEWER_BLOCKING_VERDICTS:
        if verdict in upper:
            return verdict
    return ""


def _is_substantive_must_fix(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    low = stripped.lower()
    bullet = re.match(r"^[-*]\s+(.*)$", low)
    if not bullet:
        return False
    content = bullet.group(1).strip().rstrip(".;:").strip()
    if content in {"none", "n/a", "na"}:
        return False
    if "<finding" in content or "<file" in content:
        return False
    return bool(content)


def _extract_physics_reviewer_must_fixes(text: str) -> list[str]:
    return [
        line.strip()
        for line in _markdown_section_lines(text, "## Must-fix-this-iter")
        if _is_substantive_must_fix(line)
    ]


def _reviewer_for_project(project_path: Path) -> str:
    """Select the semantics reviewer paired with the project's domain profile."""
    if load_domain_profile(project_path).name == "chemistry":
        return CHEMISTRY_REVIEWER
    return PHYSICS_REVIEWER


def _load_reviewer_blockers(
    state_dir: Path,
    reviewer: str,
) -> list[dict[str, str]]:
    """Load blocking verdicts or must-fixes from one reviewer kind."""
    task_results = state_dir / "task_results"
    if not task_results.is_dir():
        return []

    blockers: list[dict[str, str]] = []
    for report in sorted(task_results.rglob(f"{reviewer}-*.md")):
        try:
            text = report.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        verdict = _extract_physics_reviewer_verdict(text)
        must_fixes = _extract_physics_reviewer_must_fixes(text)
        if not verdict and not must_fixes:
            continue

        reason_parts: list[str] = []
        if verdict:
            reason_parts.append(f"overall verdict: {verdict}")
        if must_fixes:
            reason_parts.append("must-fix: " + " ".join(must_fixes[:3]))
            if len(must_fixes) > 3:
                reason_parts.append(f"... and {len(must_fixes) - 3} more")

        blockers.append({
            "source": reviewer,
            "file": str(report),
            "kind": verdict or "must-fix-this-iter",
            "reason": "; ".join(reason_parts),
        })
    return blockers


def _load_domain_reviewer_blockers(
    state_dir: Path,
    project_path: Path | None = None,
) -> list[dict[str, str]]:
    """Load reports from the reviewer selected by the project domain profile."""
    project = project_path if project_path is not None else state_dir.parent
    return _load_reviewer_blockers(state_dir, _reviewer_for_project(project))


def _load_physics_reviewer_blockers(state_dir: Path) -> list[dict[str, str]]:
    """Load physics-reviewer blockers (legacy helper kept for compatibility)."""
    return _load_reviewer_blockers(state_dir, PHYSICS_REVIEWER)


def _first_matching_line(text: str, needle: str) -> str:
    needle_upper = needle.upper()
    for line in text.splitlines():
        if needle_upper in line.upper():
            return line.strip()
    return ""


def _load_physics_session_review_blockers(
    state_dir: Path,
    iter_num: int,
) -> list[dict[str, str]]:
    """Load blocker verdicts written by the main review agent this iter."""
    sessions = [
        state_dir / "proof-journal" / "sessions" / f"session_{iter_num}",
        state_dir / "proof-journal" / "sessions" / f"session_{iter_num:03d}",
    ]
    blockers: list[dict[str, str]] = []
    seen: set[Path] = set()
    for session_dir in sessions:
        for name in ("summary.md", "recommendations.md"):
            path = session_dir / name
            if path in seen:
                continue
            seen.add(path)
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            verdict = _find_blocking_verdict(text)
            if not verdict:
                continue
            reason = _first_matching_line(text, verdict) or f"overall verdict: {verdict}"
            blockers.append({
                "source": "review-agent",
                "file": str(path),
                "kind": verdict,
                "reason": reason,
            })
    return blockers


def _physics_blocker_label(source: str) -> str:
    if source in PHYSICS_DOCTOR_BLOCKER_KEYS:
        return "physics-doctor"
    return source or "physics-review-gate"


def _append_physics_review_auto_note(
    notes_file: Path,
    blockers: list[dict[str, str]],
) -> None:
    """Write the legacy physics gate note."""
    _append_domain_review_auto_note(notes_file, blockers, domain_name="physics")


def _append_domain_review_auto_note(
    notes_file: Path,
    blockers: list[dict[str, str]],
    *,
    domain_name: str,
) -> None:
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    sources = sorted({
        _physics_blocker_label(item.get("source") or "")
        for item in blockers
    })
    if len(sources) == 1:
        label = sources[0]
    else:
        label = f"{domain_name}-review-gate"
    lines = [
        f"\n- [{ts}] archon[{label}]: current review found "
        f"{len(blockers)} {domain_name} blocker(s), so the project must not "
        f"mark COMPLETE until these are repaired. The review gate reset "
        f"the stage to `autoformalize` for statement redraft:",
    ]
    for item in blockers[:8]:
        source = _physics_blocker_label(item.get("source") or "")
        file_part = item.get("file") or "(unknown file)"
        kind = item.get("kind") or "(unknown kind)"
        reason = item.get("reason") or "(no reason)"
        lines.append(f"  - {source}: {file_part} — {kind}: {reason}")
    if len(blockers) > 8:
        lines.append(f"  - ... and {len(blockers) - 8} more")
    note = "\n".join(lines) + "\n"
    notes_file.parent.mkdir(parents=True, exist_ok=True)
    existing = ""
    if notes_file.exists():
        try:
            existing = notes_file.read_text(encoding="utf-8")
        except OSError:
            pass
    notes_file.write_text(existing + note, encoding="utf-8")


def _enforce_domain_review_blocker_gate(
    state_dir: Path,
    progress_file: Path,
    iter_num: int,
    *,
    project_path: Path | None = None,
) -> tuple[list[dict[str, str]], bool]:
    """Prevent profile-selected semantics blockers from hiding behind COMPLETE."""
    project = project_path if project_path is not None else state_dir.parent
    profile = load_domain_profile(project)
    blockers = (
        _load_physics_doctor_blockers(state_dir, iter_num)
        + _load_reviewer_blockers(
            state_dir,
            _reviewer_for_project(project),
        )
        + _load_physics_session_review_blockers(state_dir, iter_num)
    )
    if not blockers:
        return blockers, False
    if not is_complete(progress_file):
        return blockers, False

    write_stage(progress_file, "autoformalize")
    _append_domain_review_auto_note(
        state_dir / AUTO_NOTES_FILENAME,
        blockers,
        domain_name=profile.name,
    )
    return blockers, True


def _enforce_physics_review_blocker_gate(
    state_dir: Path,
    progress_file: Path,
    iter_num: int,
    *,
    project_path: Path | None = None,
) -> tuple[list[dict[str, str]], bool]:
    """Backward-compatible name for the profile-aware semantics review gate."""
    return _enforce_domain_review_blocker_gate(
        state_dir,
        progress_file,
        iter_num,
        project_path=project_path,
    )


def _enforce_physics_doctor_blocker_gate(
    state_dir: Path,
    progress_file: Path,
    iter_num: int,
    *,
    project_path: Path | None = None,
) -> tuple[list[dict[str, str]], bool]:
    """Backward-compatible alias for the broader physics review gate."""
    return _enforce_physics_review_blocker_gate(
        state_dir,
        progress_file,
        iter_num,
        project_path=project_path,
    )


def _maybe_compress_review_prompt(
    ctx, prompt: str, *, force: bool = False,
) -> str:
    if not ctx.options.compress_plan_review_inputs and not force:
        return prompt
    result = compress_prompt(
        prompt,
        role="review",
        config=PromptCompressionConfig(
            enabled=True,
            target_chars=ctx.options.prompt_compression_target_chars,
            section_chars=ctx.options.prompt_compression_section_chars,
        ),
    )
    report = result.report
    if ctx.iter_dir is not None:
        try:
            write_prompt_compression_report(
                ctx.iter_dir / "prompt-compression-review.json",
                report,
            )
        except OSError as e:
            log.warn(f"could not write review prompt compression report: {e}")
    if ctx.iter_meta is not None:
        write_meta(
            ctx.iter_meta,
            **{
                "review.promptOriginalChars": report.original_chars,
                "review.promptCompressedChars": report.compressed_chars,
                "review.promptCompressionOmittedChars": report.omitted_chars,
                "review.promptCompressionChanged": report.changed,
            },
        )
    if report.changed:
        log.info(
            "Review prompt compression: "
            f"{report.original_chars} -> {report.compressed_chars} chars "
            f"({report.omitted_chars} omitted)"
        )
    else:
        log.info(
            f"Review prompt compression enabled; no eligible section changed "
            f"({report.original_chars} chars)."
        )
    return result.prompt


class ReviewPhase(Phase):
    name = "Review agent"
    number = 3
    skip_token = "review"

    def run(self) -> PhaseResult:
        ctx = self.ctx
        formalization_gate_active = (
            ctx.options.formalization_review_gate
            and normalize_stage_for_prompt_path(ctx.current_stage) == "autoformalize"
        )
        reviewed_objectives = (
            parse_objective_files(ctx.progress_file, ctx.project_path)
            if formalization_gate_active else []
        )
        proof_gate_active = (
            getattr(ctx.options, "proof_review_gate", False)
            and normalize_stage_for_prompt_path(ctx.current_stage) == "prover"
        )
        proof_reviewed_objectives = (
            parse_objective_files(ctx.progress_file, ctx.project_path)
            if proof_gate_active else []
        )

        if self.skip_token in ctx.skip_now:
            log.phase(self.number, f"{self.name} — skipped (--from)")
            return PhaseResult(skipped=True)

        if ctx.dry_run:
            return PhaseResult(skipped=True)
        if ctx.options.no_review:
            if formalization_gate_active:
                log.error(
                    "formalization Review gate is enabled, but Review is disabled; "
                    "targets will remain uncertified and cannot enter prover"
                )
                write_meta(ctx.iter_meta, **{
                    "review.formalizationGateStatus": "review_required",
                })
            self._run_physics_doctor_gate()
            return PhaseResult(skipped=True)

        log.phase(self.number, self.name)
        review_start = time.monotonic()
        write_meta(ctx.iter_meta, **{"review.status": "running"})

        self._review_preflight_path: Path | None = None
        self._review_candidate_pack: Path | None = None
        self._review_preflight: dict | None = None
        cfg = load_project_config(ctx.project_path)
        loop_cfg = cfg.loop_section()
        deterministic_review = bool(loop_cfg.get("deterministic_review", False))
        exact_objectives = (
            proof_reviewed_objectives
            or reviewed_objectives
            or parse_objective_files(ctx.progress_file, ctx.project_path)
        )
        from ..shared_infrastructure import pending_shared_infrastructure_objectives

        pending_shared_paths = {
            (ctx.project_path / item.module_path).resolve()
            for item in pending_shared_infrastructure_objectives(
                state_dir=getattr(
                    ctx, "state_dir", ctx.project_path / ".archon"
                ),
                project_path=ctx.project_path,
            )
        }
        if exact_objectives and all(
            path.resolve() in pending_shared_paths for path in exact_objectives
        ):
            # These files are governed by the mandatory axiom sweep + full
            # Lake build lifecycle. Ordinary problem Review requires source
            # contracts/blueprints and can incorrectly route infrastructure to
            # statement redraft, so it must not consume this isolated batch.
            review_secs = int(time.monotonic() - review_start)
            log.info(
                "Review skipped for isolated shared-infrastructure batch; "
                "axiom/build verification owns the verdict."
            )
            write_meta(ctx.iter_meta, **{
                # Resume detection treats only status=done as terminal. Keep
                # the specialized outcome separately so --resume can reach
                # Plan, where queue reconciliation happens.
                "review.status": "done",
                "review.outcome": "shared_infrastructure_deferred",
                "review.durationSecs": review_secs,
                "review.sharedInfrastructureTargets": len(exact_objectives),
            })
            commit_phase(
                ctx.project_path,
                iter_num=ctx.iter_num,
                phase="review",
                summary=f"shared infrastructure gate ({review_secs}s)",
            )
            return PhaseResult(skipped=True)
        parallel_target_review = (
            deterministic_review
            and proof_gate_active
            and bool(loop_cfg.get("parallel_target_review", False))
        )
        parallel_formalization_review = (
            deterministic_review
            and formalization_gate_active
            and bool(loop_cfg.get("parallel_formalization_review", False))
        )
        pipelined_report = None
        pipeline_requested = (
            bool(loop_cfg.get("pipeline_target_review", False))
            and ctx.iter_dir is not None
            and (
                parallel_target_review
                or (
                    formalization_gate_active
                    and parallel_formalization_review
                    and getattr(ctx.options, "proof_review_gate", False)
                    and bool(loop_cfg.get("parallel_target_review", False))
                )
            )
        )
        pipeline_objectives = (
            proof_reviewed_objectives
            if proof_gate_active else reviewed_objectives
        )
        if pipeline_requested:
            report_path = ctx.iter_dir / "pipelined-review.json"
            if report_path.exists():
                pipelined_report, pipeline_error = load_pipelined_review_report(
                    project_path=ctx.project_path,
                    state_dir=ctx.state_dir,
                    iter_dir=ctx.iter_dir,
                    iter_num=ctx.iter_num,
                    objectives=pipeline_objectives,
                )
                if pipeline_error:
                    log.warn(
                        f"pipelined Review hand-off rejected: {pipeline_error}; "
                        "falling back to the normal target Review batch"
                    )
                else:
                    self._review_preflight = pipelined_report.get("preflight", {})
                    summary = self._review_preflight.get("summary", {})
                    log.success(
                        "consuming target Reviews produced during prover fanout: "
                        f"{pipelined_report.get('reviewed', 0)}/"
                        f"{pipelined_report.get('targets', 0)}"
                    )
                    write_meta(ctx.iter_meta, **{
                        "review.pipelineTargetConsumed": True,
                        "review.pipelineTargetReport": str(report_path),
                        "review.deterministic": True,
                        "review.preflightJobs": self._review_preflight.get("jobs", 1),
                        "review.preflightDurationSecs": self._review_preflight.get(
                            "duration_secs", 0.0,
                        ),
                        "review.preflightPassed": summary.get("passed", 0),
                        "review.preflightFailed": summary.get("failed", 0),
                    })

        if (
            deterministic_review
            and exact_objectives
            and ctx.iter_dir is not None
            and pipelined_report is None
        ):
            jobs = int(
                loop_cfg.get(
                    "review_preflight_jobs", ctx.options.max_parallel
                )
            )
            timeout_sec = int(
                loop_cfg.get("review_preflight_timeout_sec", 3600)
            )
            preflight = run_parallel_review_preflight(
                project_path=ctx.project_path,
                objectives=exact_objectives,
                iter_dir=ctx.iter_dir,
                iter_num=ctx.iter_num,
                jobs=jobs,
                timeout_sec=timeout_sec,
            )
            self._review_preflight = preflight
            self._review_preflight_path = preflight["md_path"]
            self._review_candidate_pack = write_deterministic_review_pack(
                project_path=ctx.project_path,
                state_dir=ctx.state_dir,
                iter_dir=ctx.iter_dir,
                iter_num=ctx.iter_num,
                objectives=exact_objectives,
                preflight=preflight,
            )
            summary = preflight["summary"]
            log.info(
                "parallel Review preflight: "
                f"{summary['passed']} passed / {summary['failed']} failed "
                f"across {summary['total']} target(s) "
                f"in {preflight['duration_secs']:.3f}s"
            )
            write_meta(ctx.iter_meta, **{
                "review.deterministic": True,
                "review.preflightJobs": preflight["jobs"],
                "review.preflightDurationSecs": preflight["duration_secs"],
                "review.preflightPassed": summary["passed"],
                "review.preflightFailed": summary["failed"],
                "review.preflightPath": str(self._review_preflight_path),
                "review.candidatePackPath": str(self._review_candidate_pack),
            })

        if pipelined_report is not None:
            review_ok = True
        elif parallel_target_review:
            review_ok = self._invoke_parallel_target_review(
                proof_reviewed_objectives,
                cfg=cfg,
            )
        elif parallel_formalization_review:
            review_ok = self._invoke_parallel_formalization_review(
                reviewed_objectives,
                cfg=cfg,
            )
        else:
            review_ok = self._invoke_review()
        if not review_ok:
            review_secs = int(time.monotonic() - review_start)
            write_meta(ctx.iter_meta, **{
                "review.status": "error",
                "review.durationSecs": review_secs,
                "review.error": (
                    "review batch remained incomplete; unresolved targets "
                    "were not accepted"
                ),
            })
            raise RuntimeError(
                "Review batch remained incomplete; refusing to apply "
                "unresolved target verdicts or continue"
            )
        blockers, reset_complete = self._run_physics_doctor_gate()
        reporting_blockers = numeric_reporting_blockers(self._review_preflight)
        blockers.extend(reporting_blockers)
        formalization_result = None
        proof_result = None
        proof_redrafts_reopened: tuple[str, ...] = ()
        pipeline_gates_applied = (
            isinstance(pipelined_report, dict)
            and pipelined_report.get("gate_events_applied") is True
        )
        pipeline_lifecycle = (
            isinstance(pipelined_report, dict)
            and pipelined_report.get("pipeline_mode") == "target_lifecycle"
        )

        def pipeline_items(raw_gate: dict, name: str) -> tuple[str, ...]:
            raw_items = raw_gate.get(name, [])
            if not isinstance(raw_items, list):
                return ()
            return tuple(sorted({
                str(item).lstrip("./")
                for item in raw_items
                if str(item).strip()
            }))

        if formalization_gate_active:
            if pipeline_gates_applied and pipeline_lifecycle:
                raw_formalization_gate = pipelined_report.get(
                    "formalization_gate_result", {}
                )
                raw_formalization_gate = (
                    raw_formalization_gate
                    if isinstance(raw_formalization_gate, dict) else {}
                )
                formalization_result = GateResult(
                    passed=pipeline_items(raw_formalization_gate, "passed"),
                    retry=pipeline_items(raw_formalization_gate, "retry"),
                    exhausted=pipeline_items(raw_formalization_gate, "exhausted"),
                    reviewed=pipeline_items(raw_formalization_gate, "reviewed"),
                )
                log.info(
                    "consuming per-target formalization gate events: "
                    f"passed={len(formalization_result.passed)}, "
                    f"retry={len(formalization_result.retry)}, "
                    f"exhausted={len(formalization_result.exhausted)}"
                )
            else:
                formalization_result = apply_formalization_review(
                    state_dir=ctx.state_dir,
                    project_path=ctx.project_path,
                    progress_file=ctx.progress_file,
                    session_dir=(
                        ctx.state_dir / "proof-journal" / "sessions"
                        / f"session_{ctx.iter_num}"
                    ),
                    iter_num=ctx.iter_num,
                    reviewed_objectives=reviewed_objectives,
                    max_iterations=ctx.options.formalization_review_max_iterations,
                    blockers=blockers,
                )
                ctx.current_stage = read_stage(ctx.progress_file)
                log.info(
                    "formalization Review gate: "
                    f"passed={len(formalization_result.passed)}, "
                    f"retry={len(formalization_result.retry)}, "
                    f"exhausted={len(formalization_result.exhausted)}; "
                    f"next stage={ctx.current_stage}"
                )
        if proof_gate_active or (
            pipeline_lifecycle and pipeline_gates_applied
        ):
            if pipeline_gates_applied:
                raw_gate = pipelined_report.get("proof_gate_result", {})
                raw_gate = raw_gate if isinstance(raw_gate, dict) else {}
                proof_result = ProofReviewResult(
                    solved=pipeline_items(raw_gate, "solved"),
                    retry=pipeline_items(raw_gate, "retry"),
                    needs_redraft=pipeline_items(raw_gate, "needs_redraft"),
                    blocked_infrastructure=pipeline_items(
                        raw_gate, "blocked_infrastructure"
                    ),
                    exhausted=pipeline_items(raw_gate, "exhausted"),
                    reviewed=pipeline_items(raw_gate, "reviewed"),
                )
                raw_reopened = pipelined_report.get(
                    "proof_redrafts_reopened", []
                )
                if isinstance(raw_reopened, list):
                    proof_redrafts_reopened = tuple(sorted({
                        str(item).lstrip("./")
                        for item in raw_reopened
                        if str(item).strip()
                    }))
                raw_pending = pipelined_report.get(
                    "pending_formalization_targets", []
                )
                pending_formalization = (
                    tuple(sorted({
                        str(item).lstrip("./")
                        for item in raw_pending
                        if str(item).strip()
                    }))
                    if isinstance(raw_pending, list)
                    else ()
                )
                if pending_formalization:
                    formalize_mode = (
                        load_domain_profile(ctx.project_path).mode_for_stage(
                            "autoformalize"
                        )
                        or "physics-formalize"
                    )
                    write_stage(ctx.progress_file, "autoformalize")
                    _replace_objectives(ctx.progress_file, [
                        f"- **`{rel}`** — Resume the target-local redraft "
                        "that could not finish inside the prover pipeline. "
                        f"[prover-mode: {formalize_mode}]"
                        for rel in pending_formalization
                    ])
                    ctx.current_stage = read_stage(ctx.progress_file)
                    log.warn(
                        "target pipeline left "
                        f"{len(pending_formalization)} formalization(s) "
                        "for the normal autoformalize fallback"
                    )
                elif pipeline_lifecycle and formalization_gate_active:
                    write_stage(ctx.progress_file, "prover")
                    if proof_result.retry:
                        proof_mode = (
                            load_domain_profile(ctx.project_path).mode_for_stage(
                                "prover"
                            )
                            or "physics"
                        )
                        _replace_objectives(ctx.progress_file, [
                            f"- **`{rel}`** — Continue the target-local proof "
                            "retry requested by Proof Review. "
                            f"[prover-mode: {proof_mode}]"
                            for rel in proof_result.retry
                        ])
                    else:
                        _replace_objectives(ctx.progress_file, [
                            "(no dispatch — selected target lifecycles are "
                            "settled; plan the next eligible frontier)"
                        ])
                    ctx.current_stage = read_stage(ctx.progress_file)
                    log.success(
                        "target lifecycle batch has no pending "
                        "formalization; continuing in prover stage"
                    )
                write_meta(ctx.iter_meta, **{
                    "review.pipelineGateEventsConsumed": True,
                    "review.pipelineFormalizationPending": len(
                        pending_formalization
                    ),
                })
            else:
                proof_result = apply_proof_review(
                    state_dir=ctx.state_dir,
                    project_path=ctx.project_path,
                    session_dir=(
                        ctx.state_dir / "proof-journal" / "sessions"
                        / f"session_{ctx.iter_num}"
                    ),
                    iter_num=ctx.iter_num,
                    reviewed_objectives=proof_reviewed_objectives,
                    max_iterations=getattr(
                        ctx.options, "proof_review_max_iterations", 3,
                    ),
                    deterministic_blockers={
                        str(item.get("file") or ""): str(item.get("reason") or "")
                        for item in reporting_blockers
                        if str(item.get("file") or "").strip()
                        and item.get("kind") == "invalid_reporting_certificate"
                    },
                    deterministic_retry_blockers={
                        str(item.get("file") or ""): str(item.get("reason") or "")
                        for item in reporting_blockers
                        if str(item.get("file") or "").strip()
                        and item.get("kind")
                        == "reporting_verification_unavailable"
                    },
                )
                if proof_result.needs_redraft:
                    proof_state = load_proof_review_state(ctx.state_dir)
                    proof_targets = proof_state.get("targets", {})
                    if not isinstance(proof_targets, dict):
                        proof_targets = {}
                    redraft_records = {
                        rel: (
                            proof_targets.get(rel)
                            if isinstance(proof_targets.get(rel), dict)
                            else "proof Review requested statement redraft"
                        )
                        for rel in proof_result.needs_redraft
                    }
                    completed_redrafts = {}
                    if isinstance(pipelined_report, dict):
                        raw_handoffs = pipelined_report.get(
                            "formalization_handoffs", {}
                        )
                        if isinstance(raw_handoffs, dict):
                            completed_redrafts = raw_handoffs
                    proof_redrafts_reopened = reopen_formalization_targets(
                        state_dir=ctx.state_dir,
                        project_path=ctx.project_path,
                        progress_file=ctx.progress_file,
                        redrafts=redraft_records,
                        iter_num=ctx.iter_num,
                        max_iterations=getattr(
                            ctx.options,
                            "formalization_review_max_iterations",
                            3,
                        ),
                        completed_redrafts=completed_redrafts,
                        enforce_budget=True,
                    )
                    ctx.current_stage = read_stage(ctx.progress_file)
                    log.warn(
                        "proof Review routed "
                        f"{len(proof_redrafts_reopened)} target(s) back to "
                        f"'{ctx.current_stage}' and revoked their pass certificates"
                    )
            log.info(
                "proof Review routing gate: "
                f"solved={len(proof_result.solved)}, "
                f"retry={len(proof_result.retry)}, "
                f"needs_redraft={len(proof_result.needs_redraft)}, "
                f"blocked_infrastructure="
                f"{len(proof_result.blocked_infrastructure)}, "
                f"exhausted={len(proof_result.exhausted)}"
            )

        review_secs = int(time.monotonic() - review_start)
        log.info(f"Review phase finished ({review_secs}s)")
        if ctx.dashboard_url:
            log.step(f"Journal: {ctx.dashboard_url}/journal")
        cfg = load_project_config(ctx.project_path)
        check_mandatory_dispatched(
            ctx.project_path, ctx.state_dir, ctx.iter_num,
            phase="review",
            enabled=resolve_subagents_enabled(cfg),
        )
        doctor_blocker_count = len([
            b for b in blockers
            if b.get("source") in PHYSICS_DOCTOR_BLOCKER_KEYS
        ])
        reviewer = _reviewer_for_project(ctx.project_path)
        domain_reviewer_blocker_count = len([
            b for b in blockers
            if b.get("source") == reviewer
        ])
        physics_reviewer_blocker_count = len([
            b for b in blockers
            if b.get("source") == PHYSICS_REVIEWER
        ])
        review_agent_blocker_count = len([
            b for b in blockers
            if b.get("source") == "review-agent"
        ])
        numeric_reporting_blocker_count = len(reporting_blockers)
        write_meta(ctx.iter_meta, **{
            "review.status": "done",
            "review.durationSecs": review_secs,
            "review.physicsBlockers": len(blockers),
            "review.physicsDoctorBlockers": doctor_blocker_count,
            "review.physicsReviewerBlockers": physics_reviewer_blocker_count,
            "review.physicsReviewAgentBlockers": review_agent_blocker_count,
            "review.physicsGateResetComplete": reset_complete,
            "review.domainReviewer": reviewer,
            "review.domainReviewerBlockers": domain_reviewer_blocker_count,
            "review.domainBlockers": len(blockers),
            "review.domainGateResetComplete": reset_complete,
            "review.numericReportingBlockers": numeric_reporting_blocker_count,
        })
        if formalization_result is not None:
            if formalization_result.retry:
                gate_status = "retry"
            elif formalization_result.exhausted:
                gate_status = "exhausted"
            else:
                gate_status = "passed"
            write_meta(ctx.iter_meta, **{
                "review.formalizationGateEnabled": True,
                "review.formalizationGateStatus": gate_status,
                "review.formalizationGatePassed": len(formalization_result.passed),
                "review.formalizationGateRetry": len(formalization_result.retry),
                "review.formalizationGateExhausted": len(formalization_result.exhausted),
                "review.formalizationGateReviewed": len(formalization_result.reviewed),
            })
        if proof_result is not None:
            write_meta(ctx.iter_meta, **{
                "review.proofGateEnabled": True,
                "review.proofGateSolved": len(proof_result.solved),
                "review.proofGateRetry": len(proof_result.retry),
                "review.proofGateNeedsRedraft": len(proof_result.needs_redraft),
                "review.proofGateInfrastructureBlocked": len(
                    proof_result.blocked_infrastructure
                ),
                "review.proofGateRedraftsReopened": len(proof_redrafts_reopened),
                "review.proofGateExhausted": len(proof_result.exhausted),
                "review.proofGateReviewed": len(proof_result.reviewed),
            })
        commit_phase(
            ctx.project_path, iter_num=ctx.iter_num, phase="review",
            summary=f"journal session ({review_secs}s)",
        )
        return PhaseResult()

    def _run_physics_doctor_gate(self) -> tuple[list[dict[str, str]], bool]:
        ctx = self.ctx
        profile = load_domain_profile(ctx.project_path)
        reviewer = _reviewer_for_project(ctx.project_path)
        blockers, reset_complete = _enforce_physics_review_blocker_gate(
            ctx.state_dir,
            ctx.progress_file,
            ctx.iter_num,
            project_path=ctx.project_path,
        )
        doctor_blockers = [
            b for b in blockers
            if b.get("source") in PHYSICS_DOCTOR_BLOCKER_KEYS
        ]
        reviewer_blockers = [
            b for b in blockers
            if b.get("source") == reviewer
        ]
        review_agent_blockers = [
            b for b in blockers
            if b.get("source") == "review-agent"
        ]
        if blockers:
            log.warn(
                f"{profile.name} review gate: {len(blockers)} blocker(s) remain "
                f"(doctor={len(doctor_blockers)}, "
                f"reviewer={len(reviewer_blockers)}, "
                f"review-agent={len(review_agent_blockers)})"
            )
        if reset_complete:
            ctx.current_stage = read_stage(ctx.progress_file)
            log.warn(
                f"{profile.name} review gate: PROGRESS.md was COMPLETE "
                f"despite {profile.name} blockers; reset stage to "
                f"'{ctx.current_stage}'."
            )
        return blockers, reset_complete

    def _invoke_parallel_formalization_review(
        self,
        objectives: list[Path],
        *,
        cfg,
    ) -> bool:
        """Run one isolated semantic Reviewer per formalized target."""
        ctx = self.ctx
        loop_cfg = cfg.loop_section()
        requested_jobs = max(
            1,
            int(loop_cfg.get(
                "parallel_formalization_review_jobs",
                ctx.options.max_parallel,
            )),
        )
        max_attempts = max(
            1,
            int(loop_cfg.get("parallel_formalization_review_max_attempts", 3)),
        )
        backoff_sec = max(
            0.0,
            float(loop_cfg.get("parallel_formalization_review_backoff_sec", 5)),
        )
        prior_state = load_formalization_review_state(ctx.state_dir) or {}
        prior_targets = prior_state.get("targets", {})
        if not isinstance(prior_targets, dict):
            prior_targets = {}

        start = time.monotonic()
        report = run_parallel_formalization_reviews(
            project_path=ctx.project_path,
            state_dir=ctx.state_dir,
            iter_dir=ctx.iter_dir,
            iter_num=ctx.iter_num,
            objectives=list(objectives),
            preflight=self._review_preflight or {},
            prior_gate_targets=prior_targets,
            requested_jobs=requested_jobs,
            max_attempts=max_attempts,
            backoff_sec=backoff_sec,
            verbose_logs=ctx.verbose_logs,
            model=ctx.model,
            backend=ctx.backend,
            harness=ctx.harness_descriptor_for("review"),
            partial_gate_max_iterations=(
                ctx.options.formalization_review_max_iterations
            ),
        )
        secs = round(time.monotonic() - start, 3)
        rounds = report.get("rounds", [])
        write_meta(ctx.iter_meta, **{
            "review.parallelFormalizationEnabled": True,
            "review.parallelFormalizationRequestedJobs": requested_jobs,
            "review.parallelFormalizationTargets": report.get("targets", 0),
            "review.parallelFormalizationReviewed": report.get("reviewed", 0),
            "review.parallelFormalizationUnresolved": len(
                report.get("unresolved", [])
            ),
            "review.parallelFormalizationRounds": rounds,
            "review.parallelFormalizationDurationSecs": secs,
            "review.parallelFormalizationReport": str(
                ctx.iter_dir / FORMALIZATION_REVIEW_REPORT_FILENAME
            ),
        })
        if not report.get("complete"):
            unresolved = report.get("unresolved", [])
            log.error(
                "parallel formalization Review incomplete after automatic "
                f"concurrency backoff: {len(unresolved)} unresolved target(s)"
            )
            return False

        log.success(
            "parallel formalization Review: "
            f"{report.get('reviewed', 0)}/{report.get('targets', 0)} "
            f"target(s) reviewed in {secs:.3f}s; "
            f"requested concurrency={requested_jobs}"
        )
        validate_script = data_path("scripts/validate-review.py")
        session_dir = (
            ctx.state_dir / "proof-journal" / "sessions"
            / f"session_{ctx.iter_num}"
        )
        if validate_script.exists():
            subprocess.run(
                [sys.executable, str(validate_script), str(session_dir)],
                capture_output=True,
            )
        return True

    def _invoke_parallel_target_review(
        self,
        objectives: list[Path],
        *,
        cfg,
    ) -> bool:
        """Run one isolated proof Reviewer per target and merge once."""
        ctx = self.ctx
        loop_cfg = cfg.loop_section()
        requested_jobs = max(
            1,
            int(loop_cfg.get("parallel_target_review_jobs", ctx.options.max_parallel)),
        )
        max_attempts = max(
            1,
            int(loop_cfg.get("parallel_target_review_max_attempts", 3)),
        )
        backoff_sec = max(
            0.0,
            float(loop_cfg.get("parallel_target_review_backoff_sec", 5)),
        )
        prior_state = load_proof_review_state(ctx.state_dir)
        prior_targets = prior_state.get("targets", {})
        if not isinstance(prior_targets, dict):
            prior_targets = {}

        start = time.monotonic()
        report = run_parallel_target_reviews(
            project_path=ctx.project_path,
            state_dir=ctx.state_dir,
            iter_dir=ctx.iter_dir,
            iter_num=ctx.iter_num,
            objectives=list(objectives),
            preflight=self._review_preflight or {},
            prior_gate_targets=prior_targets,
            requested_jobs=requested_jobs,
            max_attempts=max_attempts,
            backoff_sec=backoff_sec,
            verbose_logs=ctx.verbose_logs,
            model=ctx.model,
            backend=ctx.backend,
            harness=ctx.harness_descriptor_for("review"),
        )
        secs = round(time.monotonic() - start, 3)
        rounds = report.get("rounds", [])
        write_meta(ctx.iter_meta, **{
            "review.parallelTargetEnabled": True,
            "review.parallelTargetRequestedJobs": requested_jobs,
            "review.parallelTargetTargets": report.get("targets", 0),
            "review.parallelTargetReviewed": report.get("reviewed", 0),
            "review.parallelTargetUnresolved": len(report.get("unresolved", [])),
            "review.parallelTargetRounds": rounds,
            "review.parallelTargetDurationSecs": secs,
            "review.parallelTargetReport": str(ctx.iter_dir / "parallel-review.json"),
        })
        if report.get("complete"):
            log.success(
                "parallel target Review: "
                f"{report.get('reviewed', 0)}/{report.get('targets', 0)} "
                f"target(s) reviewed in {secs:.3f}s; "
                f"requested concurrency={requested_jobs}"
            )
        else:
            unresolved = report.get("unresolved", [])
            log.error(
                "parallel target Review incomplete after automatic "
                f"concurrency backoff: {len(unresolved)} unresolved target(s)"
            )
            return False

        validate_script = data_path("scripts/validate-review.py")
        session_dir = (
            ctx.state_dir / "proof-journal" / "sessions"
            / f"session_{ctx.iter_num}"
        )
        if validate_script.exists():
            subprocess.run(
                [sys.executable, str(validate_script), str(session_dir)],
                capture_output=True,
            )
        return True

    def _invoke_review(self) -> bool:
        ctx = self.ctx
        # Session number == iteration number. The pre-2026 monotonic
        # counter drifted away from iter numbers whenever the user did
        # ``git reset --hard`` past existing review dirs (the dirs are
        # filesystem-only, never tracked by the inner archon git, so a
        # reset would leave them in place while the iter numbers
        # rewound). Aligning the two means session_NNN/ is always
        # exactly the review of iter-NNN.
        session_num = ctx.iter_num
        journal_dir = ctx.state_dir / "proof-journal"
        session_dir = journal_dir / "sessions" / f"session_{session_num}"
        current_session_dir = journal_dir / "current_session"
        attempts_file = current_session_dir / "attempts_raw.jsonl"

        session_dir.mkdir(parents=True, exist_ok=True)
        current_session_dir.mkdir(parents=True, exist_ok=True)

        log.step("Extracting attempt data from prover logs...")
        provers_dir = ctx.iter_dir / "provers"
        # Take only the parsed `.jsonl` files (skip `.raw.jsonl`). The
        # `is_file()` filter drops dangling symlinks — these come from
        # (a) cancelled lanes whose parser was killed before writing
        # the target file, or (b) prior runs on the same iter dir with
        # a different lane set (e.g. kimi was enabled then disabled),
        # leaving stale symlinks pointing at non-existent files.
        parsed_logs = [
            p for p in sorted(provers_dir.glob("*.jsonl"))
            if not p.name.endswith(".raw.jsonl") and p.is_file()
        ] if provers_dir.exists() else []
        if parsed_logs:
            combined = ctx.iter_dir / "provers-combined.jsonl"
            with combined.open("w") as out:
                for jf in parsed_logs:
                    try:
                        out.write(jf.read_text(encoding="utf-8", errors="ignore"))
                    except OSError as e:
                        log.warn(f"skipping unreadable prover log {jf.name}: {e}")
        else:
            combined = ctx.iter_dir / "prover.jsonl"

        # ``current_session/attempts_raw.jsonl`` is reused across iters.
        # When no prover ran this iter (intentional skip, plan-validate
        # failure, etc.), extract-attempts.py either errors out (input
        # missing) or produces nothing, leaving the file with the *prior*
        # iter's attempts — which the review agent then reads as if it
        # were current. Stamp a sentinel so the file is unambiguously
        # this-iter, and skip the extract step entirely.
        if not parsed_logs:
            sentinel = {
                "type": "summary",
                "no_prover_lane": True,
                "iter": ctx.iter_num,
                "reason": (
                    "No prover lane this iter — either an intentional "
                    "skip (see plan-validate marker / iter sidecar) or "
                    "the prover phase produced no parsed logs."
                ),
            }
            attempts_file.write_text(
                json.dumps(sentinel, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        else:
            extract_script = data_path("scripts/extract-attempts.py")
            if extract_script.exists():
                subprocess.run(
                    [sys.executable, str(extract_script),
                     str(combined), str(attempts_file)],
                    capture_output=True,
                )
        
        # TO_USER.md is a *persistent* shared notice board — plan, prover,
        # and review may all maintain it. We deliberately do NOT clear it
        # here: a standing notice (e.g. "set DEEPSEEK_API_KEY to unblock X")
        # must survive quiet iters until the agent that owns the item prunes
        # it. The review agent is told to read it, drop now-irrelevant items,
        # and keep it to <=2-3 concise bullets (see review.md Step 7).

        cfg = load_project_config(ctx.project_path)
        compact_input_pack = None
        deterministic_review = self._review_preflight_path is not None
        if ctx.options.compress_plan_review_inputs or deterministic_review:
            pack_iter_dir = ctx.iter_dir
            if pack_iter_dir is None and ctx.dry_run:
                pack_iter_dir = ctx.log_dir / f"iter-{ctx.iter_num:03d}"
                pack_iter_dir.mkdir(parents=True, exist_ok=True)
            if pack_iter_dir is not None:
                compact_input_pack = build_review_input_pack(
                    project_path=ctx.project_path,
                    state_dir=ctx.state_dir,
                    iter_dir=pack_iter_dir,
                    iter_num=ctx.iter_num,
                    attempts_file=attempts_file,
                    combined_prover_log=combined,
                    deterministic_preflight=self._review_preflight_path,
                    deterministic_candidates_pack=self._review_candidate_pack,
                )
        prompt = build_review_prompt(
            ctx.project_name, ctx.project_path, ctx.state_dir, ctx.current_stage,
            session_num, session_dir, attempts_file, combined,
            ctx.iter_num,
            debug_feedback=ctx.options.debug_feedback,
            recent_iter_window=resolve_recent_iter_window(cfg),
            compact_input_pack=compact_input_pack,
            formalization_review_gate=ctx.options.formalization_review_gate,
            proof_review_gate=getattr(ctx.options, "proof_review_gate", False),
        )
        if self._review_preflight_path and self._review_candidate_pack:
            prompt = deterministic_review_prompt_prefix(
                preflight_path=self._review_preflight_path,
                candidate_pack=self._review_candidate_pack,
                doctor_path=(ctx.iter_dir / "blueprint-doctor.json"),
            ) + prompt
        prompt = _maybe_compress_review_prompt(
            ctx, prompt, force=deterministic_review,
        )
        review_log = ctx.iter_dir / "review"
        resume_sid = pick_resume_session(
            ctx.iter_meta, "review.sessionId",
            enabled=(ctx.resume_phase == self.skip_token),
            label="review",
            cwd=ctx.project_path,
            jsonl_fallback=Path(str(review_log) + ".jsonl"),
        )
        review_ok = ctx.make_agent("review").run(
            REVIEW_CONTINUE if resume_sid else prompt,
            cwd=ctx.project_path,
            log_base=review_log, verbose_logs=ctx.verbose_logs,
            resume_session_id=resume_sid,
        )
        persist_session_id(
            ctx.iter_meta, Path(str(review_log) + ".jsonl"),
            "review.sessionId",
        )

        validate_script = data_path("scripts/validate-review.py")
        if validate_script.exists():
            subprocess.run(
                [sys.executable, str(validate_script), str(session_dir), str(attempts_file)],
                capture_output=True,
            )

        # If the agent crashed before writing anything, drop the empty
        # session_NNN/ rather than leaving a stub the UI will surface.
        if session_dir.is_dir():
            try:
                content = list(session_dir.iterdir())
            except OSError:
                content = []
            if not content or all(
                p.is_file() and p.stat().st_size == 0 for p in content
            ):
                for p in content:
                    if p.is_file():
                        p.unlink()
                try:
                    session_dir.rmdir()
                    log.warn(
                        f"Removed empty session_{session_num}/ — review "
                        f"agent produced no output"
                    )
                except OSError:
                    pass
        return review_ok
