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
from archon.state import write_meta
from archon.state.progress import is_complete, write_stage
from archon.state.progress import read_stage
from archon.subagents.audit import check_mandatory_dispatched

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
    if low in {"none", "- none", "* none", "n/a", "- n/a", "* n/a"}:
        return False
    if "<finding>" in low or "<file>" in low:
        return False
    return bool(re.match(r"^[-*]\s+\S", stripped))


def _extract_physics_reviewer_must_fixes(text: str) -> list[str]:
    return [
        line.strip()
        for line in _markdown_section_lines(text, "## Must-fix-this-iter")
        if _is_substantive_must_fix(line)
    ]


def _load_physics_reviewer_blockers(state_dir: Path) -> list[dict[str, str]]:
    """Load current physics-reviewer verdicts that should block COMPLETE."""
    task_results = state_dir / "task_results"
    if not task_results.is_dir():
        return []

    blockers: list[dict[str, str]] = []
    for report in sorted(task_results.rglob("physics-reviewer-*.md")):
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
            "source": "physics-reviewer",
            "file": str(report),
            "kind": verdict or "must-fix-this-iter",
            "reason": "; ".join(reason_parts),
        })
    return blockers


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
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    sources = sorted({
        _physics_blocker_label(item.get("source") or "")
        for item in blockers
    })
    if len(sources) == 1:
        label = sources[0]
    else:
        label = "physics-review-gate"
    lines = [
        f"\n- [{ts}] archon[{label}]: current review found "
        f"{len(blockers)} physics blocker(s), so the project must not "
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


def _enforce_physics_review_blocker_gate(
    state_dir: Path,
    progress_file: Path,
    iter_num: int,
) -> tuple[list[dict[str, str]], bool]:
    """Prevent physics review blockers from being hidden by COMPLETE."""
    blockers = (
        _load_physics_doctor_blockers(state_dir, iter_num)
        + _load_physics_reviewer_blockers(state_dir)
        + _load_physics_session_review_blockers(state_dir, iter_num)
    )
    if not blockers:
        return blockers, False
    if not is_complete(progress_file):
        return blockers, False

    write_stage(progress_file, "autoformalize")
    _append_physics_review_auto_note(
        state_dir / AUTO_NOTES_FILENAME,
        blockers,
    )
    return blockers, True


def _enforce_physics_doctor_blocker_gate(
    state_dir: Path,
    progress_file: Path,
    iter_num: int,
) -> tuple[list[dict[str, str]], bool]:
    """Backward-compatible alias for the broader physics review gate."""
    return _enforce_physics_review_blocker_gate(state_dir, progress_file, iter_num)


def _maybe_compress_review_prompt(ctx, prompt: str) -> str:
    if not ctx.options.compress_plan_review_inputs:
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

        if self.skip_token in ctx.skip_now:
            log.phase(self.number, f"{self.name} — skipped (--from)")
            return PhaseResult(skipped=True)

        if ctx.dry_run:
            return PhaseResult(skipped=True)
        if ctx.options.no_review:
            self._run_physics_doctor_gate()
            return PhaseResult(skipped=True)

        log.phase(self.number, self.name)
        review_start = time.monotonic()
        write_meta(ctx.iter_meta, **{"review.status": "running"})

        self._invoke_review()
        blockers, reset_complete = self._run_physics_doctor_gate()

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
        reviewer_blocker_count = len([
            b for b in blockers
            if b.get("source") == "physics-reviewer"
        ])
        review_agent_blocker_count = len([
            b for b in blockers
            if b.get("source") == "review-agent"
        ])
        write_meta(ctx.iter_meta, **{
            "review.status": "done",
            "review.durationSecs": review_secs,
            "review.physicsBlockers": len(blockers),
            "review.physicsDoctorBlockers": doctor_blocker_count,
            "review.physicsReviewerBlockers": reviewer_blocker_count,
            "review.physicsReviewAgentBlockers": review_agent_blocker_count,
            "review.physicsGateResetComplete": reset_complete,
        })
        commit_phase(
            ctx.project_path, iter_num=ctx.iter_num, phase="review",
            summary=f"journal session ({review_secs}s)",
        )
        return PhaseResult()

    def _run_physics_doctor_gate(self) -> tuple[list[dict[str, str]], bool]:
        ctx = self.ctx
        blockers, reset_complete = _enforce_physics_review_blocker_gate(
            ctx.state_dir,
            ctx.progress_file,
            ctx.iter_num,
        )
        doctor_blockers = [
            b for b in blockers
            if b.get("source") in PHYSICS_DOCTOR_BLOCKER_KEYS
        ]
        reviewer_blockers = [
            b for b in blockers
            if b.get("source") == "physics-reviewer"
        ]
        review_agent_blockers = [
            b for b in blockers
            if b.get("source") == "review-agent"
        ]
        if blockers:
            log.warn(
                f"physics review gate: {len(blockers)} blocker(s) remain "
                f"(doctor={len(doctor_blockers)}, "
                f"reviewer={len(reviewer_blockers)}, "
                f"review-agent={len(review_agent_blockers)})"
            )
        if reset_complete:
            ctx.current_stage = read_stage(ctx.progress_file, ctx.force_stage())
            log.warn(
                "physics review gate: PROGRESS.md was COMPLETE despite "
                f"physics blockers; reset stage to '{ctx.current_stage}'."
            )
        return blockers, reset_complete

    def _invoke_review(self) -> None:
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
        if ctx.options.compress_plan_review_inputs:
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
                )
        prompt = build_review_prompt(
            ctx.project_name, ctx.project_path, ctx.state_dir, ctx.current_stage,
            session_num, session_dir, attempts_file, combined,
            ctx.iter_num,
            debug_feedback=ctx.options.debug_feedback,
            recent_iter_window=resolve_recent_iter_window(cfg),
            compact_input_pack=compact_input_pack,
        )
        prompt = _maybe_compress_review_prompt(ctx, prompt)
        review_log = ctx.iter_dir / "review"
        resume_sid = pick_resume_session(
            ctx.iter_meta, "review.sessionId",
            enabled=(ctx.resume_phase == self.skip_token),
            label="review",
            cwd=ctx.project_path,
            jsonl_fallback=Path(str(review_log) + ".jsonl"),
        )
        ctx.make_agent("review").run(
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
