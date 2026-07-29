"""Plan phase: invoke the plan agent and refresh `current_stage`.

Loop-side automation done here so the prompt doesn't have to ask the
agent to do it:

* **User hints**: read ``USER_HINTS.md`` BEFORE the agent starts,
  inject the content into the prompt via ``captured_user_hints=``,
  and clear the file AFTER the plan phase succeeds. The agent does
  not read or clear that file itself.
* **Blueprint-doctor findings**: the build_plan_prompt builder reads
  the prior iter's doctor JSON and injects findings inline — no
  agent-side file read required.
"""

from __future__ import annotations

import re
import time
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
from archon.phase_input_summary import build_plan_input_pack
from archon.prompts import build_plan_prompt
from archon.commands.loop.sorry_count import count_sorries
from archon.state import is_complete, read_stage, write_meta, write_stage
from archon.subagents.audit import check_mandatory_dispatched

from ..deterministic_plan import (
    deterministic_plan_prompt_prefix,
    select_deterministic_candidates,
    write_deterministic_candidate_pack,
    write_deterministic_objectives,
)
from ..plan_validate import AUTO_NOTES_FILENAME
from ..resume import PLAN_CONTINUE, persist_session_id, pick_resume_session
from ..proof_review_gate import proof_review_prompt_block
from .base import Phase, PhaseResult


def _capture_auto_notes(state_dir: Path) -> str | None:
    """Read AUTO_NOTES.md (loop-managed validation feedback) if present.

    This is the system-generated counterpart to USER_HINTS.md: plan-validate
    writes dropped/blocked/deferred-objective notes here (never into the
    user-authored USER_HINTS.md). Captured before the plan agent runs and
    cleared after, exactly like user hints, but with no persistent section to
    preserve — it is fully loop-owned.
    """
    notes_file = state_dir / AUTO_NOTES_FILENAME
    if not notes_file.is_file():
        return None
    try:
        return notes_file.read_text(encoding="utf-8")
    except OSError:
        return None


def _clear_auto_notes(state_dir: Path) -> None:
    """Delete AUTO_NOTES.md after the plan phase consumed it.

    Unlike USER_HINTS.md (which keeps a template + persistent section), this
    file is purely loop-owned, so clearing means removing it — the next
    plan-validate run recreates it on demand.
    """
    notes_file = state_dir / AUTO_NOTES_FILENAME
    try:
        notes_file.unlink(missing_ok=True)
    except OSError as e:
        log.warn(f"could not clear {notes_file}: {e}")


def _capture_user_hints(state_dir: Path) -> str | None:
    """Read USER_HINTS.md if present and return its text.

    Returns the raw text (whitespace preserved) when the file exists
    and is readable; returns ``None`` when the file is missing or
    unreadable. The clear step is deferred to
    :func:`_clear_user_hints` so we only clear when the plan phase
    actually consumes the hints — a crashed plan keeps the file
    intact for the retry.
    """
    hints_file = state_dir / "USER_HINTS.md"
    if not hints_file.is_file():
        return None
    try:
        return hints_file.read_text(encoding="utf-8")
    except OSError:
        return None


_PERSISTENT_HEADING = re.compile(r"^##\s+Persistent hints\s*$", re.IGNORECASE | re.MULTILINE)
_HTML_COMMENT_END_RE = re.compile(r"-->")


def _split_hints(text: str) -> tuple[str, str]:
    """Split USER_HINTS.md text into (temporary_body, persistent_block).

    ``persistent_block`` is everything from the ``## Persistent hints``
    heading to EOF (heading line included).  ``temporary_body`` is the
    rest.  Returns (text, "") when no persistent section is found.

    HTML comment blocks are skipped before searching so that a heading
    mentioned inside the comment preamble (e.g. the template's format
    guide) is not mistaken for the actual section boundary.
    """
    # Start searching after the last HTML comment end marker so headings
    # mentioned inside the comment preamble are ignored.
    search_from = 0
    for cm in _HTML_COMMENT_END_RE.finditer(text):
        search_from = cm.end()
    m = _PERSISTENT_HEADING.search(text, search_from)
    if not m:
        return text, ""
    return text[: m.start()], text[m.start():]


def _clear_user_hints(state_dir: Path) -> None:
    """Selectively reset USER_HINTS.md after the plan phase consumed it.

    Only the ``## Temporary hints`` section is cleared; the
    ``## Persistent hints`` section (standing user directives) is
    preserved verbatim across iterations. The cleared temporary section
    is replaced with the corresponding part of the bundled template so
    the HTML-comment preamble and section headings are always present.

    Falls back to a full template reset when the template is unreadable
    or the file cannot be parsed, so a missing-template scenario never
    carries stale content into the next iter.
    """
    hints_file = state_dir / "USER_HINTS.md"
    try:
        template = _read_user_hints_template()
    except Exception:
        template = ""

    # Read the current file to preserve any persistent hints.
    current = ""
    try:
        current = hints_file.read_text(encoding="utf-8")
    except OSError:
        pass

    _, persistent_block = _split_hints(current)

    if persistent_block:
        # Rebuild: fresh template up to (but not including) the persistent
        # section, then the preserved persistent section.
        template_temporary, _ = _split_hints(template)
        new_content = template_temporary + persistent_block
    else:
        new_content = template

    try:
        hints_file.write_text(new_content, encoding="utf-8")
    except OSError as e:
        log.warn(f"could not clear {hints_file}: {e}")


def _read_user_hints_template() -> str:
    """Return the bundled ``USER_HINTS.md`` template content.

    Resolved via the same ``data_path`` helper ``archon init`` uses, so
    the runtime can't drift from what a fresh ``archon init`` would
    produce. Empty string when the template is missing — defensive
    fallback so a missing-template scenario degrades to clean clear
    behavior rather than crashing the loop.
    """
    from archon.commands.init.utils import data_path
    template_path = data_path("archon-template/USER_HINTS.md")
    if not template_path.is_file():
        return ""
    try:
        return template_path.read_text(encoding="utf-8")
    except OSError:
        return ""


def _maybe_compress_plan_prompt(ctx, prompt: str, *, force: bool = False) -> str:
    if not ctx.options.compress_plan_review_inputs and not force:
        return prompt
    result = compress_prompt(
        prompt,
        role="plan",
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
                ctx.iter_dir / "prompt-compression-plan.json",
                report,
            )
        except OSError as e:
            log.warn(f"could not write plan prompt compression report: {e}")
    if ctx.iter_meta is not None:
        write_meta(
            ctx.iter_meta,
            **{
                "plan.promptOriginalChars": report.original_chars,
                "plan.promptCompressedChars": report.compressed_chars,
                "plan.promptCompressionOmittedChars": report.omitted_chars,
                "plan.promptCompressionChanged": report.changed,
            },
        )
    if report.changed:
        log.info(
            "Plan prompt compression: "
            f"{report.original_chars} -> {report.compressed_chars} chars "
            f"({report.omitted_chars} omitted)"
        )
    else:
        log.info(
            f"Plan prompt compression enabled; no eligible section changed "
            f"({report.original_chars} chars)."
        )
    return result.prompt


class PlanPhase(Phase):
    name = "Plan agent"
    number = 1
    skip_token = "plan"

    def run(self) -> PhaseResult:
        ctx = self.ctx
        if self.skip_token in ctx.skip_now:
            log.phase(self.number, f"{self.name} — skipped (--from)")
            ctx.current_stage = read_stage(ctx.progress_file, ctx.force_stage())
            return PhaseResult(skipped=True)

        log.phase(self.number, self.name)
        plan_start = time.monotonic()
        cfg = load_project_config(ctx.project_path)
        starting_stage = ctx.current_stage
        captured_hints = _capture_user_hints(ctx.state_dir)
        captured_auto_notes = _capture_auto_notes(ctx.state_dir)
        deterministic_candidates = []
        deterministic_candidate_pack = None
        loop_cfg = cfg.loop_section()
        deterministic_enabled = bool(loop_cfg.get("deterministic_plan", False))
        foundation_build_enabled = bool(
            loop_cfg.get("pipeline_foundation_build", False)
        )
        foundation_build_max_iterations = max(1, int(loop_cfg.get(
            "pipeline_foundation_build_max_iterations", 3,
        )))
        pack_iter_dir = ctx.iter_dir
        if pack_iter_dir is None and ctx.dry_run:
            pack_iter_dir = ctx.log_dir / f"iter-{ctx.iter_num:03d}"
            pack_iter_dir.mkdir(parents=True, exist_ok=True)
        if deterministic_enabled and starting_stage.strip().lower().startswith(
            ("prover", "polish")
        ):
            deterministic_candidates = select_deterministic_candidates(
                project_path=ctx.project_path,
                state_dir=ctx.state_dir,
                stage=starting_stage,
                # `max_objectives` is queue depth; `max_parallel` only caps
                # concurrently executing workers. A deeper queue refills idle
                # slots immediately when shorter targets finish.
                limit=ctx.options.max_objectives,
                formalization_gate_enabled=ctx.options.formalization_review_gate,
                proof_gate_enabled=getattr(ctx.options, "proof_review_gate", False),
                foundation_build_enabled=foundation_build_enabled,
                foundation_build_max_iterations=(
                    foundation_build_max_iterations
                ),
            )
            if deterministic_candidates and pack_iter_dir is not None:
                if not ctx.dry_run:
                    write_deterministic_objectives(
                        progress_file=ctx.progress_file,
                        state_dir=ctx.state_dir,
                        iter_num=ctx.iter_num,
                        candidates=deterministic_candidates,
                    )
                deterministic_candidate_pack = write_deterministic_candidate_pack(
                    project_path=ctx.project_path,
                    iter_dir=pack_iter_dir,
                    iter_num=ctx.iter_num,
                    candidates=deterministic_candidates,
                )
                log.info(
                    "Deterministic Plan selected "
                    f"{len(deterministic_candidates)} Review-safe objective(s); "
                    "the plan agent is restricted to this bounded set."
                )
                if not ctx.dry_run and ctx.iter_meta is not None:
                    write_meta(ctx.iter_meta, **{
                        "plan.deterministic": True,
                        "plan.deterministicCandidates": [
                            item.relative_path for item in deterministic_candidates
                        ],
                    })
            else:
                log.warn(
                    "Deterministic Plan found no eligible prover objectives; "
                    "falling back to the normal planner for completion/blocker handling."
                )
        compact_input_pack = None
        if ctx.options.compress_plan_review_inputs or deterministic_candidate_pack:
            if pack_iter_dir is not None:
                pack_iter_num = ctx.iter_num
                compact_input_pack = build_plan_input_pack(
                    project_path=ctx.project_path,
                    state_dir=ctx.state_dir,
                    iter_dir=pack_iter_dir,
                    iter_num=pack_iter_num,
                    deterministic_candidates_pack=deterministic_candidate_pack,
                )
        if deterministic_candidate_pack is not None and compact_input_pack is not None:
            # Crucially, do not call build_plan_prompt here: its leandag
            # frontier construction parses the full blueprint corpus.
            plan_prompt = deterministic_plan_prompt_prefix(
                candidate_pack=deterministic_candidate_pack,
                plan_input_pack=compact_input_pack,
                state_dir=ctx.state_dir,
                iter_num=ctx.iter_num,
                project_name=ctx.project_name,
                project_path=ctx.project_path,
                stage=starting_stage,
                captured_user_hints=captured_hints,
                captured_auto_notes=captured_auto_notes,
            )
        else:
            plan_prompt = build_plan_prompt(
                ctx.project_name, ctx.project_path, ctx.state_dir, ctx.current_stage,
                ctx.iter_num,
                ignore_multilane=(
                    ctx.options.multilane_preview or ctx.options.multilane_execute
                ),
                debug_feedback=ctx.options.debug_feedback,
                recent_iter_window=resolve_recent_iter_window(cfg),
                captured_user_hints=captured_hints,
                captured_auto_notes=captured_auto_notes,
                compact_input_pack=compact_input_pack,
            )
        plan_prompt += proof_review_prompt_block(
            state_dir=ctx.state_dir,
            max_iterations=getattr(ctx.options, "proof_review_max_iterations", 3),
            enabled=(
                getattr(ctx.options, "proof_review_gate", False)
                and ctx.current_stage.strip().lower().startswith("prover")
            ),
        )
        plan_prompt = _maybe_compress_plan_prompt(
            ctx, plan_prompt, force=bool(deterministic_candidate_pack)
        )

        if ctx.dry_run:
            log.step("[dry-run] Plan prompt:")
            print(plan_prompt)
        else:
            plan_log = ctx.iter_dir / "plan"
            resume_sid = pick_resume_session(
                ctx.iter_meta, "plan.sessionId",
                enabled=(ctx.resume_phase == self.skip_token),
                label="plan",
                cwd=ctx.project_path,
                jsonl_fallback=Path(str(plan_log) + ".jsonl"),
            )
            ctx.make_agent("plan").run(
                PLAN_CONTINUE if resume_sid else plan_prompt,
                cwd=ctx.project_path,
                log_base=plan_log, verbose_logs=ctx.verbose_logs,
                env_overrides={"ARCHON_ITER_NUM": f"{ctx.iter_num:03d}"},
                resume_session_id=resume_sid,
            )
            persist_session_id(
                ctx.iter_meta, Path(str(plan_log) + ".jsonl"),
                "plan.sessionId",
            )

        if deterministic_candidates and not ctx.dry_run:
            # The planner owns strategy, not scheduling. Restore the exact
            # loop-selected frontier if the model rewrote PROGRESS.md.
            write_deterministic_objectives(
                progress_file=ctx.progress_file,
                state_dir=ctx.state_dir,
                iter_num=ctx.iter_num,
                candidates=deterministic_candidates,
            )
            write_stage(ctx.progress_file, starting_stage)

        plan_secs = int(time.monotonic() - plan_start)
        log.info(f"Plan phase finished ({plan_secs}s)")
        if not ctx.dry_run:
            # Clear USER_HINTS.md AFTER the plan agent has had a chance
            # to consume the captured content. If the plan crashed
            # before completing this far, the file is left intact so
            # the retry sees the same hints.
            if captured_hints is not None and captured_hints.strip():
                _clear_user_hints(ctx.state_dir)
            # AUTO_NOTES.md is fully loop-owned — clear it whenever it had
            # content so each validation note reaches the planner exactly once.
            if captured_auto_notes is not None and captured_auto_notes.strip():
                _clear_auto_notes(ctx.state_dir)
            check_mandatory_dispatched(
                ctx.project_path, ctx.state_dir, ctx.iter_num,
                phase="plan",
                enabled=resolve_subagents_enabled(cfg),
            )
            write_meta(
                ctx.iter_meta,
                **{"plan.status": "done", "plan.durationSecs": plan_secs},
            )
            commit_phase(
                ctx.project_path, iter_num=ctx.iter_num, phase="plan",
                summary=f"stage={ctx.current_stage} ({plan_secs}s)",
            )

        if is_complete(ctx.progress_file, ctx.force_stage()):
            remaining_sorries = None if ctx.dry_run else count_sorries(ctx.project_path)
            if remaining_sorries is not None and remaining_sorries > 0:
                log.warn(
                    f"Plan marked COMPLETE, but {remaining_sorries} sorries "
                    f"were found."
                )
                write_stage(ctx.progress_file, "prover")
                ctx.current_stage = read_stage(ctx.progress_file, ctx.force_stage())
                log.warn(
                    "Stage reset to 'prover' so the loop continues instead "
                    "of accepting an incomplete project."
                )
            else:
                log.success("PROGRESS.md says COMPLETE. Exiting loop.")
                return PhaseResult(completed=True)

        ctx.current_stage = read_stage(ctx.progress_file, ctx.force_stage())
        return PhaseResult()
