"""Serial and parallel prover runners.

`SerialProverRunner` runs one prover invocation in the project's main
checkout. `ParallelProverRunner` fans out one prover per file in
`PROGRESS.md ## Current Objectives` over a `ProcessPoolExecutor`.

Both runners write meta status into the iteration's `meta.json` so the
dashboard can surface live state.
"""

from __future__ import annotations

import hashlib
import heapq
import json
import time
from collections import deque
from concurrent.futures import (
    FIRST_COMPLETED,
    ProcessPoolExecutor,
    ThreadPoolExecutor,
    as_completed,
    wait,
)
from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import count
from pathlib import Path

from archon import log
from archon.agent import (
    ClaudeBackend,
    DEFAULT_HARNESS,
    QuotaExhaustedError,
    build_runner,
)
from archon.commands.tooling.project_config import HarnessDescriptor
from archon.prompts import (
    build_parallel_prover_prompt,
    build_prover_prompt,
    default_prover_mode_for_stage,
    normalize_stage_for_prompt_path,
)
from archon.state import (
    archive_task_results,
    parse_objective_files,
    parse_objectives_with_modes,
    read_meta,
    write_meta,
)

from ..formalization_review_gate import (
    apply_target_formalization_review,
    filter_materialized_redrafts_for_dispatch,
    formalization_review_decision,
    load_gate_state as load_formalization_review_state,
    reopen_formalization_targets,
)
from ..parallel_formalization_review import (
    _run_formalization_review_worker,
    build_target_formalization_review_prompt,
)
from ..parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewOutcome,
    TargetReviewSpec,
    _run_review_worker,
    build_target_review_prompt,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from ..proof_review_gate import (
    apply_target_proof_review,
    load_proof_review_state,
    proof_review_decision,
)
from ..review_preflight import check_review_target
from ..resume import PROVER_CONTINUE, persist_session_id, pick_resume_session
from ..utils import file_slug, relpath
from .environment import ProverEnvironment, snapshot_baseline


def _default_harness() -> HarnessDescriptor:
    """The built-in claude-code descriptor (zero-config default).

    Used as the default for the prover runners so an unconfigured project
    threads exactly the built-in claude-code runner — :func:`build_runner`
    short-circuits a ``runner == "claude-code"`` descriptor to the legacy
    :class:`~archon.agent.ClaudeAgent` (carrying the loop-wide backend).
    """
    return HarnessDescriptor(name=DEFAULT_HARNESS, runner=DEFAULT_HARNESS)


def _load_mode_content(state_dir: Path, mode_name: str | None) -> str | None:
    """Load the body of a prover-mode descriptor (after frontmatter), or None."""
    if not mode_name:
        return None
    mode_file = state_dir / "prover-modes" / f"{mode_name}.md"
    if not mode_file.exists():
        return None
    text = mode_file.read_text(encoding="utf-8")
    # Strip YAML frontmatter (---...---) so only the body is injected.
    import re as _re
    stripped = _re.sub(r"^---\s*\n.*?\n---\s*\n", "", text, count=1, flags=_re.DOTALL)
    return stripped.strip() or None


_PHYSICS_BLUEPRINT_MARKER = "% archon:physics"
_PHYSICS_STAGE_MODES = {
    "autoformalize": "physics-formalize",
    "prover": "physics",
}


def _blueprint_chapter_for_target(project_path: Path, target: Path) -> Path:
    """Return the conventional blueprint chapter path for a Lean target."""
    try:
        rel = target.resolve().relative_to(project_path.resolve())
    except ValueError:
        rel = target
    stem_parts = Path(rel).with_suffix("").parts
    slug = "_".join(stem_parts)
    return project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"


def _target_has_physics_blueprint_marker(project_path: Path, target: Path) -> bool:
    chapter = _blueprint_chapter_for_target(project_path, target)
    try:
        return _PHYSICS_BLUEPRINT_MARKER in chapter.read_text(encoding="utf-8")
    except OSError:
        return False


def _mode_file_exists(state_dir: Path, mode_name: str) -> bool:
    return (state_dir / "prover-modes" / f"{mode_name}.md").is_file()


def select_prover_mode_for_target(
    state_dir: Path,
    stage: str,
    project_path: Path,
    target: Path,
    *,
    explicit_mode: str | None,
) -> str | None:
    """Resolve the prover mode for one objective file.

    Explicit ``[prover-mode: ...]`` tags still win. Without a tag, physics
    blueprint chapters opt into physics-aware modes for formalization/proving;
    other targets use the normal stage default.
    """
    if explicit_mode:
        return explicit_mode
    canonical = normalize_stage_for_prompt_path(stage)
    if _target_has_physics_blueprint_marker(project_path, target):
        physics_mode = _PHYSICS_STAGE_MODES.get(canonical)
        if physics_mode and _mode_file_exists(state_dir, physics_mode):
            return physics_mode
    return default_prover_mode_for_stage(state_dir, stage)


def _target_sha256(target: Path) -> str:
    try:
        return hashlib.sha256(target.read_bytes()).hexdigest()
    except OSError:
        return ""


def _task_result_fingerprints(state_dir: Path, rel: str) -> dict[str, str]:
    result_root = state_dir / "task_results"
    slug = file_slug(rel)
    candidates = {
        result_root / f"{rel}.md",
        result_root / f"{Path(rel).name}.md",
        result_root / f"{slug}.lean.md",
        result_root / f"{slug}.md",
    }
    fingerprints: dict[str, str] = {}
    for path in candidates:
        digest = _target_sha256(path)
        if digest:
            fingerprints[str(path)] = digest
    return fingerprints


def build_immediate_redraft_prompt(
    *,
    project_name: str,
    project_path: Path,
    state_dir: Path,
    iter_num: int,
    target: Path,
    review_certificate: dict,
    debug_feedback: bool,
    handoff_label: str = "proof Review",
) -> str:
    """Build a target-only formalizer prompt from a semantic Review route."""
    rel = relpath(target, project_path)
    mode_name = select_prover_mode_for_target(
        state_dir, "autoformalize", project_path, target, explicit_mode=None,
    )
    base_prompt = build_parallel_prover_prompt(
        project_name,
        project_path,
        state_dir,
        "autoformalize",
        iter_num,
        assigned_rel_lean_path=rel,
        debug_feedback=debug_feedback,
        mode_name=mode_name,
        mode_content=_load_mode_content(state_dir, mode_name),
    )
    certificate = json.dumps(review_certificate, ensure_ascii=False, indent=2)
    return f"""{base_prompt}

Your assigned file: {rel}

## Immediate {handoff_label} redraft hand-off

The global PROGRESS stage intentionally remains `prover` until the batch's
atomic Review aggregation finishes. Ignore that stage for task routing: the
validated target Review certificate below authorizes an immediate, target-only
`autoformalize` redraft.

{certificate}

Repair the certificate's stated root cause in the theorem contract, not just
the last proof error. You may change unprotected statements in `{rel}` and
replace proof bodies invalidated by those statement changes with explicit
`by sorry` stubs. Never violate `archon-protected.yaml`; report a protected
contract as blocked. Do not continue proving the old contract. Keep the file
compiling, update only the assigned task-result report, and do not edit
PROGRESS.md, gate files, AUTO_NOTES.md, blueprint files, or any other Lean file.
Return only after the
assigned Lean file compiles and the redraft evidence is durable on disk.
"""


def _run_single_prover(
    prompt: str,
    cwd: Path,
    log_base: Path,
    verbose_logs: bool,
    model: str,
    snap_dir: Path | None = None,
    project_path: Path | None = None,
    resume_session_id: str | None = None,
    backend: ClaudeBackend | None = None,
    harness: HarnessDescriptor | None = None,
) -> bool:
    """Top-level for `ProcessPoolExecutor` — must be importable by the worker.

    ``harness`` is the resolved, **picklable** :class:`HarnessDescriptor`
    (a frozen dataclass) — not a bare name string — so the worker can build
    a fully-configured runner (codex model / effort / gateway, or the
    claude-code engine carrying ``backend``) via :func:`build_runner`
    without re-reading config. ``None`` → built-in claude-code.
    """
    descriptor = harness if harness is not None else _default_harness()
    agent = build_runner(
        role="prover", model=model, descriptor=descriptor,
        backend=backend or ClaudeBackend(),
    )
    if snap_dir is not None and project_path is not None:
        with ProverEnvironment(
            snap_dir=snap_dir,
            prover_jsonl=Path(str(log_base) + ".jsonl"),
            project_path=project_path,
        ):
            return agent.run(
                prompt, cwd=cwd, log_base=log_base, verbose_logs=verbose_logs,
                resume_session_id=resume_session_id,
            )
    return agent.run(
        prompt, cwd=cwd, log_base=log_base, verbose_logs=verbose_logs,
        resume_session_id=resume_session_id,
    )


@dataclass(frozen=True)
class _PipelineWork:
    kind: str
    target: Path
    rel: str
    slug: str
    attempt: int = 0
    cycle: int = 0
    baseline_sha256: str = ""
    result_fingerprints: tuple[tuple[str, str], ...] = ()


class SerialProverRunner:
    """Runs a single prover prompt over the whole stage.

    The plan agent's objectives mention chapters; we don't pre-split by
    file because we don't know which file a serial run will touch in
    which order.
    """

    def __init__(
        self,
        *,
        project_name: str,
        project_path: Path,
        state_dir: Path,
        stage: str,
        iter_dir: Path,
        iter_num: int,
        verbose_logs: bool,
        model: str,
        debug_feedback: bool = False,
        iter_meta: Path | None = None,
        resume_enabled: bool = False,
        backend: ClaudeBackend | None = None,
        harness: HarnessDescriptor | None = None,
    ) -> None:
        self.project_name = project_name
        self.project_path = project_path
        self.state_dir = state_dir
        self.stage = stage
        self.iter_dir = iter_dir
        self.iter_num = iter_num
        self.verbose_logs = verbose_logs
        self.model = model
        self.debug_feedback = debug_feedback
        self.iter_meta = iter_meta
        self.resume_enabled = resume_enabled
        self.backend = backend or ClaudeBackend()
        self.harness = harness if harness is not None else _default_harness()

    def run(self, *, dry_run: bool, progress_file: Path) -> None:
        # No per-file tags on the serial whole-stage path → use the stage's
        # default prover mode (the static prover-<stage>.md prompts were
        # retired; modes are the single source of truth).
        stage_mode = default_prover_mode_for_stage(self.state_dir, self.stage)
        prompt = build_prover_prompt(
            self.project_name, self.project_path, self.state_dir, self.stage,
            self.iter_num, debug_feedback=self.debug_feedback,
            mode_name=stage_mode,
            mode_content=_load_mode_content(self.state_dir, stage_mode),
        )
        if dry_run:
            log.step("[dry-run] Prover prompt:")
            print(prompt)
            return

        archive_task_results(self.state_dir, self.iter_dir)

        prover_log = self.iter_dir / "prover"
        for sf in parse_objective_files(progress_file, self.project_path):
            srel = relpath(sf, self.project_path)
            sslug = file_slug(srel)
            snapshot_baseline(sf, self.iter_dir / "snapshots" / sslug)

        resume_sid = pick_resume_session(
            self.iter_meta, "prover.sessionId",
            enabled=self.resume_enabled, label="prover",
            cwd=self.project_path,
            jsonl_fallback=Path(str(prover_log) + ".jsonl"),
        )
        with ProverEnvironment(
            snap_dir=self.iter_dir / "snapshots",
            prover_jsonl=Path(str(prover_log) + ".jsonl"),
            project_path=self.project_path,
            serial_mode=True,
        ):
            build_runner(
                role="prover", model=self.model, descriptor=self.harness,
                backend=self.backend,
            ).run(
                PROVER_CONTINUE if resume_sid else prompt,
                cwd=self.project_path,
                log_base=prover_log, verbose_logs=self.verbose_logs,
                resume_session_id=resume_sid,
            )
        persist_session_id(
            self.iter_meta, Path(str(prover_log) + ".jsonl"),
            "prover.sessionId",
        )


class ParallelProverRunner:
    """Runs one prover per objective file in a process pool.

    Single-file rounds collapse to serial-with-blueprint-pointer for
    determinism: spawning a process pool for one worker just adds noise.
    """

    def __init__(
        self,
        *,
        project_name: str,
        project_path: Path,
        state_dir: Path,
        stage: str,
        iter_dir: Path,
        iter_meta: Path,
        iter_num: int,
        max_parallel: int,
        max_objectives: int,
        block_on_blocked_deps: bool,
        verbose_logs: bool,
        model: str,
        dashboard_url: str | None = None,
        blueprint_url: str | None = None,
        debug_feedback: bool = False,
        resume_enabled: bool = False,
        backend: ClaudeBackend | None = None,
        harness: HarnessDescriptor | None = None,
        pipeline_review: PipelinedTargetReviewConfig | None = None,
        executor_factory=ProcessPoolExecutor,
        prover_worker=_run_single_prover,
        review_worker=_run_review_worker,
        formalization_review_worker=_run_formalization_review_worker,
        formalizer_worker=None,
        preflight_checker=check_review_target,
    ) -> None:
        self.project_name = project_name
        self.project_path = project_path
        self.state_dir = state_dir
        self.stage = stage
        self.iter_dir = iter_dir
        self.iter_meta = iter_meta
        self.iter_num = iter_num
        self.max_parallel = max_parallel
        self.max_objectives = max_objectives
        self.block_on_blocked_deps = block_on_blocked_deps
        self.verbose_logs = verbose_logs
        self.model = model
        self.dashboard_url = dashboard_url
        self.blueprint_url = blueprint_url
        self.debug_feedback = debug_feedback
        self.resume_enabled = resume_enabled
        self.backend = backend or ClaudeBackend()
        self.harness = harness if harness is not None else _default_harness()
        self.pipeline_review = pipeline_review
        self.executor_factory = executor_factory
        self.prover_worker = prover_worker
        self.review_worker = review_worker
        self.formalization_review_worker = formalization_review_worker
        self.formalizer_worker = (
            formalizer_worker if formalizer_worker is not None else prover_worker
        )
        self.preflight_checker = preflight_checker

    def run(self, *, dry_run: bool) -> None:
        progress = self.state_dir / "PROGRESS.md"
        objectives_with_modes = parse_objectives_with_modes(progress, self.project_path)
        sorry_files = [p for p, _ in objectives_with_modes]
        file_modes: dict[str, str | None] = {
            str(p): m for p, m in objectives_with_modes
        }
        if not sorry_files:
            log.warn("No files parsed from PROGRESS.md ## Current Objectives.")
            log.warn("The plan agent must list target files in **bold** or `backticks`.")
            log.warn("Skipping prover iteration.")
            return

        # Drop files whose transitive imports failed the previous lake
        # build. plan_validate already filtered these and hinted the
        # planner; the runner enforces it again so a stale PROGRESS.md
        # replayed via --from prover still gets the filter applied.
        if self.block_on_blocked_deps:
            from ..blocked_deps import (
                build_local_import_graph,
                filter_objectives_for_blocked_deps,
                parse_blocked_files_from_log,
            )
            log_path = self.state_dir / "last_lake_build.log"
            blocked = parse_blocked_files_from_log(
                log_path, project_path=self.project_path,
            )
            if blocked:
                graph = build_local_import_graph(self.project_path)
                sorry_files, dropped = filter_objectives_for_blocked_deps(
                    sorry_files,
                    blocked=blocked,
                    graph=graph,
                    project_path=self.project_path,
                )
                if dropped:
                    log.warn(
                        f"Dropped {len(dropped)} objective(s) whose "
                        f"transitive imports failed the previous lake "
                        f"build — they were already noted for the "
                        f"planner via AUTO_NOTES."
                    )
                if not sorry_files:
                    log.warn(
                        "All objectives are blocked by upstream compile "
                        "errors; skipping prover dispatch."
                    )
                    return

        # Drop objectives that name an existing .lean file with zero open
        # sorries — a prover on them quits immediately with no work (the
        # "all 10 provers quit without doing anything" failure). Scaffold
        # dispatches and new files are exempt. plan_validate already
        # hinted the planner; the runner enforces it again so a stale
        # PROGRESS.md replayed via --from prover still gets filtered.
        from ..sorry_count import filter_noop_objectives

        noop_dropped: list[Path] = []
        pipeline_resume = (
            self.pipeline_review is not None and self.resume_enabled
        )
        if (
            not self.stage.strip().lower().startswith("autoformalize")
            and not pipeline_resume
        ):
            sorry_files, noop_dropped = filter_noop_objectives(
                sorry_files,
                progress_file=progress,
                state_dir=self.state_dir,
            )
        if noop_dropped:
            log.warn(
                f"Dropped {len(noop_dropped)} objective(s) naming an "
                f"existing .lean file with zero open sorries (no work to "
                f"do) — already noted for the planner via AUTO_NOTES."
            )
        if not sorry_files:
            log.warn(
                "Every objective was a no-op (zero open sorries); "
                "skipping prover dispatch."
            )
            return

        # A prior prover→Review lane may already have materialized a requested
        # statement redraft. Keep those targets in PROGRESS for the upcoming
        # formalization Review, but do not pay for the same formalizer twice.
        sorry_files, materialized_redrafts = (
            filter_materialized_redrafts_for_dispatch(
                sorry_files,
                state_dir=self.state_dir,
                project_path=self.project_path,
                stage=self.stage,
                enabled=True,
            )
        )
        if materialized_redrafts:
            log.success(
                f"Skipping {len(materialized_redrafts)} already-materialized "
                "pipelined redraft(s); they remain queued for formalization Review."
            )
        if not sorry_files:
            return

        # Hard cap on dispatched provers. plan_validate already warned
        # loudly and queued the deferred list into AUTO_NOTES; we slice
        # here so the dispatcher is deterministic even if plan_validate
        # was bypassed (e.g. --from prover replay of a stale PROGRESS.md
        # that's over the cap).
        if len(sorry_files) > self.max_objectives:
            log.warn(
                f"PROGRESS.md lists {len(sorry_files)} objectives — "
                f"capping dispatch at {self.max_objectives}. The remaining "
                f"{len(sorry_files) - self.max_objectives} files are "
                f"already queued for the next plan agent via AUTO_NOTES."
            )
            sorry_files = sorry_files[: self.max_objectives]

        file_count = len(sorry_files)

        if dry_run:
            for f in sorry_files:
                mode = select_prover_mode_for_target(
                    self.state_dir, self.stage, self.project_path, f,
                    explicit_mode=file_modes.get(str(f)),
                )
                mode_tag = f" (mode: {mode})" if mode else ""
                log.step(f"dry-run Prover: {relpath(f, self.project_path)}{mode_tag}")
            return

        if materialized_redrafts:
            # Their target-scoped reports were written after the preceding
            # iteration's archive and are evidence for the imminent Review.
            log.info("Preserving task_results for pipelined redraft Review")
        else:
            archive_task_results(self.state_dir, self.iter_dir)

        if file_count == 1 and self.pipeline_review is None:
            self._run_single_file(sorry_files[0], mode_name=file_modes.get(str(sorry_files[0])))
            return

        self._run_fanout(sorry_files, file_modes=file_modes)

    def _run_single_file(self, target: Path, mode_name: str | None = None) -> None:
        # Fall back to the stage's default mode when the objective carried no
        # explicit [prover-mode: …] tag (modes replaced the static prompts).
        mode_name = select_prover_mode_for_target(
            self.state_dir, self.stage, self.project_path, target,
            explicit_mode=mode_name,
        )
        rel = relpath(target, self.project_path)
        slug = file_slug(rel)
        log.info(f"Only 1 file ({rel}) — running serial prover")

        prover_log = self.iter_dir / "provers" / slug
        meta_update: dict[str, object] = {
            f"provers.{slug}.file": rel,
            f"provers.{slug}.status": "running",
        }
        if mode_name:
            meta_update[f"provers.{slug}.mode"] = mode_name
        write_meta(self.iter_meta, **meta_update)

        snap_dir = self.iter_dir / "snapshots" / slug
        snapshot_baseline(target, snap_dir)

        mode_content = _load_mode_content(self.state_dir, mode_name)
        base_prompt = build_parallel_prover_prompt(
            self.project_name, self.project_path, self.state_dir, self.stage,
            self.iter_num,
            assigned_rel_lean_path=rel,
            debug_feedback=self.debug_feedback,
            mode_name=mode_name,
            mode_content=mode_content,
        )
        prompt = f"{base_prompt}\nYour assigned file: {rel}"
        resume_sid = pick_resume_session(
            self.iter_meta, f"provers.{slug}.sessionId",
            enabled=self.resume_enabled, label=f"prover[{slug}]",
            cwd=self.project_path,
            jsonl_fallback=Path(str(prover_log) + ".jsonl"),
        )
        with ProverEnvironment(
            snap_dir=snap_dir,
            prover_jsonl=Path(str(prover_log) + ".jsonl"),
            project_path=self.project_path,
        ):
            ok = build_runner(
                role="prover", model=self.model, descriptor=self.harness,
                backend=self.backend,
            ).run(
                PROVER_CONTINUE if resume_sid else prompt,
                cwd=self.project_path,
                log_base=prover_log, verbose_logs=self.verbose_logs,
                resume_session_id=resume_sid,
            )

        persist_session_id(
            self.iter_meta, Path(str(prover_log) + ".jsonl"),
            f"provers.{slug}.sessionId",
        )
        write_meta(
            self.iter_meta,
            **{f"provers.{slug}.status": "done" if ok else "error"},
        )

    def _run_fanout(self, sorry_files: list[Path], *, file_modes: dict[str, str | None] | None = None) -> None:
        file_count = len(sorry_files)
        log.info(
            f"Found {file_count} file(s) — launching parallel provers "
            f"(max {self.max_parallel} concurrent)"
        )

        log.info("Watch progress:")
        if self.dashboard_url:
            log.step(f"Dashboard:       {self.dashboard_url}")
            log.step(f"Iteration view:  {self.dashboard_url}/logs")
        if self.blueprint_url:
            log.step(f"Blueprint:       {self.blueprint_url}")
        log.step(f"tail -f {self.iter_dir}/provers/*.jsonl")
        log.step(f"watch -n10 'ls -lt {self.state_dir}/task_results/'")

        if self.pipeline_review is not None:
            self._run_pipelined_fanout(
                sorry_files, file_modes=file_modes,
            )
            return

        file_modes = file_modes or {}
        futures = {}
        prover_logs: dict[str, Path] = {}
        with ProcessPoolExecutor(
            max_workers=min(self.max_parallel, file_count),
        ) as pool:
            for f in sorry_files:
                rel = relpath(f, self.project_path)
                slug = file_slug(rel)
                prover_log = self.iter_dir / "provers" / slug
                prover_logs[slug] = prover_log

                mode_name = select_prover_mode_for_target(
                    self.state_dir, self.stage, self.project_path, f,
                    explicit_mode=file_modes.get(str(f)),
                )
                mode_content = _load_mode_content(self.state_dir, mode_name)
                base_prompt = build_parallel_prover_prompt(
                    self.project_name, self.project_path, self.state_dir, self.stage,
                    self.iter_num,
                    assigned_rel_lean_path=rel,
                    debug_feedback=self.debug_feedback,
                    mode_name=mode_name,
                    mode_content=mode_content,
                )
                prompt = f"{base_prompt}\nYour assigned file: {rel}"

                snap_dir = self.iter_dir / "snapshots" / slug
                snapshot_baseline(f, snap_dir)

                # Per-slug resume: each parallel prover keeps its own
                # session id under provers.<slug>.sessionId. Files added
                # in this round that weren't part of the prior run have
                # no stored id; pick_resume_session degrades to fresh
                # (or recovers from the slug's JSONL fallback if the
                # prior run crashed mid-prove).
                resume_sid = pick_resume_session(
                    self.iter_meta, f"provers.{slug}.sessionId",
                    enabled=self.resume_enabled, label=f"prover[{slug}]",
                    cwd=self.project_path,
                    jsonl_fallback=Path(str(prover_log) + ".jsonl"),
                )
                if resume_sid:
                    submit_prompt = PROVER_CONTINUE
                else:
                    submit_prompt = prompt

                log.step(f"Starting prover for {rel}")
                meta_update: dict[str, object] = {
                    f"provers.{slug}.file": rel,
                    f"provers.{slug}.status": "running",
                }
                if mode_name:
                    meta_update[f"provers.{slug}.mode"] = mode_name
                write_meta(self.iter_meta, **meta_update)

                future = pool.submit(
                    _run_single_prover,
                    submit_prompt, self.project_path, prover_log,
                    self.verbose_logs, self.model,
                    snap_dir, self.project_path, resume_sid,
                    self.backend, self.harness,
                )
                futures[future] = (rel, slug)

            failed = 0
            for future in as_completed(futures):
                rel, slug = futures[future]
                try:
                    ok = future.result()
                except QuotaExhaustedError:
                    raise  # propagate — stop the loop immediately
                except Exception:
                    ok = False
                # Stamp the session id from the prover's JSONL — works
                # whether this was a fresh run or a --resume continuation
                # (Claude reports the same session id back on resume, so
                # the next --resume keeps targeting the same conversation).
                persist_session_id(
                    self.iter_meta,
                    Path(str(prover_logs[slug]) + ".jsonl"),
                    f"provers.{slug}.sessionId",
                )
                status = "done" if ok else "error"
                write_meta(self.iter_meta, **{f"provers.{slug}.status": status})
                if ok:
                    log.success(f"Prover finished: {rel}")
                else:
                    log.error(f"Prover failed: {rel}")
                    failed += 1

        if failed:
            log.warn(f"{failed}/{file_count} prover(s) had errors")
        else:
            log.success(f"All {file_count} prover(s) finished")

        results_dir = self.state_dir / "task_results"
        result_count = len(list(results_dir.glob("*.md"))) if results_dir.exists() else 0
        log.info(f"Task result files: {result_count}/{file_count}")

        self._emit_round_end(file_count, failed)

    def _run_pipelined_fanout(
        self,
        sorry_files: list[Path],
        *,
        file_modes: dict[str, str | None] | None = None,
    ) -> None:
        """Share one bounded pool between prover, Review, and redraft work."""
        config = self.pipeline_review
        if config is None:
            raise RuntimeError("pipelined fanout requires Review configuration")

        file_modes = file_modes or {}
        file_count = len(sorry_files)
        workers = max(1, min(self.max_parallel, file_count))
        review_jobs = max(1, min(config.requested_jobs, workers))
        max_attempts = max(1, int(config.max_attempts))
        full_pipeline = bool(config.formalization_review_enabled)
        formalization_max_attempts = max(
            1, int(config.formalization_review_max_attempts),
        )
        formalization_max_iterations = max(
            1, int(config.formalization_review_max_iterations),
        )
        proof_max_iterations = max(1, int(config.proof_review_max_iterations))
        prior_state = load_proof_review_state(self.state_dir)
        prior_targets = prior_state.get("targets", {})
        if not isinstance(prior_targets, dict):
            prior_targets = {}
        prior_formalization_state = (
            load_formalization_review_state(self.state_dir) or {}
        )
        prior_formalization_targets = prior_formalization_state.get("targets", {})
        if not isinstance(prior_formalization_targets, dict):
            prior_formalization_targets = {}

        pending_provers: deque[tuple[Path, int]] = deque()
        resumed_completed: list[tuple[Path, str, str]] = []
        proof_cycles: dict[str, int] = {}
        formalization_cycles: dict[str, int] = {}
        shadow_proof_attempts: dict[str, int] = {}
        shadow_proof_records: dict[str, dict] = {}
        shadow_formalization_reviews: dict[str, int] = {}
        shadow_formalization_records: dict[str, dict] = {}
        for target in sorry_files:
            rel = relpath(target, self.project_path)
            slug = file_slug(rel)
            proof_cycles[rel] = 1
            formalization_cycles[rel] = 0
            prior_proof = prior_targets.get(rel)
            prior_proof = prior_proof if isinstance(prior_proof, dict) else {}
            shadow_proof_attempts[rel] = int(prior_proof.get("attempts") or 0)
            shadow_proof_records[rel] = dict(prior_proof)
            prior_formalization = prior_formalization_targets.get(rel)
            prior_formalization = (
                prior_formalization
                if isinstance(prior_formalization, dict) else {}
            )
            shadow_formalization_reviews[rel] = int(
                prior_formalization.get("reviews") or 0
            )
            shadow_formalization_records[rel] = dict(prior_formalization)
            prior_status = (
                read_meta(self.iter_meta, f"provers.{slug}.status")
                if self.resume_enabled else None
            )
            if prior_status == "done":
                resumed_completed.append((target, rel, slug))
            else:
                pending_provers.append((target, 1))
        review_queue: list[
            tuple[float, int, Path, str, str, int, int]
        ] = []
        formalizer_queue: deque[
            tuple[Path, str, str, int, dict, str]
        ] = deque()
        formalization_review_queue: list[
            tuple[float, int, Path, str, str, int, int]
        ] = []
        sequence = count()
        futures: dict[object, _PipelineWork] = {}
        outcomes: dict[str, TargetReviewOutcome] = {}
        preflight_rows: dict[str, dict] = {}
        formalizer_results: dict[str, dict] = {}
        formalizer_history: dict[str, list[dict]] = {}
        gate_events: list[dict] = []
        pending_formalization: set[str] = set()
        unresolved: dict[str, str] = {}
        review_rounds: dict[int, dict[str, int]] = {}
        formalization_review_rounds: dict[
            tuple[int, int], dict[str, int]
        ] = {}
        active_reviews = 0
        failed = 0
        started = time.monotonic()
        target_rels = sorted(relpath(path, self.project_path) for path in sorry_files)

        log.info(
            "Pipelined target Review enabled: each completed prover is "
            "reviewed immediately, and needs_redraft starts that target's "
            "formalizer immediately; combined concurrency "
            f"is capped at {workers}."
        )
        if full_pipeline:
            log.info(
                "Full target loop enabled: each materialized redraft gets an "
                "immediate formalization Review and a passing target is "
                "re-enqueued to prover without a phase barrier."
            )
        write_meta(self.iter_meta, **{
            "prover.pipelineReviewEnabled": True,
            "prover.pipelineImmediateRedraftEnabled": True,
            "prover.pipelineFormalizationReviewEnabled": full_pipeline,
            "prover.pipelineReviewMaxCombined": workers,
            "prover.pipelineReviewMaxReviewers": review_jobs,
        })
        write_pipelined_review_report(
            iter_dir=self.iter_dir,
            report={
                "iteration": self.iter_num,
                "complete": False,
                "status": "running",
                "target_files": target_rels,
                "targets": file_count,
                "reviewed": 0,
                "unresolved": target_rels,
                "gate_events_applied": False,
                "formalization_reviews": {"reviewed": 0, "unresolved": []},
                "formalizers": {"requested": 0, "materialized": 0, "failed": 0},
            },
        )

        def enqueue_review(
            target: Path,
            rel: str,
            slug: str,
            attempt: int,
            cycle: int,
            *,
            delay: float = 0.0,
        ) -> None:
            heapq.heappush(
                review_queue,
                (
                    time.monotonic() + max(0.0, delay),
                    next(sequence),
                    target,
                    rel,
                    slug,
                    attempt,
                    cycle,
                ),
            )

        def run_preflight(target: Path, rel: str) -> dict:
            try:
                return self.preflight_checker(
                    project_path=self.project_path,
                    target=target,
                    timeout_sec=config.preflight_timeout_sec,
                )
            except Exception as exc:
                return {
                    "file": rel,
                    "status": "error",
                    "compiles": False,
                    "returncode": None,
                    "sorry_count": None,
                    "duration_secs": 0.0,
                    "diagnostics": f"{type(exc).__name__}: {exc}",
                }

        if resumed_completed:
            preflight_jobs = min(review_jobs, len(resumed_completed))
            log.info(
                f"Resume detected {len(resumed_completed)} completed prover "
                "lane(s); skipping re-proving and preparing their Reviews."
            )
            with ThreadPoolExecutor(max_workers=preflight_jobs) as check_pool:
                checks = {
                    check_pool.submit(run_preflight, target, rel): (
                        target, rel, slug,
                    )
                    for target, rel, slug in resumed_completed
                }
                for future in as_completed(checks):
                    target, rel, slug = checks[future]
                    preflight_rows[rel] = future.result()
                    enqueue_review(target, rel, slug, 1, 1)

        def submit_prover(pool, target: Path, cycle: int) -> None:
            rel = relpath(target, self.project_path)
            slug = file_slug(rel)
            prover_log = self.iter_dir / "provers" / slug
            mode_name = select_prover_mode_for_target(
                self.state_dir,
                self.stage,
                self.project_path,
                target,
                explicit_mode=file_modes.get(str(target)),
            )
            mode_content = _load_mode_content(self.state_dir, mode_name)
            base_prompt = build_parallel_prover_prompt(
                self.project_name,
                self.project_path,
                self.state_dir,
                self.stage,
                self.iter_num,
                assigned_rel_lean_path=rel,
                debug_feedback=self.debug_feedback,
                mode_name=mode_name,
                mode_content=mode_content,
            )
            prompt = f"{base_prompt}\nYour assigned file: {rel}"
            snap_dir = self.iter_dir / "snapshots" / slug
            snapshot_baseline(target, snap_dir)
            resume_sid = pick_resume_session(
                self.iter_meta,
                f"provers.{slug}.sessionId",
                enabled=self.resume_enabled and cycle == 1,
                label=f"prover[{slug}]",
                cwd=self.project_path,
                jsonl_fallback=Path(str(prover_log) + ".jsonl"),
            )
            submit_prompt = PROVER_CONTINUE if resume_sid else prompt
            meta_update: dict[str, object] = {
                f"provers.{slug}.file": rel,
                f"provers.{slug}.status": "running",
                f"provers.{slug}.cycle": cycle,
            }
            if mode_name:
                meta_update[f"provers.{slug}.mode"] = mode_name
            write_meta(self.iter_meta, **meta_update)
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting prover for {rel}{cycle_label}")
            future = pool.submit(
                self.prover_worker,
                submit_prompt,
                self.project_path,
                prover_log,
                self.verbose_logs,
                self.model,
                snap_dir,
                self.project_path,
                resume_sid,
                self.backend,
                self.harness,
            )
            futures[future] = _PipelineWork(
                kind="prover", target=target, rel=rel, slug=slug, cycle=cycle,
            )

        def submit_review(
            pool,
            target: Path,
            rel: str,
            slug: str,
            attempt: int,
            cycle: int,
        ) -> None:
            nonlocal active_reviews
            output_dir = (
                self.iter_dir / "review-targets" / slug
                / f"cycle-{cycle}" / f"attempt-{attempt}"
            )
            prompt = build_target_review_prompt(
                project_path=self.project_path,
                state_dir=self.state_dir,
                iter_dir=self.iter_dir,
                iter_num=self.iter_num,
                target=target,
                output_dir=output_dir,
                preflight=preflight_rows.get(rel, {}),
                prior_gate_record=shadow_proof_records.get(rel) or None,
            )
            spec = TargetReviewSpec(
                rel=rel,
                prompt=prompt,
                output_dir=str(output_dir),
                log_base=str(output_dir / "agent"),
                attempt=attempt,
            )
            future = pool.submit(
                self.review_worker,
                spec,
                project_path=self.project_path,
                verbose_logs=self.verbose_logs,
                model=self.model,
                backend=self.backend,
                harness=config.harness or self.harness,
            )
            futures[future] = _PipelineWork(
                kind="review",
                target=target,
                rel=rel,
                slug=slug,
                attempt=attempt,
                cycle=cycle,
            )
            active_reviews += 1
            stats = review_rounds.setdefault(
                attempt,
                {"attempt": attempt, "submitted": 0, "completed": 0, "failed": 0},
            )
            stats["submitted"] += 1
            write_meta(self.iter_meta, **{
                f"pipelineReviews.{slug}.status": "running",
                f"pipelineReviews.{slug}.attempt": attempt,
                f"pipelineReviews.{slug}.cycle": cycle,
            })
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting immediate proof Review for {rel}{cycle_label}")

        def submit_formalizer(
            pool,
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            certificate: dict,
            handoff_label: str,
        ) -> None:
            formalizer_log = self.iter_dir / "formalizers" / slug
            snap_dir = self.iter_dir / "formalizer-snapshots" / slug
            baseline_sha256 = _target_sha256(target)
            baseline_results = _task_result_fingerprints(self.state_dir, rel)
            snapshot_baseline(target, snap_dir)
            prompt = build_immediate_redraft_prompt(
                project_name=self.project_name,
                project_path=self.project_path,
                state_dir=self.state_dir,
                iter_num=self.iter_num,
                target=target,
                review_certificate=certificate,
                debug_feedback=self.debug_feedback,
                handoff_label=handoff_label,
            )
            resume_sid = pick_resume_session(
                self.iter_meta,
                f"pipelineFormalizers.{slug}.sessionId",
                enabled=self.resume_enabled and cycle == 1,
                label=f"formalizer[{slug}]",
                cwd=self.project_path,
                jsonl_fallback=Path(str(formalizer_log) + ".jsonl"),
            )
            submit_prompt = PROVER_CONTINUE if resume_sid else prompt
            write_meta(self.iter_meta, **{
                f"pipelineFormalizers.{slug}.file": rel,
                f"pipelineFormalizers.{slug}.status": "running",
                f"pipelineFormalizers.{slug}.reviewAttempt": cycle,
                f"pipelineFormalizers.{slug}.cycle": cycle,
            })
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting immediate formalizer for {rel}{cycle_label}")
            future = pool.submit(
                self.formalizer_worker,
                submit_prompt,
                self.project_path,
                formalizer_log,
                self.verbose_logs,
                self.model,
                snap_dir,
                self.project_path,
                resume_sid,
                self.backend,
                config.formalizer_harness or self.harness,
            )
            futures[future] = _PipelineWork(
                kind="formalizer",
                target=target,
                rel=rel,
                slug=slug,
                attempt=cycle,
                cycle=cycle,
                baseline_sha256=baseline_sha256,
                result_fingerprints=tuple(sorted(baseline_results.items())),
            )

        def enqueue_formalization_review(
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            attempt: int,
            *,
            delay: float = 0.0,
        ) -> None:
            heapq.heappush(
                formalization_review_queue,
                (
                    time.monotonic() + max(0.0, delay),
                    next(sequence),
                    target,
                    rel,
                    slug,
                    cycle,
                    attempt,
                ),
            )

        def submit_formalization_review(
            pool,
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            attempt: int,
        ) -> None:
            nonlocal active_reviews
            output_dir = (
                self.iter_dir / "formalization-review-targets" / slug
                / f"cycle-{cycle}" / f"attempt-{attempt}"
            )
            prompt = build_target_formalization_review_prompt(
                project_path=self.project_path,
                state_dir=self.state_dir,
                iter_dir=self.iter_dir,
                iter_num=self.iter_num,
                target=target,
                output_dir=output_dir,
                preflight=preflight_rows.get(rel, {}),
                prior_gate_record=shadow_formalization_records.get(rel),
            )
            spec = TargetReviewSpec(
                rel=rel,
                prompt=prompt,
                output_dir=str(output_dir),
                log_base=str(output_dir / "agent"),
                attempt=attempt,
            )
            future = pool.submit(
                self.formalization_review_worker,
                spec,
                project_path=self.project_path,
                verbose_logs=self.verbose_logs,
                model=self.model,
                backend=self.backend,
                harness=config.harness or self.harness,
            )
            futures[future] = _PipelineWork(
                kind="formalization_review",
                target=target,
                rel=rel,
                slug=slug,
                attempt=attempt,
                cycle=cycle,
            )
            active_reviews += 1
            key = (cycle, attempt)
            stats = formalization_review_rounds.setdefault(
                key,
                {
                    "cycle": cycle,
                    "attempt": attempt,
                    "submitted": 0,
                    "completed": 0,
                    "failed": 0,
                },
            )
            stats["submitted"] += 1
            write_meta(self.iter_meta, **{
                f"pipelineFormalizationReviews.{slug}.status": "running",
                f"pipelineFormalizationReviews.{slug}.cycle": cycle,
                f"pipelineFormalizationReviews.{slug}.attempt": attempt,
            })
            log.step(
                f"Starting immediate formalization Review for {rel} "
                f"(cycle {cycle})"
            )

        def fill_slots(pool) -> None:
            while len(futures) < workers:
                now = time.monotonic()
                formalization_review_ready = (
                    bool(formalization_review_queue)
                    and formalization_review_queue[0][0] <= now
                    and active_reviews < review_jobs
                )
                review_ready = (
                    bool(review_queue)
                    and review_queue[0][0] <= now
                    and active_reviews < review_jobs
                )
                if formalization_review_ready:
                    _, _, target, rel, slug, cycle, attempt = heapq.heappop(
                        formalization_review_queue
                    )
                    submit_formalization_review(
                        pool, target, rel, slug, cycle, attempt,
                    )
                elif review_ready:
                    _, _, target, rel, slug, attempt, cycle = heapq.heappop(
                        review_queue
                    )
                    submit_review(pool, target, rel, slug, attempt, cycle)
                elif formalizer_queue:
                    target, rel, slug, cycle, certificate, handoff_label = (
                        formalizer_queue.popleft()
                    )
                    submit_formalizer(
                        pool,
                        target,
                        rel,
                        slug,
                        cycle,
                        certificate,
                        handoff_label,
                    )
                elif pending_provers:
                    target, cycle = pending_provers.popleft()
                    submit_prover(pool, target, cycle)
                else:
                    break

        with self.executor_factory(max_workers=workers) as pool:
            fill_slots(pool)
            while (
                futures
                or pending_provers
                or review_queue
                or formalizer_queue
                or formalization_review_queue
            ):
                fill_slots(pool)
                if not futures:
                    due_times = [
                        queue[0][0]
                        for queue in (review_queue, formalization_review_queue)
                        if queue
                    ]
                    delay = max(0.0, min(due_times) - time.monotonic())
                    if delay:
                        time.sleep(delay)
                    continue

                timeout = None
                delayed_reviews = [
                    queue[0][0]
                    for queue in (review_queue, formalization_review_queue)
                    if queue
                ]
                if delayed_reviews and active_reviews < review_jobs:
                    timeout = max(
                        0.0, min(delayed_reviews) - time.monotonic(),
                    )
                done, _ = wait(
                    tuple(futures),
                    timeout=timeout,
                    return_when=FIRST_COMPLETED,
                )
                if not done:
                    continue

                for future in done:
                    work = futures.pop(future)
                    if work.kind == "prover":
                        try:
                            ok = bool(future.result())
                        except QuotaExhaustedError:
                            raise
                        except Exception:
                            ok = False
                        prover_log = self.iter_dir / "provers" / work.slug
                        persist_session_id(
                            self.iter_meta,
                            Path(str(prover_log) + ".jsonl"),
                            f"provers.{work.slug}.sessionId",
                        )
                        status = "done" if ok else "error"
                        write_meta(
                            self.iter_meta,
                            **{f"provers.{work.slug}.status": status},
                        )
                        if ok:
                            log.success(f"Prover finished: {work.rel}")
                        else:
                            failed += 1
                            log.error(f"Prover failed: {work.rel}")
                        preflight = run_preflight(work.target, work.rel)
                        preflight_rows[work.rel] = preflight
                        enqueue_review(
                            work.target, work.rel, work.slug, 1, work.cycle,
                        )
                        continue

                    if work.kind == "formalizer":
                        runner_error = ""
                        try:
                            runner_ok = bool(future.result())
                        except QuotaExhaustedError:
                            raise
                        except Exception as exc:
                            runner_ok = False
                            runner_error = f"{type(exc).__name__}: {exc}"
                        formalizer_log = (
                            self.iter_dir / "formalizers" / work.slug
                        )
                        persist_session_id(
                            self.iter_meta,
                            Path(str(formalizer_log) + ".jsonl"),
                            f"pipelineFormalizers.{work.slug}.sessionId",
                        )
                        digest = _target_sha256(work.target)
                        changed = bool(
                            digest
                            and work.baseline_sha256
                            and digest != work.baseline_sha256
                        )
                        postflight = run_preflight(work.target, work.rel)
                        compiles = bool(postflight.get("compiles"))
                        before_results = dict(work.result_fingerprints)
                        after_results = _task_result_fingerprints(
                            self.state_dir, work.rel,
                        )
                        result_updated = any(
                            before_results.get(path) != digest
                            for path, digest in after_results.items()
                        )
                        materialized = changed and compiles and result_updated
                        errors = [runner_error] if runner_error else []
                        if not changed:
                            errors.append("formalizer did not change the Lean target")
                        if not compiles:
                            errors.append("redrafted Lean target did not compile")
                        if not result_updated:
                            errors.append("formalizer did not update its task result")
                        result = {
                            "iteration": self.iter_num,
                            "file": work.rel,
                            "cycle": work.cycle,
                            "status": "materialized" if materialized else "error",
                            "review_attempt": work.attempt,
                            "runner_ok": runner_ok,
                            "baseline_sha256": work.baseline_sha256,
                            "lean_sha256": digest,
                            "changed": changed,
                            "task_result_updated": result_updated,
                            "task_result_fingerprints": after_results,
                            "preflight": postflight,
                            "error": "; ".join(errors),
                        }
                        formalizer_results[work.rel] = result
                        formalizer_history.setdefault(work.rel, []).append(result)
                        preflight_rows[work.rel] = postflight
                        write_meta(self.iter_meta, **{
                            f"pipelineFormalizers.{work.slug}.status": (
                                "materialized" if materialized else "error"
                            ),
                            f"pipelineFormalizers.{work.slug}.runnerOk": runner_ok,
                            f"pipelineFormalizers.{work.slug}.changed": changed,
                            f"pipelineFormalizers.{work.slug}.compiles": compiles,
                            f"pipelineFormalizers.{work.slug}.taskResultUpdated": (
                                result_updated
                            ),
                            f"pipelineFormalizers.{work.slug}.leanSha256": digest,
                            f"pipelineFormalizers.{work.slug}.error": "; ".join(errors),
                        })
                        if materialized:
                            log.success(
                                f"Immediate formalizer materialized: {work.rel}"
                            )
                            if full_pipeline:
                                enqueue_formalization_review(
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    work.cycle,
                                    1,
                                )
                        else:
                            pending_formalization.add(work.rel)
                            log.error(
                                f"Immediate formalizer incomplete: {work.rel}; "
                                f"{'; '.join(errors)}"
                            )
                        continue

                    if work.kind == "formalization_review":
                        active_reviews -= 1
                        try:
                            outcome = future.result()
                        except Exception as exc:
                            outcome = TargetReviewOutcome(
                                rel=work.rel,
                                attempt=work.attempt,
                                runner_ok=False,
                                milestone=None,
                                error=f"{type(exc).__name__}: {exc}",
                            )
                        stats = formalization_review_rounds[
                            (work.cycle, work.attempt)
                        ]
                        if (
                            isinstance(outcome, TargetReviewOutcome)
                            and outcome.rel == work.rel
                            and outcome.milestone is not None
                        ):
                            stats["completed"] += 1
                            decision, reason, certificate = (
                                formalization_review_decision(outcome.milestone)
                            )
                            reviews = shadow_formalization_reviews[work.rel] + 1
                            shadow_formalization_reviews[work.rel] = reviews
                            if decision == "passed":
                                status = "passed"
                            elif reviews >= formalization_max_iterations:
                                status = "review_exhausted"
                            else:
                                status = "retry"
                            shadow_formalization_records[work.rel] = {
                                **shadow_formalization_records.get(work.rel, {}),
                                "status": status,
                                "reviews": reviews,
                                "reason": reason,
                                "certificate": certificate,
                            }
                            event_id = (
                                f"pipeline:{self.iter_num}:{work.rel}:"
                                f"formalization:{work.cycle}"
                            )
                            gate_events.append({
                                "kind": "formalization",
                                "event_id": event_id,
                                "target": work.target,
                                "rel": work.rel,
                                "cycle": work.cycle,
                                "milestone": outcome.milestone,
                            })
                            write_meta(self.iter_meta, **{
                                f"pipelineFormalizationReviews.{work.slug}.status": (
                                    status
                                ),
                                f"pipelineFormalizationReviews.{work.slug}.reviews": (
                                    reviews
                                ),
                                f"pipelineFormalizationReviews.{work.slug}.reason": (
                                    reason
                                ),
                            })
                            log.success(
                                "Formalization Review finished: "
                                f"{work.rel} ({status}, {reviews}/"
                                f"{formalization_max_iterations})"
                            )
                            if status == "passed":
                                pending_formalization.discard(work.rel)
                                shadow_proof_attempts[work.rel] = 0
                                shadow_proof_records[work.rel] = {
                                    **shadow_proof_records.get(work.rel, {}),
                                    "status": "retry",
                                    "attempts": 0,
                                    "reason": (
                                        "formalization redraft passed; proof "
                                        "attempt budget reset"
                                    ),
                                }
                                next_cycle = proof_cycles[work.rel] + 1
                                proof_cycles[work.rel] = next_cycle
                                pending_provers.append((work.target, next_cycle))
                                log.step(
                                    "Formalization Review passed; immediately "
                                    f"re-enqueued prover for {work.rel}"
                                )
                            elif status == "retry":
                                next_cycle = formalization_cycles[work.rel] + 1
                                formalization_cycles[work.rel] = next_cycle
                                raw_certificate = outcome.milestone.get(
                                    "formalization_review"
                                )
                                handoff = (
                                    dict(raw_certificate)
                                    if isinstance(raw_certificate, dict)
                                    else dict(outcome.milestone)
                                )
                                formalizer_queue.append((
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    next_cycle,
                                    handoff,
                                    "formalization Review",
                                ))
                            else:
                                pending_formalization.discard(work.rel)
                        else:
                            stats["failed"] += 1
                            error = (
                                outcome.error
                                if isinstance(outcome, TargetReviewOutcome)
                                else "invalid formalization Review worker outcome"
                            )
                            if work.attempt < formalization_max_attempts:
                                enqueue_formalization_review(
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    work.cycle,
                                    work.attempt + 1,
                                    delay=(
                                        config.formalization_review_backoff_sec
                                        * work.attempt
                                    ),
                                )
                            else:
                                pending_formalization.add(work.rel)
                                write_meta(self.iter_meta, **{
                                    f"pipelineFormalizationReviews.{work.slug}.status": "error",
                                    f"pipelineFormalizationReviews.{work.slug}.error": error,
                                })
                                log.error(
                                    "Formalization Review failed after "
                                    f"{formalization_max_attempts} harness "
                                    f"attempt(s): {work.rel}"
                                )
                        continue

                    active_reviews -= 1
                    try:
                        outcome = future.result()
                    except Exception as exc:
                        outcome = TargetReviewOutcome(
                            rel=work.rel,
                            attempt=work.attempt,
                            runner_ok=False,
                            milestone=None,
                            error=f"{type(exc).__name__}: {exc}",
                        )
                    stats = review_rounds[work.attempt]
                    if (
                        isinstance(outcome, TargetReviewOutcome)
                        and outcome.rel == work.rel
                        and outcome.milestone is not None
                    ):
                        outcomes[work.rel] = outcome
                        stats["completed"] += 1
                        certificate = outcome.milestone.get("proof_review")
                        route, reason, evidence, redraft_kind, _explicit = (
                            proof_review_decision(outcome.milestone)
                        )
                        if full_pipeline:
                            shadow_proof_attempts[work.rel] += 1
                            attempts = shadow_proof_attempts[work.rel]
                            if route == "solved":
                                proof_status = "solved"
                            elif route == "needs_redraft":
                                proof_status = "needs_redraft"
                            elif route == "blocked_infrastructure":
                                proof_status = "blocked_infrastructure"
                            elif attempts >= proof_max_iterations:
                                proof_status = "proof_review_exhausted"
                            else:
                                proof_status = "retry"
                            shadow_proof_records[work.rel] = {
                                **shadow_proof_records.get(work.rel, {}),
                                "status": proof_status,
                                "attempts": attempts,
                                "reason": reason,
                                "evidence": evidence,
                                "redraft_kind": redraft_kind,
                            }
                            event_id = (
                                f"pipeline:{self.iter_num}:{work.rel}:"
                                f"proof:{work.cycle}"
                            )
                            gate_events.append({
                                "kind": "proof",
                                "event_id": event_id,
                                "target": work.target,
                                "rel": work.rel,
                                "cycle": work.cycle,
                                "milestone": outcome.milestone,
                            })
                        write_meta(self.iter_meta, **{
                            f"pipelineReviews.{work.slug}.status": "done",
                            f"pipelineReviews.{work.slug}.route": route,
                        })
                        log.success(f"Proof Review finished: {work.rel} ({route})")
                        if route == "needs_redraft" and isinstance(certificate, dict):
                            budget_available = (
                                not full_pipeline
                                or shadow_formalization_reviews[work.rel]
                                < formalization_max_iterations
                            )
                            if budget_available:
                                shadow_formalization_records[work.rel] = {
                                    **shadow_formalization_records.get(
                                        work.rel, {}
                                    ),
                                    "status": "retry",
                                    "reason": f"proof Review redraft: {reason}",
                                    "certificate": {},
                                    "redraft_kind": redraft_kind,
                                }
                                pending_formalization.add(work.rel)
                                next_cycle = formalization_cycles[work.rel] + 1
                                formalization_cycles[work.rel] = next_cycle
                                formalizer_queue.append((
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    next_cycle,
                                    dict(certificate),
                                    "proof Review",
                                ))
                                write_meta(self.iter_meta, **{
                                    f"pipelineFormalizers.{work.slug}.status": (
                                        "queued"
                                    ),
                                    f"pipelineFormalizers.{work.slug}.cycle": (
                                        next_cycle
                                    ),
                                })
                            else:
                                pending_formalization.discard(work.rel)
                                log.warn(
                                    "Formalization Review budget exhausted; "
                                    f"cannot redraft {work.rel} after proof "
                                    f"Review: {reason}"
                                )
                    else:
                        stats["failed"] += 1
                        error = (
                            outcome.error
                            if isinstance(outcome, TargetReviewOutcome)
                            else "invalid Review worker outcome"
                        )
                        if work.attempt < max_attempts:
                            write_meta(self.iter_meta, **{
                                f"pipelineReviews.{work.slug}.status": "retrying",
                                f"pipelineReviews.{work.slug}.error": error,
                            })
                            enqueue_review(
                                work.target,
                                work.rel,
                                work.slug,
                                work.attempt + 1,
                                work.cycle,
                                delay=config.backoff_sec * work.attempt,
                            )
                        else:
                            unresolved[work.rel] = error
                            write_meta(self.iter_meta, **{
                                f"pipelineReviews.{work.slug}.status": "error",
                                f"pipelineReviews.{work.slug}.error": error,
                            })
                            log.error(
                                f"Proof Review failed after {max_attempts} "
                                f"harness attempt(s): {work.rel}"
                            )

        complete = not unresolved and len(outcomes) == file_count
        session_dir = (
            self.state_dir / "proof-journal" / "sessions"
            / f"session_{self.iter_num}"
        )
        if complete:
            write_parallel_review_session(
                session_dir=session_dir,
                iter_num=self.iter_num,
                outcomes=outcomes,
            )
        gate_events_applied = False
        proof_gate_result = {
            "solved": [],
            "retry": [],
            "needs_redraft": [],
            "blocked_infrastructure": [],
            "exhausted": [],
            "reviewed": [],
        }
        formalization_gate_result = {
            "passed": [],
            "retry": [],
            "exhausted": [],
            "reviewed": [],
        }
        if complete and full_pipeline:
            for event in gate_events:
                if event["kind"] == "proof":
                    update = apply_target_proof_review(
                        state_dir=self.state_dir,
                        project_path=self.project_path,
                        target=event["target"],
                        milestone=event["milestone"],
                        iter_num=self.iter_num,
                        max_iterations=proof_max_iterations,
                        event_id=event["event_id"],
                    )
                    if update.route == "needs_redraft":
                        reopen_formalization_targets(
                            state_dir=self.state_dir,
                            project_path=self.project_path,
                            progress_file=self.state_dir / "PROGRESS.md",
                            redrafts={
                                update.rel: {
                                    "reason": update.reason,
                                    "redraft_kind": update.redraft_kind,
                                    "pipeline_event_id": event["event_id"],
                                }
                            },
                            iter_num=self.iter_num,
                            max_iterations=formalization_max_iterations,
                            route_progress=False,
                            enforce_budget=True,
                        )
                else:
                    apply_target_formalization_review(
                        state_dir=self.state_dir,
                        project_path=self.project_path,
                        target=event["target"],
                        milestone=event["milestone"],
                        iter_num=self.iter_num,
                        max_iterations=formalization_max_iterations,
                        event_id=event["event_id"],
                    )
            gate_events_applied = True

            proof_state = load_proof_review_state(self.state_dir)
            proof_records = proof_state.get("targets", {})
            proof_records = (
                proof_records if isinstance(proof_records, dict) else {}
            )
            formalization_state = (
                load_formalization_review_state(self.state_dir) or {}
            )
            formalization_records = formalization_state.get("targets", {})
            formalization_records = (
                formalization_records
                if isinstance(formalization_records, dict) else {}
            )
            for rel in target_rels:
                proof_record = proof_records.get(rel)
                proof_status = (
                    str(proof_record.get("status") or "retry")
                    if isinstance(proof_record, dict) else "retry"
                )
                if proof_status == "proof_review_exhausted":
                    proof_gate_result["exhausted"].append(rel)
                elif proof_status in proof_gate_result:
                    proof_gate_result[proof_status].append(rel)
                proof_gate_result["reviewed"].append(rel)

                formalization_record = formalization_records.get(rel)
                formalization_status = (
                    str(formalization_record.get("status") or "")
                    if isinstance(formalization_record, dict) else ""
                )
                if formalization_status == "review_exhausted":
                    formalization_gate_result["exhausted"].append(rel)
                elif formalization_status in {"passed", "retry"}:
                    formalization_gate_result[formalization_status].append(rel)
                if any(
                    event["kind"] == "formalization" and event["rel"] == rel
                    for event in gate_events
                ):
                    formalization_gate_result["reviewed"].append(rel)
                if (
                    proof_status == "needs_redraft"
                    and formalization_status == "retry"
                ):
                    pending_formalization.add(rel)


        checks = [preflight_rows[rel] for rel in sorted(preflight_rows)]
        preflight = {
            "iteration": self.iter_num,
            "jobs": 1,
            "duration_secs": round(sum(
                float(row.get("duration_secs") or 0.0) for row in checks
            ), 3),
            "summary": {
                "total": len(checks),
                "passed": sum(bool(row.get("compiles")) for row in checks),
                "failed": sum(not bool(row.get("compiles")) for row in checks),
            },
            "targets": checks,
        }
        rounds = [review_rounds[key] for key in sorted(review_rounds)]
        formalization_rounds = [
            formalization_review_rounds[key]
            for key in sorted(formalization_review_rounds)
        ]
        formalizer_invocations = [
            result
            for rel in sorted(formalizer_history)
            for result in formalizer_history[rel]
        ]
        materialized_invocations = [
            result
            for result in formalizer_invocations
            if result.get("status") == "materialized"
        ]
        failed_invocations = [
            result
            for result in formalizer_invocations
            if result.get("status") != "materialized"
        ]
        gate_event_summaries = []
        for event in gate_events:
            summary = {
                "kind": event["kind"],
                "event_id": event["event_id"],
                "file": event["rel"],
                "cycle": event["cycle"],
            }
            if event["kind"] == "proof":
                summary["route"] = proof_review_decision(event["milestone"])[0]
            else:
                summary["decision"] = formalization_review_decision(
                    event["milestone"]
                )[0]
            gate_event_summaries.append(summary)
        proof_redrafts_reopened = sorted({
            row["file"]
            for row in gate_event_summaries
            if row.get("kind") == "proof"
            and row.get("route") == "needs_redraft"
        })
        materialized_redrafts = {
            rel: result
            for rel, result in sorted(formalizer_results.items())
            if result.get("status") == "materialized"
        }
        failed_redrafts = {
            rel: result for rel, result in sorted(formalizer_results.items())
            if result.get("status") != "materialized"
        }
        report_path = write_pipelined_review_report(
            iter_dir=self.iter_dir,
            report={
                "iteration": self.iter_num,
                "complete": complete,
                "status": "complete" if complete else "incomplete",
                "target_files": sorted(preflight_rows),
                "targets": file_count,
                "reviewed": len(outcomes),
                "unresolved": sorted(unresolved),
                "errors": unresolved,
                "requested_jobs": config.requested_jobs,
                "max_combined_workers": workers,
                "max_reviewers": review_jobs,
                "max_attempts": max_attempts,
                "rounds": rounds,
                "duration_secs": round(time.monotonic() - started, 3),
                "preflight": preflight,
                "session_dir": str(session_dir),
                "formalizers": {
                    "requested": len(formalizer_invocations),
                    "materialized": len(materialized_invocations),
                    "failed": len(failed_invocations),
                },
                "formalizer_results": formalizer_results,
                "formalizer_history": formalizer_history,
                "formalization_handoffs": materialized_redrafts,
                "formalization_reviews": {
                    "enabled": full_pipeline,
                    "reviewed": len(formalization_gate_result["reviewed"]),
                    "rounds": formalization_rounds,
                    "unresolved": sorted(pending_formalization),
                },
                "gate_events_applied": gate_events_applied,
                "gate_events": gate_event_summaries,
                "proof_gate_result": proof_gate_result,
                "formalization_gate_result": formalization_gate_result,
                "proof_redrafts_reopened": proof_redrafts_reopened,
                "pending_formalization_targets": sorted(pending_formalization),
            },
        )
        write_meta(self.iter_meta, **{
            "prover.pipelineReviewComplete": complete,
            "prover.pipelineReviewTargets": file_count,
            "prover.pipelineReviewReviewed": len(outcomes),
            "prover.pipelineReviewUnresolved": len(unresolved),
            "prover.pipelineReviewReport": str(report_path),
            "prover.pipelineFormalizersRequested": len(formalizer_invocations),
            "prover.pipelineFormalizersMaterialized": len(
                materialized_invocations
            ),
            "prover.pipelineFormalizersFailed": len(failed_invocations),
            "prover.pipelineFormalizationReviews": len(
                formalization_gate_result["reviewed"]
            ),
            "prover.pipelineFormalizationPending": len(pending_formalization),
            "prover.pipelineGateEventsApplied": gate_events_applied,
            "prover.pipelineGateEvents": len(gate_event_summaries),
        })
        if complete:
            log.success(
                f"Pipelined proof Review finished for all {file_count} target(s)"
            )
        else:
            log.warn(
                "Pipelined proof Review hand-off is incomplete; ReviewPhase "
                "will fail closed and rerun the normal target Review batch."
            )

        if materialized_redrafts:
            log.success(
                f"Immediate redrafts materialized: {len(materialized_redrafts)}"
            )
        if failed_redrafts:
            log.warn(
                f"Immediate redrafts incomplete: {len(failed_redrafts)}; "
                "normal autoformalize fallback remains enabled"
            )

        if failed:
            log.warn(f"{failed}/{file_count} prover(s) had errors")
        else:
            log.success(f"All {file_count} prover(s) finished")
        results_dir = self.state_dir / "task_results"
        result_count = (
            len(list(results_dir.glob("*.md"))) if results_dir.exists() else 0
        )
        log.info(f"Task result files: {result_count}/{file_count}")
        self._emit_round_end(file_count, failed)

    def _emit_round_end(self, prover_count: int, failed: int) -> None:
        provers_dir = self.iter_dir / "provers"
        target = None
        if provers_dir.exists():
            # is_file() filters dangling symlinks — left over from cancelled
            # multilane runs or prior runs with a different lane set.
            logs = sorted(
                p for p in provers_dir.glob("*.jsonl")
                if not p.name.endswith(".raw.jsonl") and p.is_file()
            )
            if logs:
                target = logs[0]
        if target is None:
            target = self.iter_dir / "parallel.jsonl"

        row = {
            "ts": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "event": "parallel_round_end",
            "prover_count": prover_count,
            "failed": failed,
        }
        with target.open("a") as f:
            f.write(json.dumps(row) + "\n")
