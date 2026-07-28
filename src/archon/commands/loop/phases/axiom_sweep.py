"""AxiomSweepPhase — deterministic ``sorryAx``-laundering detector.

Runs after ``sync_leanok`` / ``blueprint-doctor`` and before Review when
``loop.axiom_sweep`` is true. Normal iterations check exact objectives in
parallel; polish checks all source files. Each mutating shell probe operates on
a disposable copy. Writes ``axiom-sweep.{md,json}``, logs a one-line summary,
and never blocks the loop.
"""

from __future__ import annotations

from archon import log
from archon.commands.tooling.project_config import load_project_config
from archon.state import parse_objective_files, write_meta
from archon.state.progress import is_complete

from ..axiom_sweep import run_axiom_sweep, write_reports
from .base import Phase, PhaseResult


class AxiomSweepPhase(Phase):
    """Optional ``#print axioms`` sweep for sorryAx laundering."""

    name = "Axiom sweep"
    skip_token = "axiom-sweep"

    def run(self) -> PhaseResult:
        ctx = self.ctx
        if self.skip_token in ctx.skip_now:
            log.phase(0, f"{self.name} — skipped (--from)")
            return PhaseResult(skipped=True)
        if ctx.dry_run:
            log.phase(0, f"{self.name} — skipped (--dry-run)")
            return PhaseResult(skipped=True)

        cfg = load_project_config(ctx.project_path)
        loop_cfg = cfg.loop_section()
        if not bool(loop_cfg.get("axiom_sweep")):
            # Off by default — silent skip.
            return PhaseResult()

        requested_jobs = max(
            1,
            int(loop_cfg.get(
                "axiom_sweep_jobs",
                min(int(getattr(ctx.options, "max_parallel", 1)), 8),
            )),
        )
        timeout_s = max(1, int(loop_cfg.get("axiom_sweep_timeout_sec", 1800)))
        scope = str(loop_cfg.get("axiom_sweep_scope", "current_objectives"))
        full = (
            scope == "full"
            or ctx.current_stage == "polish"
            or is_complete(ctx.progress_file)
        )
        targets = None if full else parse_objective_files(
            ctx.progress_file, ctx.project_path,
        )

        log.phase(0, self.name)
        try:
            report = run_axiom_sweep(
                ctx.project_path,
                targets=targets,
                jobs=requested_jobs,
                timeout_s=timeout_s,
                scratch_root=(
                    ctx.state_dir / "tmp" / "axiom-sweep"
                    / f"iter-{ctx.iter_num:03d}"
                ),
            )
        except Exception as e:  # defensive: the sweep must never break the loop
            log.warn(f"axiom sweep crashed: {e}")
            return PhaseResult()

        if report is None:
            # No Lean project / script missing — silent skip.
            return PhaseResult()

        write_meta(ctx.iter_meta, **{
            "axiomSweep.status": "done" if report.ran else "partial",
            "axiomSweep.scope": report.scope,
            "axiomSweep.jobs": report.jobs,
            "axiomSweep.targets": len(report.target_files),
            "axiomSweep.filesChecked": report.files_checked,
            "axiomSweep.failedFiles": len(report.failed_files),
            "axiomSweep.durationSecs": report.duration_s,
            "axiomSweep.sorryLaunderings": len(report.sorry_launderings),
        })

        if ctx.iter_dir is not None:
            _, md_path = write_reports(report, ctx.iter_dir, ctx.project_path)
        else:
            md_path = None

        if report.failed_files:
            log.warn(
                f"axiom sweep: {len(report.failed_files)} target(s) failed: {report.error}"
            )
        if report.has_launderings:
            n = len(report.sorry_launderings)
            where = f" — see {md_path}" if md_path else ""
            log.warn(
                f"axiom sweep: {n} sorryAx-laundering decl(s) that emit NO "
                f"sorry warning ({report.duration_s}s){where}"
            )
        elif report.failed_files:
            log.warn(
                "axiom sweep: no laundering found in completed checks, but "
                f"{len(report.failed_files)} target(s) did not complete "
                f"({report.duration_s}s)"
            )
        else:
            log.success(
                "axiom sweep: no sorryAx laundering "
                f"({report.files_checked} files, {report.jobs} jobs, "
                f"{report.duration_s}s)"
            )
        return PhaseResult()
