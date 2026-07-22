"""Physics grounding phase — deterministic LeanExplore evidence preflight."""

from __future__ import annotations

import time

from archon import log

from ..physics_grounding import run_physics_grounding
from .base import Phase, PhaseResult


class PhysicsGroundingPhase(Phase):
    """Write LeanExplore grounding logs for physics blueprint targets."""

    name = "Physics grounding"
    skip_token = "physics-grounding"

    def run(self) -> PhaseResult:
        ctx = self.ctx
        if self.skip_token in ctx.skip_now:
            log.phase(0, f"{self.name} — skipped (--from)")
            return PhaseResult(skipped=True)
        if ctx.dry_run:
            log.phase(0, f"{self.name} — skipped (--dry-run)")
            return PhaseResult(skipped=True)
        if ctx.current_stage not in {"autoformalize", "prover"}:
            return PhaseResult()

        start = time.monotonic()
        try:
            descriptor = ctx.harness_descriptor_for("prover")
            configured_backend = descriptor.raw.get("lean_explore_backend")
            backend = (
                configured_backend
                if configured_backend in {"api", "local"}
                else "auto"
            )
            reports = run_physics_grounding(ctx.project_path, backend=backend)
        except Exception as exc:  # defensive: grounding must not break the loop
            log.warn(f"physics grounding crashed: {exc}")
            return PhaseResult()

        if not reports:
            return PhaseResult()

        secs = int(time.monotonic() - start)
        complete = sum(1 for report in reports if report.is_complete)
        incomplete = len(reports) - complete
        if incomplete:
            log.warn(
                f"physics grounding: {complete} complete, {incomplete} incomplete "
                f"report(s) ({secs}s)"
            )
        else:
            log.success(f"physics grounding: {complete} report(s) complete ({secs}s)")
        return PhaseResult()
