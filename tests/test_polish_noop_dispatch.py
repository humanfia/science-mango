"""Regression tests for zero-sorry objectives routed to polish."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from archon.commands.loop.prover.runners import ParallelProverRunner


def _write_polish_mode(state_dir: Path) -> None:
    modes = state_dir / "prover-modes"
    modes.mkdir(parents=True)
    (modes / "polish.md").write_text(
        "---\n"
        "name: polish\n"
        "compatible_stages:\n"
        "  - polish\n"
        "default_for_stages:\n"
        "  - polish\n"
        "---\n\n"
        "Polish completed proofs.\n",
        encoding="utf-8",
    )


def _runner(project: Path, *, stage: str) -> ParallelProverRunner:
    state = project / ".archon"
    return ParallelProverRunner(
        project_name="test-project",
        project_path=project,
        state_dir=state,
        stage=stage,
        iter_dir=state / "logs" / "iter-001",
        iter_meta=state / "logs" / "iter-001" / "meta.json",
        iter_num=1,
        max_parallel=2,
        max_objectives=2,
        block_on_blocked_deps=False,
        verbose_logs=False,
        model="test-model",
    )


class PolishNoopDispatchTest(unittest.TestCase):
    def test_explicit_polish_dispatches_but_ordinary_clean_prover_is_filtered(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d).resolve()
            state = project / ".archon"
            state.mkdir()
            (project / "Polish.lean").write_text(
                "theorem polished : True := trivial\n", encoding="utf-8"
            )
            (project / "Done.lean").write_text(
                "theorem done : True := trivial\n", encoding="utf-8"
            )
            (state / "PROGRESS.md").write_text(
                "## Current Objectives\n\n"
                "1. **`Polish.lean`** [prover-mode: polish] — refactor it.\n"
                "2. **`Done.lean`** — fill proof holes.\n",
                encoding="utf-8",
            )

            with patch(
                "archon.commands.loop.prover.runners.log.step"
            ) as log_step:
                _runner(project, stage="prover").run(dry_run=True)

            messages = [str(call.args[0]) for call in log_step.call_args_list]
            self.assertEqual(len(messages), 1)
            self.assertIn("Polish.lean", messages[0])
            self.assertIn("(mode: polish)", messages[0])
            self.assertNotIn("Done.lean", messages[0])

    def test_polish_stage_dispatches_untagged_clean_target_to_default_mode(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d).resolve()
            state = project / ".archon"
            state.mkdir()
            _write_polish_mode(state)
            (project / "Clean.lean").write_text(
                "theorem clean : True := trivial\n", encoding="utf-8"
            )
            (state / "PROGRESS.md").write_text(
                "## Current Objectives\n\n"
                "1. **`Clean.lean`** — polish the completed proof.\n",
                encoding="utf-8",
            )

            with patch(
                "archon.commands.loop.prover.runners.log.step"
            ) as log_step:
                _runner(project, stage="polish").run(dry_run=True)

            messages = [str(call.args[0]) for call in log_step.call_args_list]
            self.assertEqual(len(messages), 1)
            self.assertIn("Clean.lean", messages[0])
            self.assertIn("(mode: polish)", messages[0])


if __name__ == "__main__":
    unittest.main()
