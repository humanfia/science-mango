"""Regression tests for updating the stage in supported PROGRESS.md layouts."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from archon.state.progress import read_stage, write_stage


class WriteStageTests(unittest.TestCase):
    def _progress(self, content: str) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / "PROGRESS.md"
        path.write_text(content, encoding="utf-8")
        return path

    def test_updates_template_layout_with_stages_section(self):
        progress = self._progress(
            "# Project Progress\n\n"
            "## Current Stage\n"
            "init\n\n"
            "## Stages\n"
            "- [ ] init\n"
            "- [ ] prover\n\n"
            "## Current Objectives\n"
        )

        write_stage(progress, "prover")

        self.assertEqual(read_stage(progress), "prover")
        content = progress.read_text(encoding="utf-8")
        self.assertIn("## Stages\n- [ ] init\n- [ ] prover", content)

    def test_updates_problem_set_layout_without_stages_section(self):
        progress = self._progress(
            "# IChO 2026 Progress\n\n"
            "## Current Stage\n\n"
            "autoformalize\n\n"
            "## Current Objectives\n\n"
            "### 1. **`IChO2026Problems/problem_icho_2026_t4_a6.lean`** "
            "[prover-mode: chemistry-formalize]\n"
            "- Keep this objective unchanged.\n"
        )
        objectives = progress.read_text(encoding="utf-8").split(
            "## Current Objectives", 1
        )[1]

        write_stage(progress, "prover")

        self.assertEqual(read_stage(progress), "prover")
        content = progress.read_text(encoding="utf-8")
        self.assertEqual(
            content.split("## Current Objectives", 1)[1], objectives
        )
        self.assertIn("[prover-mode: chemistry-formalize]", content)

    def test_updates_current_stage_when_it_is_the_last_section(self):
        progress = self._progress(
            "# Project Progress\n\n## Current Stage\n\nautoformalize\n"
        )

        write_stage(progress, "polish")

        self.assertEqual(read_stage(progress), "polish")

    def test_missing_current_stage_still_raises_without_modifying_file(self):
        progress = self._progress(
            "# Project Progress\n\n## Current Objectives\n\n- `Foo.lean`\n"
        )
        original = progress.read_text(encoding="utf-8")

        with self.assertRaisesRegex(ValueError, "Current Stage"):
            write_stage(progress, "prover")

        self.assertEqual(progress.read_text(encoding="utf-8"), original)


if __name__ == "__main__":
    unittest.main()
