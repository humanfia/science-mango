"""Tests for ``sync_leanok-state.json`` (per-iter sync attribution marker).

After each successful ``sync_leanok`` run, the phase wrapper stamps a small
state file under the project state dir. Review-phase checkers consult this
to distinguish "this chapter's \\leanok is stale, sync will strip it
shortly" from "genuine headline laundering" — the failure mode the user
flagged when the keyword-prefix bug let sorry-bodied decls keep their
proof-block markers.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.phases.sync_leanok import SyncLeanokPhase, _write_state


class WriteStateTest(unittest.TestCase):

    def _project(self) -> Path:
        tmp = tempfile.mkdtemp()
        self.addCleanup(_rmtree, tmp)
        return Path(tmp)

    def test_writes_well_formed_json(self):
        proj = self._project()
        state_dir = proj / ".archon"
        _write_state(
            state_dir,
            iter_num=163,
            project_path=proj,
            added=3,
            removed=5,
            chapters_touched=["blueprint/src/chapters/A.tex",
                              "blueprint/src/chapters/B.tex",
                              "blueprint/src/chapters/A.tex"],  # dup
            secs=12,
        )
        path = state_dir / "sync_leanok-state.json"
        self.assertTrue(path.exists())
        data = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(data["iter"], 163)
        self.assertEqual(data["added"], 3)
        self.assertEqual(data["removed"], 5)
        self.assertEqual(data["duration_secs"], 12)
        # chapters_touched dedup + sorted.
        self.assertEqual(
            data["chapters_touched"],
            ["blueprint/src/chapters/A.tex", "blueprint/src/chapters/B.tex"],
        )
        self.assertIn("timestamp", data)
        # ``sha`` is None when there's no inner-git initialized — make sure
        # the writer still produces a parseable file in that case.
        self.assertIn("sha", data)
        self.assertEqual(data["scope"], "full")
        self.assertEqual(data["targets_checked"], [])

    def test_creates_state_dir_if_absent(self):
        proj = self._project()
        state_dir = proj / "nested" / "state"  # does not exist yet
        _write_state(
            state_dir,
            iter_num=1,
            project_path=proj,
            added=0,
            removed=0,
            chapters_touched=[],
            secs=0,
        )
        self.assertTrue((state_dir / "sync_leanok-state.json").exists())

    def test_silent_on_unwritable_dir(self):
        # Pointing at a path inside a regular file should not raise.
        proj = self._project()
        not_a_dir = proj / "blocker"
        not_a_dir.write_text("x")
        state_dir = not_a_dir / "state"  # cannot mkdir under a file
        # Should swallow the OSError quietly.
        _write_state(
            state_dir,
            iter_num=1,
            project_path=proj,
            added=0,
            removed=0,
            chapters_touched=[],
            secs=0,
        )


class IncrementalPhaseTest(unittest.TestCase):
    def test_phase_passes_only_current_objectives_to_script(self):
        with tempfile.TemporaryDirectory() as td:
            proj = Path(td)
            state = proj / ".archon"
            state.mkdir()
            chapters = proj / "blueprint" / "src" / "chapters"
            chapters.mkdir(parents=True)
            (proj / "A.lean").write_text("theorem a : True := by trivial\n")
            (proj / "B.lean").write_text("theorem b : True := by trivial\n")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "1. **`A.lean`** — current target.\n"
            )
            script = proj / "sync.py"
            script.write_text("# placeholder\n")
            ctx = SimpleNamespace(
                skip_now=set(), dry_run=False, project_path=proj,
                progress_file=progress, state_dir=state, iter_num=7,
            )
            completed = SimpleNamespace(returncode=0, stdout="[]", stderr="")
            with (
                patch(
                    "archon.commands.loop.phases.sync_leanok._script_path",
                    return_value=script,
                ),
                patch(
                    "archon.commands.loop.phases.sync_leanok.subprocess.run",
                    return_value=completed,
                ) as run,
            ):
                SyncLeanokPhase(ctx).run()

            command = run.call_args.args[0]
            self.assertIn("--lean-file", command)
            self.assertIn("A.lean", command)
            self.assertNotIn("B.lean", command)
            data = json.loads((state / "sync_leanok-state.json").read_text())
            self.assertEqual(data["scope"], "current-objectives")
            self.assertEqual(data["targets_checked"], ["A.lean"])


def _rmtree(path: str) -> None:
    import shutil
    shutil.rmtree(path, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
