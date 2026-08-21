"""Regressions for phase auto-detection during ``archon loop --resume``."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.resume import detect_last_interrupted_phase


class DetectLastInterruptedPhaseTest(unittest.TestCase):
    def _meta(self, value: object) -> Path:
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        path = root / "meta.json"
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def test_explicitly_skipped_plan_resumes_running_prover(self) -> None:
        path = self._meta({
            "plan": {"status": "skipped"},
            "prover": {"status": "running"},
        })

        self.assertEqual(detect_last_interrupted_phase(path), "prover")

    def test_explicitly_skipped_plan_and_done_prover_resume_review(self) -> None:
        path = self._meta({
            "plan": {"status": "skipped"},
            "prover": {"status": "done"},
        })

        self.assertEqual(detect_last_interrupted_phase(path), "review")

    def test_all_terminal_statuses_return_none(self) -> None:
        path = self._meta({
            "plan": {"status": "skipped"},
            "prover": {"status": "done"},
            "review": {"status": "done"},
        })

        self.assertIsNone(detect_last_interrupted_phase(path))

    def test_actual_running_plan_still_resumes_plan(self) -> None:
        path = self._meta({"plan": {"status": "running"}})

        self.assertEqual(detect_last_interrupted_phase(path), "plan")

    def test_missing_or_malformed_metadata_fails_safe_to_plan(self) -> None:
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))

        with self.subTest("missing"):
            self.assertEqual(
                detect_last_interrupted_phase(root / "missing.json"), "plan"
            )
        with self.subTest("non-object"):
            self.assertEqual(
                detect_last_interrupted_phase(self._meta([])), "plan"
            )
        with self.subTest("missing-phase-section"):
            self.assertEqual(
                detect_last_interrupted_phase(self._meta({"iteration": 1})),
                "plan",
            )


if __name__ == "__main__":
    unittest.main()
