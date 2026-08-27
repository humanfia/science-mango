"""Regression tests for the Kimi branch's Claude idle-watchdog default."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from archon.agent import ClaudeAgent, RunOutcome


class ClaudeIdleTimeoutTest(unittest.TestCase):
    def _run_and_capture_timeout(self, **kwargs: object) -> float | None:
        agent = ClaudeAgent(model="opus", role="prover")
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            with mock.patch.object(
                agent, "_run_with_logging", return_value=RunOutcome.SUCCESS,
            ) as run_once:
                self.assertTrue(
                    agent.run(
                        "test prompt",
                        cwd=root,
                        log_base=root / "agent",
                        **kwargs,
                    )
                )
        return run_once.call_args.kwargs["idle_timeout_s"]

    def test_omitted_timeout_passes_kimi_branch_default(self) -> None:
        self.assertEqual(self._run_and_capture_timeout(), 1800)

    def test_explicit_timeout_override_is_preserved(self) -> None:
        self.assertEqual(
            self._run_and_capture_timeout(idle_timeout_s=37),
            37,
        )


if __name__ == "__main__":
    unittest.main()
