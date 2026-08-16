"""Focused regressions for the mechanical Lake CLI wrapper."""

from __future__ import annotations

import unittest

from archon.commands.tooling.lake import LakeError


class LakeErrorTest(unittest.TestCase):
    def test_string_preserves_command_returncode_and_captured_diagnostics(self):
        error = LakeError(
            ["build"], "compiler stdout\n", "compiler stderr\n", 7,
        )

        self.assertEqual(error.command, ["build"])
        self.assertEqual(error.returncode, 7)
        self.assertIn("lake build exited with code 7", str(error))
        self.assertIn("stdout: compiler stdout", str(error))
        self.assertIn("stderr: compiler stderr", str(error))


if __name__ == "__main__":
    unittest.main()
