from __future__ import annotations

import importlib.util
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/install_answer_blind_runtime_wrappers.py"
CAMPAIGN_SOURCE = ROOT / "scripts/run_answer_blind_gpt_campaign.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_runtime_installer", SCRIPT)
assert SPEC and SPEC.loader
INSTALLER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = INSTALLER
SPEC.loader.exec_module(INSTALLER)


@unittest.skipUnless(os.geteuid() == 0, "runtime installation is root-only")
class AnswerBlindRuntimeInstallerTests(unittest.TestCase):
    def test_campaign_controller_and_wrapper_are_runtime_inventory_files(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-runtime-install-") as raw:
            runtime = Path(raw) / "runtime"
            python = runtime / "venv/bin/python"
            python.parent.mkdir(parents=True)
            python.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            python.chmod(0o755)
            module_root = (
                runtime
                / "venv/lib/python3.14/site-packages/archon/.archon-src/tools"
                / "lean-lsp-mcp/src/lean_lsp_mcp"
            )
            module_root.mkdir(parents=True)
            (module_root / "__main__.py").write_text("", encoding="utf-8")
            for relative in (
                ".pytest_cache/state",
                "venv/.mypy_cache/state",
                "venv/.ruff_cache/state",
                "venv/lib/python3.14/site-packages/pkg/__pycache__/module.pyc",
            ):
                cache_file = runtime / relative
                cache_file.parent.mkdir(parents=True, exist_ok=True)
                cache_file.write_bytes(b"generated-cache")

            with mock.patch.object(INSTALLER, "_copy_controller_tools"):
                INSTALLER.install(runtime_root=runtime, materialize_python=False)

            module = runtime / "libexec/run_answer_blind_gpt_campaign.py"
            wrapper = runtime / "bin/answer-blind-gpt-campaign"
            self.assertEqual(module.read_bytes(), CAMPAIGN_SOURCE.read_bytes())
            self.assertEqual(stat.S_IMODE(module.stat().st_mode), 0o444)
            self.assertEqual(module.stat().st_uid, 0)
            self.assertEqual(stat.S_IMODE(wrapper.stat().st_mode), 0o755)
            self.assertEqual(wrapper.stat().st_uid, 0)
            payload = wrapper.read_text(encoding="utf-8")
            self.assertIn(f"exec '{python}' -I -B '{module}' \"$@\"", payload)
            self.assertIn("PYTHONNOUSERSITE=1", payload)
            self.assertIn("PYTHONDONTWRITEBYTECODE=1", payload)
            self.assertNotIn(str(ROOT), payload)

            # Both paths are ordinary files under runtime_root, so the
            # production recursive runtime inventory necessarily binds them.
            inventory_paths = {
                path.relative_to(runtime).as_posix()
                for path in runtime.rglob("*")
                if path.is_file() and not path.is_symlink()
            }
            self.assertIn("libexec/run_answer_blind_gpt_campaign.py", inventory_paths)
            self.assertIn("bin/answer-blind-gpt-campaign", inventory_paths)
            self.assertFalse(
                any(
                    path.name in INSTALLER.PYTHON_CACHE_DIRS
                    or path.suffix in {".pyc", ".pyo"}
                    for path in runtime.rglob("*")
                )
            )


if __name__ == "__main__":
    unittest.main()
