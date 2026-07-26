from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


_SYNC = Path(__file__).resolve().parent.parent / (
    "src/archon/.archon-src/skills/lean4/lib/scripts/sync_leanok.py"
)


def _load_sync_module():
    name = "sync_leanok_incremental_module"
    spec = importlib.util.spec_from_file_location(name, _SYNC)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)  # type: ignore[union-attr]
    return module


class IncrementalSyncTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mod = _load_sync_module()

    def test_decl_scan_and_chapter_sync_stay_in_selected_file(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            a = root / "A.lean"
            b = root / "B.lean"
            a.write_text(
                "namespace N\ntheorem a : True := by trivial\nend N\n",
                encoding="utf-8",
            )
            b.write_text(
                "namespace N\ntheorem b : True := by trivial\nend N\n",
                encoding="utf-8",
            )
            chapter = root / "Both.tex"
            chapter.write_text(
                "\\begin{theorem}\\lean{N.a}\\end{theorem}\n"
                "\\begin{proof}\\end{proof}\n"
                "\\begin{theorem}\\lean{N.b}\\leanok\\end{theorem}\n"
                "\\begin{proof}\\leanok\\end{proof}\n",
                encoding="utf-8",
            )
            allowed = {a.resolve()}
            index = self.mod._scan_lean_decls(root, allowed)
            self.assertIn("N.a", index)
            self.assertNotIn("N.b", index)

            changes = self.mod._sync_chapter(
                chapter,
                root,
                index,
                dry_run=True,
                verbose=False,
                compile_cache={a: True},
                allowed_files=allowed,
            )
            self.assertTrue(changes)
            self.assertTrue(all(change.lean_name == "N.a" for change in changes))
            # Out-of-scope N.b markers remain untouched.
            self.assertEqual(chapter.read_text().count("\\leanok"), 2)


if __name__ == "__main__":
    unittest.main()
