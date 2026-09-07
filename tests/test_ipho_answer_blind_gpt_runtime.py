from __future__ import annotations

import importlib.util
import json
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/build_ipho_answer_blind_gpt_runtime.py"
SPEC = importlib.util.spec_from_file_location("ipho_gpt_runtime_builder", SCRIPT)
assert SPEC and SPEC.loader
BUILDER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BUILDER
SPEC.loader.exec_module(BUILDER)


class IPhOAnswerBlindGptRuntimeTests(unittest.TestCase):
    def _file(self, path: Path, content: bytes, mode: int = 0o644) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        path.chmod(mode)
        return path

    def _fixture(self, root: Path) -> tuple[Path, Path, Path, Path]:
        base = root / "base-runtime"
        output = root / "gpt-runtime"
        repo = root / "repo"
        installed = base / "venv/lib/python3.14/site-packages/archon"

        self._file(
            base / BUILDER.SOURCE_MARKER,
            (BUILDER.EXPECTED_BASE_COMMIT + "\n").encode(),
            0o444,
        )
        self._file(base / "python/bin/python3.14", b"fixture-python\n", 0o555)
        self._file(
            base / "bin/archon",
            f"#!{base}/bin/sh\nexec {base}/venv/bin/archon\n".encode(),
            0o555,
        )
        self._file(base / "bin/sh", b"#!/bin/sh\n", 0o555)
        self._file(
            base / "venv/bin/archon",
            f"#!{base}/venv/bin/python\n".encode(),
            0o555,
        )
        self._file(
            base / "venv/pyvenv.cfg",
            f"home = {base}/python/bin\n".encode(),
        )
        (base / "venv/bin/python").symlink_to(base / "python/bin/python3.14")

        codex = b"""class CodexAgent:
    def run(
        self,
        *,
        idle_timeout_s: float | None = 900,
    ) -> bool:
        return True
"""
        self._file(installed / BUILDER.CODEX_AGENT, codex)
        self._file(installed / BUILDER.CLAUDE_AGENT, b"CLAUDE_AGENT = 'base-only'\n")

        for index, (source_rel, destination_rel) in enumerate(BUILDER.OVERLAYS):
            self._file(repo / source_rel, f"overlay-{index}\n".encode())
            self._file(installed / destination_rel, f"old-{index}\n".encode())
        return base, output, repo, installed

    def _make_writable(self, root: Path) -> None:
        if not root.exists():
            return
        paths = list(root.rglob("*"))
        for path in paths:
            if not path.is_symlink():
                try:
                    path.chmod(stat.S_IMODE(path.stat().st_mode) | 0o700)
                except OSError:
                    pass
        root.chmod(0o700)

    def _build(self, base: Path, output: Path, repo: Path) -> dict:
        return BUILDER.build_runtime(
            base=base,
            output=output,
            repo=repo,
            owner_uid=os.geteuid(),
            owner_gid=os.getegid(),
        )

    def test_build_and_validate_relocates_and_installs_exact_delta(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ipho-gpt-runtime-") as raw:
            root = Path(raw)
            try:
                base, output, repo, base_installed = self._fixture(root)
                marker = self._build(base, output, repo)
                installed = BUILDER._installed_archon(output)

                self.assertTrue(output.is_dir())
                self.assertEqual(marker["schema_version"], 1)
                self.assertEqual(marker["protocol"], BUILDER.PROTOCOL)
                self.assertEqual(
                    marker["base_runtime"]["source_commit"],
                    BUILDER.EXPECTED_BASE_COMMIT,
                )
                self.assertEqual(marker["runtime"]["root"], str(output))
                self.assertEqual(marker["codex_agent"]["idle_timeout_s"], 1800)
                self.assertEqual(marker["prefix_relocation"]["regular_files_changed"], 3)
                self.assertEqual(marker["prefix_relocation"]["symlinks_changed"], 1)

                self.assertNotIn(str(base), (output / "bin/archon").read_text())
                self.assertIn(str(output), (output / "bin/archon").read_text())
                self.assertNotIn(str(base), (output / "venv/pyvenv.cfg").read_text())
                self.assertEqual(
                    os.readlink(output / "venv/bin/python"),
                    str(output / "python/bin/python3.14"),
                )
                for source_rel, destination_rel in BUILDER.OVERLAYS:
                    self.assertEqual(
                        (installed / destination_rel).read_bytes(),
                        (repo / source_rel).read_bytes(),
                    )
                codex = (installed / BUILDER.CODEX_AGENT).read_bytes()
                self.assertIn(BUILDER.NEW_IDLE, codex)
                self.assertNotIn(BUILDER.OLD_IDLE, codex)
                self.assertEqual(
                    (installed / BUILDER.CLAUDE_AGENT).read_bytes(),
                    (base_installed / BUILDER.CLAUDE_AGENT).read_bytes(),
                )
                self.assertEqual(
                    json.loads((output / BUILDER.BUILD_MARKER).read_text()), marker
                )
                self.assertEqual(
                    BUILDER.validate_runtime(
                        base=base,
                        runtime=output,
                        repo=repo,
                        owner_uid=os.geteuid(),
                        owner_gid=os.getegid(),
                    ),
                    marker,
                )
                self.assertEqual(list(root.glob(f".{output.name}.staging-*")), [])
                for path in (output, *output.rglob("*")):
                    metadata = path.lstat()
                    self.assertEqual(metadata.st_uid, os.geteuid())
                    self.assertEqual(metadata.st_gid, os.getegid())
                    if not stat.S_ISLNK(metadata.st_mode):
                        self.assertFalse(stat.S_IMODE(metadata.st_mode) & 0o022)
            finally:
                self._make_writable(root)

    def test_build_refuses_existing_output(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ipho-gpt-runtime-existing-") as raw:
            root = Path(raw)
            base, output, repo, _installed = self._fixture(root)
            output.mkdir()
            sentinel = self._file(output / "sentinel", b"keep\n")
            with self.assertRaisesRegex(BUILDER.RuntimeBuildError, "must not exist"):
                self._build(base, output, repo)
            self.assertEqual(sentinel.read_bytes(), b"keep\n")

    def test_build_rejects_wrong_base_source_marker(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ipho-gpt-runtime-marker-") as raw:
            root = Path(raw)
            base, output, repo, _installed = self._fixture(root)
            (base / BUILDER.SOURCE_MARKER).chmod(0o644)
            (base / BUILDER.SOURCE_MARKER).write_text("0" * 40 + "\n")
            with self.assertRaisesRegex(BUILDER.RuntimeBuildError, "base source marker"):
                self._build(base, output, repo)
            self.assertFalse(output.exists())

    def test_validate_rejects_tampered_build_marker(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ipho-gpt-runtime-tamper-") as raw:
            root = Path(raw)
            try:
                base, output, repo, _installed = self._fixture(root)
                self._build(base, output, repo)
                path = output / BUILDER.BUILD_MARKER
                path.chmod(0o644)
                value = json.loads(path.read_text())
                value["codex_agent"]["idle_timeout_s"] = 900
                path.write_text(json.dumps(value) + "\n")
                with self.assertRaisesRegex(
                    BUILDER.RuntimeBuildError, "build marker does not match"
                ):
                    BUILDER.validate_runtime(
                        base=base,
                        runtime=output,
                        repo=repo,
                        owner_uid=os.geteuid(),
                        owner_gid=os.getegid(),
                    )
            finally:
                self._make_writable(root)

    def test_validate_rejects_stale_overlay(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ipho-gpt-runtime-stale-") as raw:
            root = Path(raw)
            try:
                base, output, repo, _installed = self._fixture(root)
                self._build(base, output, repo)
                source_rel, _destination_rel = BUILDER.OVERLAYS[0]
                (repo / source_rel).write_text("newer-overlay\n")
                with self.assertRaisesRegex(
                    BUILDER.RuntimeBuildError, "runtime overlay hash mismatch"
                ):
                    BUILDER.validate_runtime(
                        base=base,
                        runtime=output,
                        repo=repo,
                        owner_uid=os.geteuid(),
                        owner_gid=os.getegid(),
                    )
            finally:
                self._make_writable(root)


if __name__ == "__main__":
    unittest.main()
