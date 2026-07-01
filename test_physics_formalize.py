"""Tests for the physics multimodal formalization command.

These tests avoid model calls. They cover Archon's integration boundary:
input/path handling, dry-run manifests, and the configuration patch that lets
the external Auto-formalization project compile inside the target Archon
project.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile
import threading
import time
import types
import unittest
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from unittest import mock

import typer

from archon.commands.physics_formalize import (
    DEFAULT_ANTHROPIC_BASE_URL,
    DEFAULT_ANTHROPIC_MAX_TOKENS,
    PHYSLEAN_GIT_URL,
    BUILTIN_FORMALIZER_ROOT,
    PhysicsFormalizeCommand,
    _AnthropicOpenAICompatClient,
)

Exit = typer.Exit


class PhysicsFormalizeDryRunTests(unittest.TestCase):
    def test_dry_run_uses_builtin_formalizer_by_default(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="A block has mass 5 kg and acceleration 2 m/s^2. Find force.",
                work_dir=work_dir,
                index="builtin",
                dry_run=True,
            )
            cmd.run()

            manifest = json.loads(
                (work_dir / "problem_builtin_manifest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                manifest["formalizer_root"],
                str(BUILTIN_FORMALIZER_ROOT.resolve()),
            )

    def test_dry_run_writes_manifest_without_calling_formalizer(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"
            image = root / "diagram.png"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )
            image.write_bytes(b"fake image")

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="A block has mass 5 kg and acceleration 2 m/s^2. Find force.",
                image=image,
                answer="10",
                out=Path("PhysicsProblems/p001.lean"),
                report_out=Path("reports/p001.json"),
                work_dir=work_dir,
                index="p001",
                formalizer_root=formalizer,
                dry_run=True,
            )
            cmd.run()

            manifest_path = work_dir / "problem_p001_manifest.json"
            self.assertTrue(manifest_path.exists())
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            latest_path = project / ".archon" / "physics-formalize" / "latest.json"
            latest = json.loads(latest_path.read_text(encoding="utf-8"))
            self.assertEqual(manifest["command"], "physics-formalize")
            self.assertEqual(manifest["domain"], "physics")
            self.assertEqual(manifest["lean_search_packages"], ["Mathlib", "PhysLean"])
            self.assertTrue(latest["dry_run"])
            self.assertEqual(latest["output_lean"], manifest["output_lean"])
            self.assertTrue(manifest["use_multimodal"])
            self.assertEqual(manifest["entry"]["image"], "diagram.png")
            self.assertEqual(manifest["entry"]["answer"], "10")
            self.assertEqual(
                manifest["output_lean"],
                str((project / "PhysicsProblems" / "p001.lean").resolve()),
            )
            self.assertFalse((project / "PhysicsProblems" / "p001.lean").exists())

    def test_dry_run_preflight_checks_target_physlean_project(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(returncode=0, stdout="", stderr=""),
            ) as run:
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p004",
                    formalizer_root=formalizer,
                    dry_run=True,
                    preflight=True,
                )
                cmd.run()

            manifest = json.loads(
                (work_dir / "problem_p004_manifest.json").read_text(encoding="utf-8")
            )
            self.assertTrue(manifest["preflight"]["requested"])
            self.assertTrue(manifest["preflight"]["passed"])
            self.assertEqual(manifest["preflight"]["packages"], ["Mathlib", "PhysLean"])
            preflight_path = Path(manifest["preflight"]["file"])
            self.assertIn(
                "import Physlib.ClassicalMechanics.Basic",
                preflight_path.read_text(encoding="utf-8"),
            )
            command = run.call_args.args[0]
            self.assertEqual(command[:3], ["/fake/lake", "env", "lean"])
            self.assertEqual(run.call_args.kwargs["cwd"], project.resolve())

    def test_dry_run_builds_physlean_when_requested(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(returncode=0, stdout="", stderr=""),
            ) as run:
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p006",
                    formalizer_root=formalizer,
                    dry_run=True,
                    build_physlean=True,
                )
                cmd.run()

            manifest = json.loads(
                (work_dir / "problem_p006_manifest.json").read_text(encoding="utf-8")
            )
            self.assertTrue(manifest["physlean_build"]["requested"])
            self.assertTrue(manifest["physlean_build"]["passed"])
            self.assertEqual(manifest["physlean_build"]["target"], "PhysLean")
            command = run.call_args.args[0]
            self.assertEqual(command, ["/fake/lake", "build", "PhysLean"])
            self.assertEqual(run.call_args.kwargs["cwd"], project.resolve())

    def test_dry_run_ensures_physlean_dependency_in_lean_lakefile(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            lakefile = project / "lakefile.lean"
            lakefile.write_text(
                "import Lake\nopen Lake DSL\n\npackage Test where\n",
                encoding="utf-8",
            )
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(returncode=0, stdout="", stderr=""),
            ) as run:
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p008",
                    formalizer_root=formalizer,
                    dry_run=True,
                    ensure_physlean=True,
                )
                cmd.run()

            text = lakefile.read_text(encoding="utf-8")
            self.assertIn("require PhysLean", text)
            self.assertIn(PHYSLEAN_GIT_URL, text)
            manifest = json.loads(
                (work_dir / "problem_p008_manifest.json").read_text(encoding="utf-8")
            )
            self.assertTrue(manifest["physlean_dependency"]["requested"])
            self.assertTrue(manifest["physlean_dependency"]["modified"])
            self.assertTrue(manifest["physlean_dependency"]["update_passed"])
            self.assertEqual(run.call_args.args[0], ["/fake/lake", "update", "PhysLean"])

    def test_dry_run_ensures_physlean_dependency_in_toml_lakefile(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            lakefile = project / "lakefile.toml"
            lakefile.write_text('name = "Test"\n', encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(returncode=0, stdout="", stderr=""),
            ):
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p009",
                    formalizer_root=formalizer,
                    dry_run=True,
                    ensure_physlean=True,
                )
                cmd.run()

            text = lakefile.read_text(encoding="utf-8")
            self.assertIn('name = "PhysLean"', text)
            self.assertIn(PHYSLEAN_GIT_URL, text)

    def test_ensure_physlean_does_not_modify_existing_dependency(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            lakefile = project / "lakefile.lean"
            lakefile.write_text(
                "import Lake\nopen Lake DSL\n\npackage Test where\n"
                f'require PhysLean from git "{PHYSLEAN_GIT_URL}" @ "master"\n',
                encoding="utf-8",
            )
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
            ) as run:
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p010",
                    formalizer_root=formalizer,
                    dry_run=True,
                    ensure_physlean=True,
                )
                cmd.run()

            run.assert_not_called()
            manifest = json.loads(
                (work_dir / "problem_p010_manifest.json").read_text(encoding="utf-8")
            )
            self.assertTrue(manifest["physlean_dependency"]["requested"])
            self.assertFalse(manifest["physlean_dependency"]["modified"])
            self.assertIsNone(manifest["physlean_dependency"]["update_passed"])

    def test_preflight_failure_exits_before_formalizer_import(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('preflight should stop before import')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(
                    returncode=1,
                    stdout="",
                    stderr="unknown package PhysLean",
                ),
            ):
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p005",
                    formalizer_root=formalizer,
                    dry_run=True,
                    preflight=True,
                )
                with self.assertRaises(Exit) as caught:
                    cmd.run()

            self.assertEqual(caught.exception.exit_code, 1)
            self.assertFalse((work_dir / "problem_p005_manifest.json").exists())

    def test_build_physlean_failure_exits_before_formalizer_import(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('build should stop before import')\n",
                encoding="utf-8",
            )

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=types.SimpleNamespace(
                    returncode=1,
                    stdout="",
                    stderr="build failed",
                ),
            ):
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=work_dir,
                    index="p007",
                    formalizer_root=formalizer,
                    dry_run=True,
                    build_physlean=True,
                )
                with self.assertRaises(Exit) as caught:
                    cmd.run()

            self.assertEqual(caught.exception.exit_code, 1)
            self.assertFalse((work_dir / "problem_p007_manifest.json").exists())

    def test_dry_run_records_model_config_without_leaking_keys(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            old_llm = os.environ.get("ARCHON_TEST_LLM_KEY")
            old_search = os.environ.get("ARCHON_TEST_LEANEXPLORE_KEY")
            os.environ["ARCHON_TEST_LLM_KEY"] = "secret-llm-key"
            os.environ["ARCHON_TEST_LEANEXPLORE_KEY"] = "secret-search-key"
            self.addCleanup(self._restore_env, "ARCHON_TEST_LLM_KEY", old_llm)
            self.addCleanup(self._restore_env, "ARCHON_TEST_LEANEXPLORE_KEY", old_search)

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find force.",
                work_dir=work_dir,
                index="p002",
                formalizer_root=formalizer,
                dry_run=True,
                llm_api_key_env="ARCHON_TEST_LLM_KEY",
                llm_base_url="https://openrouter.ai/api/v1",
                llm_model="gpt-5",
                leanexplore_api_key_env="ARCHON_TEST_LEANEXPLORE_KEY",
            )
            cmd.run()

            manifest_text = (work_dir / "problem_p002_manifest.json").read_text(
                encoding="utf-8"
            )
            latest_text = (
                project / ".archon" / "physics-formalize" / "latest.json"
            ).read_text(encoding="utf-8")
            self.assertNotIn("secret-llm-key", manifest_text)
            self.assertNotIn("secret-search-key", manifest_text)
            self.assertNotIn("secret-llm-key", latest_text)
            self.assertNotIn("secret-search-key", latest_text)

            manifest = json.loads(manifest_text)
            self.assertEqual(manifest["llm"]["provider"], "openai-compatible")
            self.assertEqual(manifest["llm"]["model"], "gpt-5")
            self.assertEqual(
                manifest["llm"]["base_url"], "https://openrouter.ai/api/v1"
            )
            self.assertEqual(
                manifest["llm"]["api_key_source"], "env:ARCHON_TEST_LLM_KEY"
            )
            self.assertFalse(manifest["llm"]["supports_temperature"])
            self.assertEqual(
                manifest["leanexplore"]["api_key_source"],
                "env:ARCHON_TEST_LEANEXPLORE_KEY",
            )

    def test_dry_run_records_native_anthropic_config_without_leaking_keys(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )

            old_key = os.environ.get("ANTHROPIC_API_KEY")
            os.environ["ANTHROPIC_API_KEY"] = "secret-anthropic-key"
            self.addCleanup(self._restore_env, "ANTHROPIC_API_KEY", old_key)

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find force.",
                work_dir=work_dir,
                index="p003",
                formalizer_root=formalizer,
                dry_run=True,
                llm_provider="anthropic",
                llm_model="claude-sonnet-4-5",
            )
            cmd.run()

            manifest_text = (work_dir / "problem_p003_manifest.json").read_text(
                encoding="utf-8"
            )
            self.assertNotIn("secret-anthropic-key", manifest_text)

            manifest = json.loads(manifest_text)
            self.assertEqual(manifest["llm"]["provider"], "anthropic")
            self.assertEqual(manifest["llm"]["model"], "claude-sonnet-4-5")
            self.assertEqual(manifest["llm"]["base_url"], DEFAULT_ANTHROPIC_BASE_URL)
            self.assertEqual(
                manifest["llm"]["api_key_source"], "env:ANTHROPIC_API_KEY"
            )
            self.assertEqual(
                manifest["llm"]["max_tokens"], DEFAULT_ANTHROPIC_MAX_TOKENS
            )
            self.assertTrue(manifest["llm"]["supports_temperature"])

    @staticmethod
    def _restore_env(name: str, value: str | None):
        if value is None:
            os.environ.pop(name, None)
        else:
            os.environ[name] = value

    def test_successful_run_writes_outputs_metadata_and_progress(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "run"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "config.py").write_text("", encoding="utf-8")
            (formalizer / "Formalizer" / "main.py").write_text(
                "def process_single_problem(entry, output_dir, image_root_dir=None):\n"
                "    return {\n"
                "        'status': 'success',\n"
                "        'compilation_passed': True,\n"
                "        'semantic_passed': True,\n"
                "        'consistency_level': 'level_1',\n"
                "        'generated_code': 'import Mathlib\\n\\ntheorem result : True := by sorry\\n',\n"
                "    }\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find force.",
                answer="10",
                out=Path("PhysicsProblems/p001.lean"),
                report_out=Path("reports/p001.json"),
                work_dir=work_dir,
                index="p001",
                formalizer_root=formalizer,
                update_progress=True,
            )
            cmd.run()

            lean_path = project / "PhysicsProblems" / "p001.lean"
            report_path = project / "reports" / "p001.json"
            latest_path = project / ".archon" / "physics-formalize" / "latest.json"
            progress_path = project / ".archon" / "PROGRESS.md"

            self.assertIn("theorem result", lean_path.read_text(encoding="utf-8"))
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["status"], "success")
            latest = json.loads(latest_path.read_text(encoding="utf-8"))
            self.assertFalse(latest["dry_run"])
            self.assertEqual(latest["result"]["consistency_level"], "level_1")
            self.assertEqual(latest["output_lean"], str(lean_path.resolve()))

            progress = progress_path.read_text(encoding="utf-8")
            self.assertIn("## Current Stage", progress)
            self.assertIn("prover", progress)
            self.assertIn("**`PhysicsProblems/p001.lean`**", progress)
            self.assertIn("[prover-mode: physics]", progress)
            self.assertIn("`reports/p001.json`", progress)
            self.assertIn("Blueprint chapter:", progress)

            mode_path = project / ".archon" / "prover-modes" / "physics.md"
            self.assertTrue(mode_path.exists())
            self.assertIn("PhysLean", mode_path.read_text(encoding="utf-8"))

            chapter_path = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "PhysicsProblems_p001.tex"
            )
            self.assertTrue(chapter_path.exists())
            chapter = chapter_path.read_text(encoding="utf-8")
            self.assertIn("% archon:covers PhysicsProblems/p001.lean", chapter)
            self.assertIn(r"\lean{result}", chapter)
            self.assertIn(r"\label{thm:physics:p001:result}", chapter)
            self.assertIn("Find force.", chapter)
            self.assertIn("reports/p001.json", chapter)

            content = (project / "blueprint" / "src" / "content.tex").read_text(
                encoding="utf-8"
            )
            self.assertIn(r"\input{chapters/PhysicsProblems_p001.tex}", content)

            protected = (project / "archon-protected.yaml").read_text(
                encoding="utf-8"
            )
            self.assertIn("PhysicsProblems/p001.lean", protected)
            self.assertIn("result", protected)
            self.assertIn("thm:physics:p001:result", protected)


    def test_batch_dry_run_writes_manifest_without_calling_formalizer(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            dataset = root / "dataset"
            work_dir = project / ".archon" / "physics-formalize" / "batch-dry"

            project.mkdir()
            dataset.mkdir()
            (dataset / "image").mkdir()
            (dataset / "image" / "diagram.png").write_bytes(b"fake image")
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('dry-run should not import Formalizer')\n",
                encoding="utf-8",
            )
            input_jsonl = dataset / "data.jsonl"
            input_jsonl.write_text(
                json.dumps(
                    {
                        "index": "p101",
                        "question": "A 2 kg block accelerates at 3 m/s^2. Find force.",
                        "answer": "6 N",
                        "category": "mechanics",
                        "image": "diagram.png",
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                work_dir=work_dir,
                out_dir=Path("PhysicsProblemsBatch"),
                report_dir=Path("reports/physics"),
                formalizer_root=formalizer,
                dry_run=True,
            )
            cmd.run()

            manifest_path = work_dir / "batch_manifest.json"
            self.assertTrue(manifest_path.exists())
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            latest = json.loads(
                (project / ".archon" / "physics-formalize" / "latest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(manifest["mode"], "batch")
            self.assertTrue(manifest["dry_run"])
            self.assertEqual(manifest["entry_count"], 1)
            self.assertTrue(manifest["use_multimodal"])
            self.assertEqual(manifest["entries"][0]["index"], "p101")
            self.assertEqual(manifest["entries"][0]["answer"], "6 N")
            self.assertEqual(manifest["missing_images"], [])
            self.assertEqual(manifest["output_dir"], str((project / "PhysicsProblemsBatch").resolve()))
            self.assertEqual(latest["mode"], "batch")
            self.assertEqual(latest["input_jsonl"], str(input_jsonl.resolve()))
            self.assertFalse((project / "PhysicsProblemsBatch" / "problem_p101.lean").exists())

    def test_batch_successful_run_writes_outputs_metadata_and_progress(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            dataset = root / "dataset"
            work_dir = project / ".archon" / "physics-formalize" / "batch-run"

            project.mkdir()
            dataset.mkdir()
            (dataset / "image").mkdir()
            (dataset / "image" / "diagram.png").write_bytes(b"fake image")
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "config.py").write_text("", encoding="utf-8")
            (formalizer / "Formalizer" / "main.py").write_text(
                "import config\n"
                "def process_single_problem(entry, output_dir, image_root_dir=None):\n"
                "    suffix = entry['index'].replace('-', '_')\n"
                "    return {\n"
                "        'index': entry['index'],\n"
                "        'status': 'success',\n"
                "        'compilation_passed': True,\n"
                "        'semantic_passed': True,\n"
                "        'consistency_level': 'level_1',\n"
                "        'image_root_dir': image_root_dir,\n"
                "        'use_multimodal': config.USE_MULTIMODAL,\n"
                "        'generated_code': f'import Mathlib\\n\\ntheorem result_{suffix} : True := by sorry\\n',\n"
                "    }\n",
                encoding="utf-8",
            )
            input_jsonl = dataset / "data.jsonl"
            input_jsonl.write_text(
                json.dumps(
                    {
                        "index": "p201",
                        "question": "A 2 kg block accelerates at 3 m/s^2. Find force.",
                        "answer": "6 N",
                        "image": "diagram.png",
                    }
                )
                + "\n"
                + json.dumps(
                    {
                        "index": "p202",
                        "question": "A car moves at constant velocity. Formalize zero acceleration.",
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                work_dir=work_dir,
                out_dir=Path("PhysicsProblemsBatch"),
                report_dir=Path("reports/physics"),
                formalizer_root=formalizer,
                update_progress=True,
            )
            cmd.run()

            lean_1 = project / "PhysicsProblemsBatch" / "problem_p201.lean"
            lean_2 = project / "PhysicsProblemsBatch" / "problem_p202.lean"
            report_1 = project / "reports" / "physics" / "problem_p201.report.json"
            latest_path = project / ".archon" / "physics-formalize" / "latest.json"
            progress_path = project / ".archon" / "PROGRESS.md"

            self.assertIn("theorem result_p201", lean_1.read_text(encoding="utf-8"))
            self.assertIn("theorem result_p202", lean_2.read_text(encoding="utf-8"))
            report = json.loads(report_1.read_text(encoding="utf-8"))
            self.assertTrue(report["use_multimodal"])
            self.assertEqual(report["status"], "success")
            latest = json.loads(latest_path.read_text(encoding="utf-8"))
            self.assertEqual(latest["mode"], "batch")
            self.assertFalse(latest["dry_run"])
            self.assertEqual(latest["result"]["compiled"], 2)
            self.assertEqual(latest["result"]["semantic_passed"], 2)
            self.assertEqual(len(latest["records"]), 2)
            summary_lines = (work_dir / "summary.jsonl").read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(summary_lines), 2)

            progress = progress_path.read_text(encoding="utf-8")
            self.assertIn("**`PhysicsProblemsBatch/problem_p201.lean`**", progress)
            self.assertIn("**`PhysicsProblemsBatch/problem_p202.lean`**", progress)
            self.assertIn("[prover-mode: physics]", progress)

            content = (project / "blueprint" / "src" / "content.tex").read_text(
                encoding="utf-8"
            )
            self.assertIn(
                r"\input{chapters/PhysicsProblemsBatch_problem_p201.tex}",
                content,
            )
            self.assertIn(
                r"\input{chapters/PhysicsProblemsBatch_problem_p202.tex}",
                content,
            )
            protected = (project / "archon-protected.yaml").read_text(
                encoding="utf-8"
            )
            self.assertIn("PhysicsProblemsBatch/problem_p201.lean", protected)
            self.assertIn("result_p201", protected)
            self.assertIn("PhysicsProblemsBatch/problem_p202.lean", protected)
            self.assertIn("result_p202", protected)

    def test_update_progress_can_include_rethlas_blueprint_sketch(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "run"
            rethlas_script = root / "fake_rethlas.py"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "config.py").write_text("", encoding="utf-8")
            (formalizer / "Formalizer" / "main.py").write_text(
                "def process_single_problem(entry, output_dir, image_root_dir=None):\n"
                "    return {\n"
                "        'index': entry['index'],\n"
                "        'question': entry['question'],\n"
                "        'answer': entry.get('answer', ''),\n"
                "        'status': 'success',\n"
                "        'compilation_passed': True,\n"
                "        'semantic_passed': True,\n"
                "        'consistency_level': 'level_1',\n"
                "        'generated_code': 'import Mathlib\\n\\n"
                "theorem result : True := by sorry\\n',\n"
                "    }\n",
                encoding="utf-8",
            )
            rethlas_script.write_text(
                "import sys, json\n"
                "payload = json.load(sys.stdin)\n"
                "print('Resolve the loop into four directed edge-force claims.')\n"
                "print('Use cancellation of opposite vertical edges.')\n"
                "print('Conclude the net force matches ' + payload.get('answer', 'the answer'))\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="A square current loop is in a magnetic field. Find net force.",
                answer="-I B0 L j",
                work_dir=work_dir,
                out=Path("PhysicsProblems/problem_001.lean"),
                report_out=Path("reports/problem_001.report.json"),
                formalizer_root=formalizer,
                update_progress=True,
                with_rethlas_blueprint=True,
                rethlas_command=f"{sys.executable} {rethlas_script}",
            )
            cmd.run()

            chapter = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "PhysicsProblems_problem_001.tex"
            )
            text = chapter.read_text(encoding="utf-8")
            self.assertIn("Rethlas-assisted proof route", text)
            self.assertIn("Resolve the loop into four directed edge-force claims", text)
            self.assertIn("Use cancellation of opposite vertical edges", text)
            self.assertIn("Conclude the net force matches -I B0 L j", text)

    def test_rethlas_blueprint_degrades_when_command_is_missing(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            work_dir = project / ".archon" / "physics-formalize" / "run"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "config.py").write_text("", encoding="utf-8")
            (formalizer / "Formalizer" / "main.py").write_text(
                "def process_single_problem(entry, output_dir, image_root_dir=None):\n"
                "    return {\n"
                "        'index': entry['index'],\n"
                "        'question': entry['question'],\n"
                "        'status': 'success',\n"
                "        'compilation_passed': True,\n"
                "        'semantic_passed': True,\n"
                "        'consistency_level': 'level_1',\n"
                "        'generated_code': 'import Mathlib\\n\\n"
                "theorem result : True := by sorry\\n',\n"
                "    }\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find the acceleration of a block.",
                work_dir=work_dir,
                out=Path("PhysicsProblems/problem_002.lean"),
                report_out=Path("reports/problem_002.report.json"),
                formalizer_root=formalizer,
                update_progress=True,
                with_rethlas_blueprint=True,
                rethlas_command="definitely-not-a-rethlas-command",
            )
            cmd.run()

            chapter = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "PhysicsProblems_problem_002.tex"
            )
            text = chapter.read_text(encoding="utf-8")
            self.assertIn("Rethlas-assisted proof route", text)
            self.assertIn("Rethlas was requested but unavailable", text)
            self.assertIn("Model the physical quantities named in the statement", text)

    def test_batch_mode_rejects_single_problem_options(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = root / "Project"
            formalizer = root / "Auto-formalization"
            input_jsonl = root / "data.jsonl"

            project.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            (formalizer / "Formalizer").mkdir(parents=True)
            (formalizer / "Formalizer" / "main.py").write_text(
                "raise RuntimeError('should fail before import')\n",
                encoding="utf-8",
            )
            input_jsonl.write_text(
                json.dumps({"index": "p1", "question": "Find force."}) + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                question="Find force.",
                formalizer_root=formalizer,
                dry_run=True,
            )
            with self.assertRaises(Exit) as caught:
                cmd.run()
            self.assertEqual(caught.exception.exit_code, 1)


class PhysicsFormalizeConfigTests(unittest.TestCase):
    def setUp(self):
        self._old_modules = {
            name: sys.modules.get(name)
            for name in ("modules", "modules.external_tools", "modules.llm_modules")
        }
        modules_pkg = types.ModuleType("modules")
        external_tools = types.ModuleType("modules.external_tools")

        class LeanCompilerClient:
            def __init__(self, sandbox_path="old-sandbox"):
                self.sandbox_path = sandbox_path

        external_tools.LeanCompilerClient = LeanCompilerClient
        sys.modules["modules"] = modules_pkg
        sys.modules["modules.external_tools"] = external_tools
        self.LeanCompilerClient = LeanCompilerClient

    def tearDown(self):
        for name, module in self._old_modules.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module

    def test_configure_formalizer_sets_physics_mode_and_sandbox_default(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            config = types.SimpleNamespace()
            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find the force.",
                image=project / "diagram.png",
                workers=0,
                decompose=False,
                llm_model="gpt-5",
            )

            runtime_config = {
                "llm_api_key": "secret",
                "llm_base_url": "https://example.test/v1",
                "llm_model": "gpt-5",
                "llm_timeout": 45,
                "llm_supports_temperature": False,
                "leanexplore_api_key": "search-secret",
            }
            cmd._configure_formalizer(config, runtime_config)

            self.assertEqual(config.CURRENT_DOMAIN, "physics")
            self.assertTrue(config.USE_MULTIMODAL)
            self.assertEqual(config.LEAN_SEARCH_PACKAGES, ["Mathlib", "PhysLean"])
            self.assertEqual(config.LEAN_SANDBOX_PATH, str(project.resolve()))
            self.assertEqual(config.CONCURRENT_WORKERS, 1)
            self.assertTrue(config.ABLATION_NO_DECOMPOSE)
            self.assertEqual(config.LLM_API_KEY, "secret")
            self.assertEqual(config.LLM_BASE_URL, "https://example.test/v1")
            self.assertEqual(config.LLM_MODEL_NAME, "gpt-5")
            self.assertEqual(config.LLM_TIMEOUT, 45)
            self.assertFalse(config.SUPPORTS_TEMPERATURE)
            self.assertEqual(config.LEANEXPLORE_API_KEY, "search-secret")
            self.assertEqual(
                self.LeanCompilerClient.__init__.__defaults__,
                (str(project.resolve()),),
            )

    def test_configure_formalizer_patches_native_anthropic_client(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            config = types.SimpleNamespace(LLM_API_KEY="fallback-key")
            llm_modules = types.ModuleType("modules.llm_modules")
            llm_modules._create_openai_client = lambda: "old-client"
            sys.modules["modules.llm_modules"] = llm_modules

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find the force.",
                llm_provider="anthropic",
                llm_api_key="secret",
                llm_model="claude-sonnet-4-5",
                llm_max_tokens=1234,
                llm_timeout=45,
            )
            runtime_config = cmd._resolve_runtime_config()

            cmd._configure_formalizer(config, runtime_config)

            client = llm_modules._create_openai_client()
            self.assertIsInstance(client, _AnthropicOpenAICompatClient)
            self.assertEqual(client.api_key, "secret")
            self.assertEqual(client.base_url, DEFAULT_ANTHROPIC_BASE_URL)
            self.assertEqual(client.max_tokens, 1234)
            self.assertEqual(client.timeout, 45)
            self.assertEqual(config.LLM_MODEL_NAME, "claude-sonnet-4-5")
            self.assertEqual(config.LLM_MAX_TOKENS, 1234)


class AnthropicAdapterTests(unittest.TestCase):
    def test_adapter_converts_openai_style_multimodal_payload(self):
        client = _AnthropicOpenAICompatClient(
            api_key="secret",
            base_url=DEFAULT_ANTHROPIC_BASE_URL,
            max_tokens=99,
        )

        payload = client._to_anthropic_payload(
            {
                "model": "claude-sonnet-4-5",
                "temperature": 0.2,
                "messages": [
                    {"role": "system", "content": "system prompt"},
                    {
                        "role": "user",
                        "content": [
                            {"type": "text", "text": "solve this"},
                            {
                                "type": "image_url",
                                "image_url": {
                                    "url": "data:image/png;base64,ZmFrZQ=="
                                },
                            },
                        ],
                    },
                ],
            }
        )

        self.assertEqual(payload["model"], "claude-sonnet-4-5")
        self.assertEqual(payload["max_tokens"], 99)
        self.assertEqual(payload["temperature"], 0.2)
        self.assertEqual(payload["system"], "system prompt")
        blocks = payload["messages"][0]["content"]
        self.assertEqual(blocks[0], {"type": "text", "text": "solve this"})
        self.assertEqual(blocks[1]["type"], "image")
        self.assertEqual(blocks[1]["source"]["media_type"], "image/png")
        self.assertEqual(blocks[1]["source"]["data"], "ZmFrZQ==")

    def test_adapter_posts_to_anthropic_messages_shape(self):
        seen = {}

        class Handler(BaseHTTPRequestHandler):
            def do_POST(self):
                length = int(self.headers["content-length"])
                seen["path"] = self.path
                seen["api_key"] = self.headers.get("x-api-key")
                seen["authorization"] = self.headers.get("authorization")
                seen["version"] = self.headers.get("anthropic-version")
                seen["payload"] = json.loads(self.rfile.read(length).decode("utf-8"))
                body = json.dumps(
                    {"content": [{"type": "text", "text": "ok from claude"}]}
                ).encode("utf-8")
                self.send_response(200)
                self.send_header("content-type", "application/json")
                self.send_header("content-length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *_args):
                return

        server = HTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            client = _AnthropicOpenAICompatClient(
                api_key="test-key",
                base_url=f"http://127.0.0.1:{server.server_port}/v1",
                max_tokens=64,
            )
            response = client.chat.completions.create(
                model="claude-test",
                temperature=0.3,
                messages=[
                    {"role": "system", "content": "system prompt"},
                    {"role": "user", "content": "formalize this"},
                ],
            )
        finally:
            server.shutdown()
            thread.join(timeout=5)
            server.server_close()

        self.assertEqual(response.choices[0].message.content, "ok from claude")
        self.assertEqual(seen["path"], "/v1/messages")
        self.assertEqual(seen["api_key"], "test-key")
        self.assertEqual(seen["authorization"], "Bearer test-key")
        self.assertEqual(seen["version"], "2023-06-01")
        self.assertEqual(seen["payload"]["model"], "claude-test")
        self.assertEqual(seen["payload"]["max_tokens"], 64)
        self.assertEqual(seen["payload"]["temperature"], 0.3)
        self.assertEqual(seen["payload"]["system"], "system prompt")
        self.assertEqual(
            seen["payload"]["messages"],
            [{"role": "user", "content": [{"type": "text", "text": "formalize this"}]}],
        )

    def test_adapter_wall_clock_timeout_interrupts_blocking_request(self):
        client = _AnthropicOpenAICompatClient(
            api_key="test-key",
            base_url="http://127.0.0.1:9/v1",
            max_tokens=64,
            timeout=1,
        )

        def blocking_urlopen(*_args, **_kwargs):
            time.sleep(5)

        started = time.monotonic()
        with mock.patch(
            "archon.commands.physics_formalize.urllib.request.urlopen",
            side_effect=blocking_urlopen,
        ):
            with self.assertRaisesRegex(RuntimeError, "timed out after 1 seconds"):
                client.chat.completions.create(
                    model="claude-test",
                    messages=[{"role": "user", "content": "formalize this"}],
                )

        self.assertLess(time.monotonic() - started, 3)

    def test_adapter_wall_clock_timeout_interrupts_worker_thread_request(self):
        client = _AnthropicOpenAICompatClient(
            api_key="test-key",
            base_url="http://127.0.0.1:9/v1",
            max_tokens=64,
            timeout=1,
        )
        errors = []

        def blocking_urlopen(*_args, **_kwargs):
            time.sleep(5)

        def call_client():
            try:
                client.chat.completions.create(
                    model="claude-test",
                    messages=[{"role": "user", "content": "formalize this"}],
                )
            except Exception as exc:
                errors.append(exc)

        started = time.monotonic()
        with mock.patch(
            "archon.commands.physics_formalize.urllib.request.urlopen",
            side_effect=blocking_urlopen,
        ):
            thread = threading.Thread(target=call_client)
            thread.start()
            thread.join(timeout=3)

        self.assertFalse(thread.is_alive())
        self.assertLess(time.monotonic() - started, 3)
        self.assertEqual(len(errors), 1)
        self.assertIn("timed out after 1 seconds", str(errors[0]))


class LeanPreflightHintTests(unittest.TestCase):
    def test_physlean_missing_hint_mentions_lake_update_and_target_project(self):
        hint = PhysicsFormalizeCommand._preflight_hint(
            "error: unknown module prefix 'PhysLean'"
        )
        self.assertIsNotNone(hint)
        self.assertIn("lake update PhysLean", hint)
        self.assertIn("target project", hint)


class LeanProofStubTests(unittest.TestCase):
    def test_stub_lean_proofs_replaces_theorem_and_lemma_bodies(self):
        code = (
            "import Mathlib\n\n"
            "theorem foo : (2 : Nat) + 2 = 4 := by\n"
            "  norm_num\n\n"
            "lemma bar : True := by\n"
            "  trivial\n\n"
            "def keep : Nat := 4\n"
        )

        stubbed = PhysicsFormalizeCommand._stub_lean_proofs(code)

        self.assertIn("theorem foo : (2 : Nat) + 2 = 4 := by sorry", stubbed)
        self.assertIn("lemma bar : True := by sorry", stubbed)
        self.assertIn("def keep : Nat := 4", stubbed)
        self.assertNotIn("norm_num", stubbed)
        self.assertNotIn("trivial", stubbed)


class PhysicsFormalizeLoadTests(unittest.TestCase):
    def test_load_formalizer_replaces_stale_config_module(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            formalizer_dir = root / "Auto-formalization" / "Formalizer"
            formalizer_dir.mkdir(parents=True)
            (formalizer_dir / "config.py").write_text(
                "MARKER = 'formalizer-config'\n",
                encoding="utf-8",
            )
            (formalizer_dir / "main.py").write_text(
                "import config\n"
                "def process_single_problem(entry, output_dir, image_root_dir=None):\n"
                "    return {'status': 'success'}\n",
                encoding="utf-8",
            )

            stale = types.ModuleType("config")
            stale.__file__ = str(root / "other" / "config.py")
            stale.MARKER = "stale"
            old_config = sys.modules.get("config")
            old_path = list(sys.path)
            sys.modules["config"] = stale
            self.addCleanup(self._restore_module, "config", old_config)
            self.addCleanup(self._restore_syspath, old_path)

            cmd = PhysicsFormalizeCommand(
                str(root),
                question="Find force.",
                formalizer_root=root / "Auto-formalization",
            )
            process_single_problem, config = cmd._load_formalizer(
                root / "Auto-formalization"
            )

            self.assertTrue(callable(process_single_problem))
            self.assertEqual(config.MARKER, "formalizer-config")

    @staticmethod
    def _restore_module(name: str, module):
        if module is None:
            sys.modules.pop(name, None)
        else:
            sys.modules[name] = module

    @staticmethod
    def _restore_syspath(path):
        sys.path[:] = path


if __name__ == "__main__":
    unittest.main()
