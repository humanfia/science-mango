"""Tests for the Archon-native physics formalization preparation command.

`archon physics-formalize` no longer runs the copied Auto-Formalizer. It
prepares physics blueprint chapters and an autoformalize-stage PROGRESS.md
entry; `archon loop` owns Lean generation and proof.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import typer

from archon.commands.physics_formalize import (
    PHYSICS_FORMALIZE_MODE,
    PHYSICS_PROVER_MODE,
    PHYSLEAN_GIT_URL,
    PhysicsFormalizeCommand,
)

Exit = typer.Exit


def _make_project(root: Path) -> Path:
    project = root / "Project"
    project.mkdir()
    (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
    return project


class PhysicsFormalizePrepareTests(unittest.TestCase):
    def test_single_problem_prepares_autoformalize_target_without_calling_formalizer(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            work_dir = project / ".archon" / "physics-formalize" / "single"

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="A block has mass 5 kg and acceleration 2 m/s^2. Find force.",
                answer="10 N",
                out=Path("PhysicsProblems/p001.lean"),
                report_out=Path("reports/p001.source.json"),
                work_dir=work_dir,
                index="p001",
                update_progress=True,
            )
            with mock.patch.object(
                PhysicsFormalizeCommand,
                "_load_formalizer",
                create=True,
                side_effect=AssertionError("Auto-Formalizer must not run"),
            ):
                cmd.run()

            lean_path = project / "PhysicsProblems" / "p001.lean"
            report_path = project / "reports" / "p001.source.json"
            latest_path = project / ".archon" / "physics-formalize" / "latest.json"
            progress_path = project / ".archon" / "PROGRESS.md"
            chapter_path = (
                project / "blueprint" / "src" / "chapters" / "PhysicsProblems_p001.tex"
            )

            self.assertFalse(lean_path.exists())
            self.assertTrue(report_path.exists())
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["status"], "prepared")
            self.assertEqual(report["next_stage"], "autoformalize")
            self.assertEqual(report["entry"]["answer"], "10 N")

            latest = json.loads(latest_path.read_text(encoding="utf-8"))
            self.assertFalse(latest["dry_run"])
            self.assertEqual(latest["result"]["status"], "prepared")
            self.assertEqual(latest["result"]["next_stage"], "autoformalize")
            self.assertEqual(latest["output_lean"], str(lean_path.resolve()))

            progress = progress_path.read_text(encoding="utf-8")
            self.assertIn("## Current Stage", progress)
            self.assertIn("autoformalize", progress)
            self.assertIn("**`PhysicsProblems/p001.lean`**", progress)
            self.assertIn(f"[prover-mode: {PHYSICS_FORMALIZE_MODE}]", progress)
            self.assertNotIn(f"[prover-mode: {PHYSICS_PROVER_MODE}]", progress)

            chapter = chapter_path.read_text(encoding="utf-8")
            self.assertIn("% archon:physics", chapter)
            self.assertIn("% archon:covers PhysicsProblems/p001.lean", chapter)
            self.assertIn("A block has mass 5 kg", chapter)
            self.assertIn("10 N", chapter)
            self.assertIn("create a compiling Lean file with sorry bodies", chapter)

            self.assertTrue((project / ".archon" / "prover-modes" / "physics.md").exists())
            self.assertTrue(
                (project / ".archon" / "prover-modes" / "physics-formalize.md").exists()
            )

    def test_batch_prepare_writes_one_chapter_and_objective_per_entry(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            dataset = root / "dataset"
            dataset.mkdir()
            input_jsonl = dataset / "data.jsonl"
            input_jsonl.write_text(
                json.dumps(
                    {
                        "index": "p101",
                        "question": "A 2 kg block accelerates at 3 m/s^2. Find force.",
                        "answer": "6 N",
                    }
                )
                + "\n"
                + json.dumps(
                    {
                        "index": "p102",
                        "question": "A car moves at constant velocity. State acceleration.",
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                work_dir=project / ".archon" / "physics-formalize" / "batch",
                out_dir=Path("PhysicsProblemsBatch"),
                report_dir=Path("reports/physics"),
                update_progress=True,
            )
            with mock.patch.object(
                PhysicsFormalizeCommand,
                "_load_formalizer",
                create=True,
                side_effect=AssertionError("Auto-Formalizer must not run"),
            ):
                cmd.run()

            self.assertFalse((project / "PhysicsProblemsBatch" / "problem_p101.lean").exists())
            self.assertFalse((project / "PhysicsProblemsBatch" / "problem_p102.lean").exists())
            self.assertTrue((project / "reports" / "physics" / "problem_p101.source.json").exists())
            self.assertTrue((project / "reports" / "physics" / "problem_p102.source.json").exists())

            progress = (project / ".archon" / "PROGRESS.md").read_text(encoding="utf-8")
            self.assertIn("**`PhysicsProblemsBatch/problem_p101.lean`**", progress)
            self.assertIn("**`PhysicsProblemsBatch/problem_p102.lean`**", progress)
            self.assertEqual(progress.count(f"[prover-mode: {PHYSICS_FORMALIZE_MODE}]"), 2)

            content = (project / "blueprint" / "src" / "content.tex").read_text(
                encoding="utf-8"
            )
            self.assertIn(r"\input{chapters/PhysicsProblemsBatch_problem_p101.tex}", content)
            self.assertIn(r"\input{chapters/PhysicsProblemsBatch_problem_p102.tex}", content)

            latest = json.loads(
                (project / ".archon" / "physics-formalize" / "latest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(latest["mode"], "batch")
            self.assertEqual(latest["result"]["prepared"], 2)

    def test_problem_set_prepare_moves_previous_parts_into_blueprint_not_formalizer(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            dataset = root / "dataset"
            dataset.mkdir()
            input_jsonl = dataset / "data.jsonl"
            input_jsonl.write_text(
                json.dumps(
                    {
                        "index": "IPhO_2024_2_A_1",
                        "problem_id": "IPhO_2024_2",
                        "part_id": "A.1",
                        "context": "Shared trap setup. Ring radius R is positive.",
                        "current_question": "Find the first-order electric field.",
                        "question": "Shared trap setup. Find the first-order electric field.",
                        "answer": "E-field formula",
                        "previous_parts": [],
                    }
                )
                + "\n"
                + json.dumps(
                    {
                        "index": "IPhO_2024_2_A_2",
                        "problem_id": "IPhO_2024_2",
                        "part_id": "A.2",
                        "context": "Shared trap setup. Use the same ring parameters.",
                        "current_question": "Write k and a in terms of known parameters.",
                        "question": "Shared trap setup. Write k and a.",
                        "answer": "k and a formulas",
                        "previous_parts": [
                            {
                                "source_id": "IPhO_2024_2_A_1",
                                "part_id": "A.1",
                                "question": "Find the first-order electric field.",
                                "answer": "E-field formula",
                                "reusable_conclusions": ["E-field formula"],
                                "dependency_policy": "natural_language_prerequisite_only; do_not_import_Lean_output",
                            }
                        ],
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                problem_id="IPhO_2024_2",
                as_problem_set=True,
                work_dir=project / ".archon" / "physics-formalize" / "problem-set",
                out_dir=Path("PhysicsProblems"),
                report_dir=Path("reports/physics"),
                update_progress=True,
            )
            with mock.patch.object(
                PhysicsFormalizeCommand,
                "_load_formalizer",
                create=True,
                side_effect=AssertionError("Auto-Formalizer must not run"),
            ):
                cmd.run()

            self.assertFalse((project / "PhysicsProblems" / "IPhO_2024_2" / "A_1.lean").exists())
            self.assertFalse((project / "PhysicsProblems" / "IPhO_2024_2" / "A_2.lean").exists())
            self.assertFalse(list((project / ".archon" / "physics-formalize" / "problem-set").glob("entry_*.json")))

            progress = (project / ".archon" / "PROGRESS.md").read_text(encoding="utf-8")
            self.assertIn("**`PhysicsProblems/IPhO_2024_2/A_1.lean`**", progress)
            self.assertIn("**`PhysicsProblems/IPhO_2024_2/A_2.lean`**", progress)
            self.assertEqual(progress.count(f"[prover-mode: {PHYSICS_FORMALIZE_MODE}]"), 2)

            chapter_a2 = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "PhysicsProblems_IPhO_2024_2_A_2.tex"
            ).read_text(encoding="utf-8")
            self.assertIn("% archon:previous-part IPhO_2024_2_A_1", chapter_a2)
            self.assertIn(
                "% archon:previous-part-policy natural_language_prerequisite_only",
                chapter_a2,
            )
            self.assertIn("Reusable previous-part conclusions", chapter_a2)
            self.assertIn("E-field formula", chapter_a2)
            self.assertNotIn(r"\uses{thm:physics:IPhO_2024_2_A_1", chapter_a2)

            latest = json.loads(
                (project / ".archon" / "physics-formalize" / "latest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                latest["dependencies"]["IPhO_2024_2_A_2"],
                ["IPhO_2024_2_A_1"],
            )

    def test_dry_run_writes_manifest_without_blueprint_or_progress(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            work_dir = project / ".archon" / "physics-formalize" / "dry"

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Find force.",
                work_dir=work_dir,
                index="p002",
                dry_run=True,
                update_progress=True,
            )
            cmd.run()

            manifest = json.loads(
                (work_dir / "problem_p002_manifest.json").read_text(encoding="utf-8")
            )
            latest = json.loads(
                (project / ".archon" / "physics-formalize" / "latest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(manifest["dry_run"])
            self.assertEqual(manifest["next_stage"], "autoformalize")
            self.assertTrue(latest["dry_run"])
            self.assertFalse((project / ".archon" / "PROGRESS.md").exists())
            self.assertFalse((project / "blueprint").exists())

    def test_ensure_physlean_dependency_remains_environment_preparation(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            lakefile = project / "lakefile.lean"

            with mock.patch(
                "archon.commands.physics_formalize.shutil.which",
                return_value="/fake/lake",
            ), mock.patch(
                "archon.commands.physics_formalize.subprocess.run",
                return_value=type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})(),
            ):
                cmd = PhysicsFormalizeCommand(
                    str(project),
                    question="Find force.",
                    work_dir=project / ".archon" / "physics-formalize" / "env",
                    index="p003",
                    dry_run=True,
                    ensure_physlean=True,
                )
                cmd.run()

            text = lakefile.read_text(encoding="utf-8")
            self.assertIn("require PhysLean", text)
            self.assertIn(PHYSLEAN_GIT_URL, text)

    def test_problem_set_requires_problem_id(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            input_jsonl = root / "data.jsonl"
            input_jsonl.write_text(
                json.dumps({"index": "p1", "question": "Find force."}) + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                as_problem_set=True,
                dry_run=True,
            )
            with self.assertRaises(Exit) as caught:
                cmd.run()
            self.assertEqual(caught.exception.exit_code, 1)


if __name__ == "__main__":
    unittest.main()
