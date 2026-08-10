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
    CHEMISTRY_FORMALIZE_MODE,
    CHEMISTRY_PROVER_MODE,
    CHEMISTRY_REVIEWER,
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
    def test_replace_generated_block_preserves_latex_backslashes(self):
        existing = r"""Hand-written preface.

% --- Archon physics formalization source begin ---
\section{Old source}
% --- Archon physics formalization source end ---

Hand-written appendix.
"""
        generated = r"""% --- Archon physics formalization source begin ---
\section{Updated source}
The uncertainty is $\sigma$.
% --- Archon physics formalization source end ---
"""

        replaced = PhysicsFormalizeCommand._replace_or_append_generated_block(
            existing,
            generated,
        )

        self.assertIn(r"\section{Updated source}", replaced)
        self.assertIn(r"$\sigma$", replaced)
        self.assertNotIn(r"\section{Old source}", replaced)
        self.assertIn("Hand-written preface.", replaced)
        self.assertIn("Hand-written appendix.", replaced)
        self.assertEqual(
            replaced.count("% --- Archon physics formalization source begin ---"),
            1,
        )

    def test_phyx_entry_normalization_resolves_answer_and_context(self):
        entry = PhysicsFormalizeCommand._normalize_phyx_entry(
            {
                "index": "0",
                "description": "Two equal pulls act symmetrically at 32 degrees.",
                "question": "How large should the pulls be?",
                "image": "0.png",
                "options": chr(65) + ":\"7.55 N\"," + chr(66) + ":\"5.55 N\"",
                "answer": "A",
                "category": "Mechanics",
                "subfield": "Statics",
                "reasoning_type": ["Spatial Relation Reasoning"],
                "image_caption": "The ropes are symmetric about the arm.",
            },
            line_no=1,
        )
        self.assertEqual(entry["index"], "phyx_0")
        self.assertEqual(entry["dataset"], "Cloudriver/PhyX")
        self.assertEqual(entry["answer"], "A: 7.55 N")
        self.assertEqual(entry["answer_text"], "7.55 N")
        self.assertIn("## Physical scenario", entry["question"])
        self.assertIn("- A: 7.55 N", entry["question"])
        self.assertIn("Spatial Relation Reasoning", entry["question"])

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
            self.assertEqual(report["schema_version"], 2)
            self.assertEqual(report["path_base"], "project")
            self.assertEqual(report["project_path"], ".")
            self.assertEqual(report["output_lean"], "PhysicsProblems/p001.lean")
            self.assertEqual(report["source_report"], "reports/p001.source.json")
            self.assertEqual(report["status"], "prepared")
            self.assertEqual(report["next_stage"], "autoformalize")
            self.assertEqual(report["entry"]["answer"], "10 N")

            latest = json.loads(latest_path.read_text(encoding="utf-8"))
            self.assertFalse(latest["dry_run"])
            self.assertEqual(latest["result"]["status"], "prepared")
            self.assertEqual(latest["result"]["next_stage"], "autoformalize")
            self.assertEqual(latest["project_path"], str(project.resolve()))
            self.assertEqual(latest["output_lean"], str(lean_path.resolve()))
            self.assertEqual(latest["source_report"], str(report_path.resolve()))

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

    def test_single_image_is_portable_but_runtime_metadata_stays_absolute(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            image_path = project / "references" / "figure.png"
            image_path.parent.mkdir()
            image_path.write_bytes(b"figure")
            work_dir = project / ".archon" / "physics-formalize" / "image"
            report_path = project / "reports" / "image.source.json"

            cmd = PhysicsFormalizeCommand(
                str(project),
                question="Read the project-local figure.",
                image=image_path,
                out=Path("PhysicsProblems/image.lean"),
                report_out=Path("reports/image.source.json"),
                work_dir=work_dir,
                index="image",
            )
            cmd.run()

            report_text = report_path.read_text(encoding="utf-8")
            report = json.loads(report_text)
            self.assertEqual(report["entry"]["image_path"], "references/figure.png")
            self.assertEqual(report["entry"]["image_paths"], ["references/figure.png"])
            self.assertNotIn(str(project.resolve()), report_text)

            chapter = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "PhysicsProblems_image.tex"
            ).read_text(encoding="utf-8")
            self.assertIn("references/figure.png", chapter)
            self.assertNotIn(str(project.resolve()), chapter)

            manifest = json.loads(
                (work_dir / "problem_image_manifest.json").read_text(encoding="utf-8")
            )
            latest = json.loads(
                (
                    project / ".archon" / "physics-formalize" / "latest.json"
                ).read_text(encoding="utf-8")
            )
            for runtime in (manifest, latest):
                self.assertEqual(runtime["project_path"], str(project.resolve()))
                self.assertEqual(
                    runtime["output_lean"],
                    str((project / "PhysicsProblems/image.lean").resolve()),
                )
                self.assertEqual(runtime["source_report"], str(report_path.resolve()))
                self.assertEqual(
                    runtime["entry"]["image_path"], str(image_path.resolve())
                )
                self.assertEqual(
                    runtime["entry"]["image_paths"], [str(image_path.resolve())]
                )

    def test_update_progress_replaces_stage_when_stages_section_is_absent(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            state = project / ".archon"
            state.mkdir()
            progress_path = state / "PROGRESS.md"
            progress_path.write_text(
                "# Progress\n\n"
                "## Current Stage\n\n"
                "prover\n\n"
                "## Current Objectives\n\n"
                "old objective\n",
                encoding="utf-8",
            )
            cmd = PhysicsFormalizeCommand(
                str(project),
                question="A chemistry target.",
                out=Path("Chem/Target.lean"),
                work_dir=state / "physics-formalize" / "single",
            )

            cmd._update_progress_records([
                {
                    "rel_lean": "Chem/Target.lean",
                    "rel_report": "reports/target.source.json",
                    "rel_chapter": "blueprint/src/chapters/Chem_Target.tex",
                }
            ])

            progress = progress_path.read_text(encoding="utf-8")
            self.assertEqual(progress.count("## Current Stage"), 1)
            self.assertIn("## Current Stage\n\nautoformalize\n", progress)
            self.assertIn("**`Chem/Target.lean`**", progress)
            self.assertNotIn("old objective", progress)

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

    def test_chemistry_profile_installs_domain_assets_and_preserves_all_images(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project = _make_project(root)
            state = project / ".archon"
            state.mkdir()
            (state / "config.json").write_text(
                json.dumps(
                    {
                        "loop": {
                            "domain_profile": {
                                "name": "chemistry",
                                "display_name": "chemistry",
                                "preflight_imports": ["Mathlib"],
                                "lean_search_packages": [
                                    "Mathlib",
                                    "Physlib",
                                    "CRNT",
                                ],
                                "target_import_prefixes": ["IChO2026Chem"],
                                "enforce_classical_physics_modeling": False,
                                "require_explicit_mathlib_import": False,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            dataset = root / "dataset"
            images = dataset / "images"
            images.mkdir(parents=True)
            (images / "primary.png").write_bytes(b"primary")
            (images / "context.png").write_bytes(b"context")
            input_jsonl = dataset / "data.jsonl"
            input_jsonl.write_text(
                json.dumps(
                    {
                        "index": "icho_t1_a1",
                        "question": "Determine the isotope abundance from both pages.",
                        "answer": "x = 0.75",
                        "image": "primary.png",
                        "images": ["primary.png", "context.png"],
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            cmd = PhysicsFormalizeCommand(
                str(project),
                input_jsonl=input_jsonl,
                image_root=Path("images"),
                work_dir=state / "physics-formalize" / "chemistry",
                out_dir=Path("IChO2026Problems"),
                report_dir=Path("reports/chemistry"),
                update_progress=True,
            )
            cmd.run()

            report = json.loads(
                (
                    project
                    / "reports"
                    / "chemistry"
                    / "problem_icho_t1_a1.source.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(report["domain"], "chemistry")
            self.assertEqual(report["prover_mode"], CHEMISTRY_FORMALIZE_MODE)
            self.assertEqual(report["proof_mode"], CHEMISTRY_PROVER_MODE)
            self.assertEqual(
                report["entry"]["images"],
                ["primary.png", "context.png"],
            )
            self.assertEqual(
                report["entry"]["image_path"],
                "../dataset/images/primary.png",
            )
            self.assertEqual(
                report["entry"]["image_paths"],
                [
                    "../dataset/images/primary.png",
                    "../dataset/images/context.png",
                ],
            )

            chapter = (
                project
                / "blueprint"
                / "src"
                / "chapters"
                / "IChO2026Problems_problem_icho_t1_a1.tex"
            ).read_text(encoding="utf-8")
            self.assertIn("% archon:chemistry", chapter)
            self.assertIn("Figure/image paths", chapter)
            self.assertIn("../dataset/images/primary.png", chapter)
            self.assertIn("../dataset/images/context.png", chapter)
            self.assertIn("primary.png", chapter)
            self.assertIn("context.png", chapter)
            self.assertNotIn(str(images.resolve()), chapter)

            latest = json.loads(
                (state / "physics-formalize" / "latest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(latest["project_path"], str(project.resolve()))
            self.assertEqual(latest["image_root"], str(images.resolve()))
            self.assertEqual(
                latest["records"][0]["output_lean"],
                str((project / "IChO2026Problems/problem_icho_t1_a1.lean").resolve()),
            )
            self.assertEqual(
                latest["records"][0]["source_report"],
                str(
                    (
                        project
                        / "reports"
                        / "chemistry"
                        / "problem_icho_t1_a1.source.json"
                    ).resolve()
                ),
            )

            progress = (state / "PROGRESS.md").read_text(encoding="utf-8")
            self.assertIn(f"[prover-mode: {CHEMISTRY_FORMALIZE_MODE}]", progress)
            self.assertIn(f"prover mode `{CHEMISTRY_PROVER_MODE}`", progress)
            self.assertTrue(
                (state / "prover-modes" / f"{CHEMISTRY_FORMALIZE_MODE}.md").is_file()
            )
            self.assertTrue(
                (state / "prover-modes" / f"{CHEMISTRY_PROVER_MODE}.md").is_file()
            )
            reviewer = state / "subagents" / f"{CHEMISTRY_REVIEWER}.md"
            self.assertTrue(reviewer.is_file())
            self.assertIn(
                f"name: {CHEMISTRY_REVIEWER}",
                reviewer.read_text(encoding="utf-8"),
            )
            self.assertFalse((state / "prover-modes" / "quantum-formalize.md").exists())

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
