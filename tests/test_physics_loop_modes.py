from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import typer

from archon.commands.loop.blueprint_doctor import run_blueprint_doctor
from archon.commands.loop.command import (
    _ensure_loop_prover_modes,
    _ensure_loop_subagents,
)
from archon.commands.loop.preflight import require_physics_lean_environment
from archon.commands.loop.physics_grounding import (
    GroundingCandidate,
    run_physics_grounding,
)
from archon.commands.loop.phases.physics_grounding import PhysicsGroundingPhase
from archon.commands.loop.phases.review import (
    _enforce_physics_doctor_blocker_gate,
    _load_physics_doctor_blockers,
    _load_physics_reviewer_blockers,
    _load_physics_session_review_blockers,
)
from archon.commands.loop.prover.runners import (
    ParallelProverRunner,
    select_prover_mode_for_target,
)
from archon.state import archive_task_results, is_complete, read_stage


def _write_mode(state_dir: Path, name: str, *, default_for: str | None = None) -> None:
    modes = state_dir / "prover-modes"
    modes.mkdir(parents=True, exist_ok=True)
    defaults = f"\ndefault_for_stages:\n  - {default_for}\n" if default_for else ""
    (modes / f"{name}.md").write_text(
        f"---\nname: {name}\ncompatible_stages:\n  - autoformalize\n  - prover\n"
        f"{defaults}read_blueprint: true\n---\n\n# {name}\n",
        encoding="utf-8",
    )


def _write_progress(progress: Path, stage: str) -> None:
    progress.write_text(
        f"## Current Stage\n\n{stage}\n\n## Stages\n\n- autoformalize\n- prover\n- COMPLETE\n",
        encoding="utf-8",
    )


class PhysicsLoopModeSelectionTest(unittest.TestCase):
    def test_physics_chapter_uses_physics_formalize_in_autoformalize(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            _write_mode(state, "formalize", default_for="autoformalize")
            _write_mode(state, "physics-formalize")

            chapter = project / "blueprint" / "src" / "chapters" / "IPhO_Test.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("% archon:physics\n\\begin{theorem}\\end{theorem}\n")
            target = project / "IPhO_Test.lean"

            self.assertEqual(
                select_prover_mode_for_target(
                    state, "autoformalize", project, target, explicit_mode=None,
                ),
                "physics-formalize",
            )

    def test_physics_chapter_uses_physics_mode_in_prover_stage(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            _write_mode(state, "prove", default_for="prover")
            _write_mode(state, "physics")

            chapter = project / "blueprint" / "src" / "chapters" / "Physics_Main.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("% archon:physics\n")
            target = project / "Physics/Main.lean"

            self.assertEqual(
                select_prover_mode_for_target(
                    state, "prover", project, target, explicit_mode=None,
                ),
                "physics",
            )

    def test_explicit_mode_tag_wins_over_physics_auto_selection(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            _write_mode(state, "formalize", default_for="autoformalize")
            _write_mode(state, "physics-formalize")
            _write_mode(state, "fine-grained")

            chapter = project / "blueprint" / "src" / "chapters" / "P.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("% archon:physics\n")

            self.assertEqual(
                select_prover_mode_for_target(
                    state, "autoformalize", project, project / "P.lean",
                    explicit_mode="fine-grained",
                ),
                "fine-grained",
            )

    def test_non_physics_chapter_uses_stage_default(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            _write_mode(state, "formalize", default_for="autoformalize")
            _write_mode(state, "physics-formalize")

            chapter = project / "blueprint" / "src" / "chapters" / "Plain.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("\\begin{theorem}\\end{theorem}\n")

            self.assertEqual(
                select_prover_mode_for_target(
                    state, "autoformalize", project, project / "Plain.lean",
                    explicit_mode=None,
                ),
                "formalize",
            )


class LoopProverModeInstallTest(unittest.TestCase):
    def test_loop_bootstrap_installs_missing_builtin_prover_modes(self):
        with tempfile.TemporaryDirectory() as d:
            state = Path(d) / ".archon"
            _ensure_loop_prover_modes(state)

            self.assertTrue((state / "prover-modes" / "formalize.md").is_file())
            self.assertTrue((state / "prover-modes" / "physics.md").is_file())
            self.assertTrue(
                (state / "prover-modes" / "physics-formalize.md").is_file()
            )

    def test_loop_bootstrap_installs_missing_builtin_subagents(self):
        with tempfile.TemporaryDirectory() as d:
            state = Path(d) / ".archon"
            _ensure_loop_subagents(state)

            self.assertTrue((state / "subagents" / "physics-reviewer.md").is_file())
            self.assertTrue((state / "subagents" / "lean-auditor.md").is_file())


class PhysicsLeanEnvironmentPreflightTest(unittest.TestCase):
    def test_physics_aware_project_without_lakefile_fails(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            (state / "config.json").write_text(
                '{"loop": {"physics_aware": true}}\n',
                encoding="utf-8",
            )

            with patch("archon.commands.loop.preflight.shutil.which", return_value="/fake/lake"):
                with self.assertRaises(typer.Exit):
                    require_physics_lean_environment(project, state)

    def test_physics_chapter_requires_lake_env_physlib_imports(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            chapter = project / "blueprint" / "src" / "chapters" / "P.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("% archon:physics\n", encoding="utf-8")

            class Result:
                returncode = 0
                stdout = ""
                stderr = ""

            with patch("archon.commands.loop.preflight.shutil.which", return_value="/fake/lake"):
                with patch(
                    "archon.commands.loop.preflight.subprocess.run",
                    return_value=Result(),
                ) as run:
                    require_physics_lean_environment(project, state)

            command = run.call_args.args[0]
            self.assertEqual(command[:3], ["/fake/lake", "env", "lean"])
            preflight_file = Path(command[3])
            text = preflight_file.read_text(encoding="utf-8")
            self.assertIn("import Mathlib", text)
            self.assertIn("import Physlib.Electromagnetism.Basic", text)


class PhysicsReviewDoctorGateTest(unittest.TestCase):
    def test_loads_current_iter_physics_doctor_blockers(self):
        with tempfile.TemporaryDirectory() as d:
            state = Path(d) / ".archon"
            report_dir = state / "logs" / "iter-003"
            report_dir.mkdir(parents=True)
            (report_dir / "blueprint-doctor.json").write_text(
                json.dumps({
                    "physics_modeling_problems": [
                        {
                            "file": "/p/Phys.lean",
                            "kind": "scalar-fallback",
                            "reason": "Current is defined directly as ℝ",
                        },
                    ],
                    "physics_grounding_problems": [
                        {
                            "file": "/p/Phys.lean",
                            "kind": "missing-grounding-log",
                            "reason": "no LeanExplore log",
                        },
                    ],
                }),
                encoding="utf-8",
            )

            blockers = _load_physics_doctor_blockers(state, 3)

            self.assertEqual(len(blockers), 2)
            self.assertEqual(
                {b["kind"] for b in blockers},
                {"scalar-fallback", "missing-grounding-log"},
            )

    def test_gate_resets_complete_stage_and_writes_auto_note(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            state = root / ".archon"
            report_dir = state / "logs" / "iter-004"
            report_dir.mkdir(parents=True)
            (report_dir / "blueprint-doctor.json").write_text(
                json.dumps({
                    "physics_modeling_problems": [
                        {
                            "file": str(root / "Phys.lean"),
                            "kind": "scalar-fallback",
                            "reason": "Charge is defined directly as ℝ",
                        },
                    ],
                    "physics_grounding_problems": [],
                }),
                encoding="utf-8",
            )
            progress = state / "PROGRESS.md"
            _write_progress(progress, "COMPLETE")

            blockers, reset = _enforce_physics_doctor_blocker_gate(
                state, progress, 4,
            )

            self.assertEqual(len(blockers), 1)
            self.assertTrue(reset)
            self.assertEqual(read_stage(progress), "autoformalize")
            notes = (state / "AUTO_NOTES.md").read_text(encoding="utf-8")
            self.assertIn("archon[physics-doctor]", notes)
            self.assertIn("scalar-fallback", notes)

    def test_lowercase_complete_stage_counts_as_complete(self):
        with tempfile.TemporaryDirectory() as d:
            progress = Path(d) / "PROGRESS.md"
            _write_progress(progress, "complete")

            self.assertTrue(is_complete(progress))

    def test_loads_physics_reviewer_modeling_blockers(self):
        with tempfile.TemporaryDirectory() as d:
            state = Path(d) / ".archon"
            reports = state / "task_results"
            reports.mkdir(parents=True)
            (reports / "physics-reviewer-Phys.md").write_text(
                "\n".join([
                    "# Physics Review Report",
                    "",
                    "## Slug",
                    "Phys",
                    "",
                    "## Must-fix-this-iter",
                    "- PhysicsProblems/Phys.lean:ring_axis_field_linearization — current target is smuggled into `Satisfies...`. Why must-fix: answer-as-assumption.",
                    "",
                    "## Overall verdict",
                    "BLOCKED ON MODELING — target formula appears as a hypothesis.",
                ]),
                encoding="utf-8",
            )

            blockers = _load_physics_reviewer_blockers(state)

            self.assertEqual(len(blockers), 1)
            self.assertEqual(blockers[0]["source"], "physics-reviewer")
            self.assertEqual(blockers[0]["kind"], "BLOCKED ON MODELING")
            self.assertIn("answer-as-assumption", blockers[0]["reason"])

    def test_gate_resets_complete_for_physics_reviewer_blocker(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            state = root / ".archon"
            reports = state / "task_results"
            reports.mkdir(parents=True)
            (reports / "physics-reviewer-Phys.md").write_text(
                "\n".join([
                    "# Physics Review Report",
                    "",
                    "## Must-fix-this-iter",
                    "- PhysicsProblems/Phys.lean:main — theorem assumes the current target conclusion. Why must-fix: goal weakening.",
                    "",
                    "## Overall verdict",
                    "BLOCKED ON MODELING",
                ]),
                encoding="utf-8",
            )
            progress = state / "PROGRESS.md"
            _write_progress(progress, "COMPLETE")

            blockers, reset = _enforce_physics_doctor_blocker_gate(
                state, progress, 4,
            )

            self.assertEqual(len(blockers), 1)
            self.assertTrue(reset)
            self.assertEqual(read_stage(progress), "autoformalize")
            notes = (state / "AUTO_NOTES.md").read_text(encoding="utf-8")
            self.assertIn("archon[physics-reviewer]", notes)
            self.assertIn("goal weakening", notes)

    def test_gate_resets_complete_for_main_review_blocker(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            state = root / ".archon"
            session = state / "proof-journal" / "sessions" / "session_004"
            session.mkdir(parents=True)
            (session / "summary.md").write_text(
                "Overall verdict: BLOCKED ON MODELING — current theorem "
                "assumes the answer-as-assumption target.\n",
                encoding="utf-8",
            )
            progress = state / "PROGRESS.md"
            _write_progress(progress, "COMPLETE")

            session_blockers = _load_physics_session_review_blockers(state, 4)
            blockers, reset = _enforce_physics_doctor_blocker_gate(
                state, progress, 4,
            )

            self.assertEqual(len(session_blockers), 1)
            self.assertEqual(session_blockers[0]["source"], "review-agent")
            self.assertEqual(len(blockers), 1)
            self.assertTrue(reset)
            self.assertEqual(read_stage(progress), "autoformalize")
            notes = (state / "AUTO_NOTES.md").read_text(encoding="utf-8")
            self.assertIn("archon[review-agent]", notes)
            self.assertIn("answer-as-assumption", notes)
            self.assertIn("must not mark COMPLETE", notes)


class PhysicsGroundingLogTest(unittest.TestCase):
    def test_generates_doctor_accepted_grounding_log_from_blueprint(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            src = project / "blueprint" / "src"
            chapters = src / "chapters"
            chapters.mkdir(parents=True)
            (src / "content.tex").write_text(
                "\\input{chapters/P}\n",
                encoding="utf-8",
            )
            (chapters / "P.tex").write_text(
                "% archon:physics\n"
                "% archon:covers P.lean\n"
                "\\begin{definition}[Charged ring parameters]\n"
                "\\label{def:params}\\lean{P.ChargedRingParameters}\n"
                "A radius, charge density, mass, and vacuum permittivity.\n"
                "\\end{definition}\n"
                "\\begin{theorem}[Harmonic oscillator frequency]\n"
                "\\label{thm:freq}\\lean{P.frequency}\n"
                "The electric field gives a transverse small oscillation "
                "frequency using Real.sqrt.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            (project / "P.lean").write_text(
                "theorem target : True := by sorry\n",
                encoding="utf-8",
            )

            seen: list[tuple[str, tuple[str, ...]]] = []

            def fake_searcher(query: str, packages: list[str], limit: int):
                seen.append((query, tuple(packages)))
                return [
                    GroundingCandidate(
                        name="Real.sqrt",
                        module="Mathlib.Data.Real.Sqrt",
                        docstring="Square root on real numbers.",
                    ),
                    GroundingCandidate(
                        name="PhysLean.Electromagnetism.Basic",
                        module="Physlib.Electromagnetism.Basic",
                        docstring="Electromagnetism infrastructure.",
                    ),
                ][:limit]

            reports = run_physics_grounding(project, searcher=fake_searcher)

            self.assertEqual(len(reports), 1)
            self.assertTrue(reports[0].is_complete)
            self.assertEqual(reports[0].report_path.name, "physics-grounding-P.md")
            self.assertTrue(reports[0].report_path.is_file())
            text = reports[0].report_path.read_text(encoding="utf-8")
            self.assertIn("LeanExplore queries/candidates actually used", text)
            self.assertIn("Grounded Mathlib/PhysLean names", text)
            self.assertIn("Local abstractions introduced", text)
            self.assertIn("Grounding gaps", text)
            self.assertIn("Mathlib", text)
            self.assertIn("PhysLean", text)
            self.assertTrue(seen)
            self.assertIn("electric field", [query for query, _ in seen])
            self.assertTrue(all(packages == ("Mathlib", "Physlib") for _, packages in seen))

            doctor = run_blueprint_doctor(project)
            self.assertIsNotNone(doctor)
            self.assertEqual(doctor.physics_grounding_problems, [])

    def test_partial_leanexplore_failures_do_not_poison_successful_grounding_log(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            src = project / "blueprint" / "src"
            chapters = src / "chapters"
            chapters.mkdir(parents=True)
            (src / "content.tex").write_text(
                "\\input{chapters/P}\n",
                encoding="utf-8",
            )
            (chapters / "P.tex").write_text(
                "% archon:physics\n"
                "% archon:covers P.lean\n"
                "\\begin{theorem}[Electric field square-root expression]\n"
                "\\label{thm:field}\\lean{P.field}\n"
                "An electric field statement involving Real.sqrt.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            (project / "P.lean").write_text(
                "theorem target : True := by sorry\n",
                encoding="utf-8",
            )

            def fake_searcher(query: str, packages: list[str], limit: int):
                if query == "electric field":
                    raise RuntimeError("Server error: transient 500")
                return [
                    GroundingCandidate(
                        name="Real.sqrt",
                        module="Mathlib.Analysis.Real.Sqrt",
                        docstring="Square root on real numbers.",
                    ),
                    GroundingCandidate(
                        name="Electromagnetism.ElectricField",
                        module="Physlib.Electromagnetism.Basic",
                        docstring="The electric field.",
                    ),
                ][:limit]

            reports = run_physics_grounding(
                project,
                searcher=fake_searcher,
                max_attempts=1,
            )

            self.assertEqual(len(reports), 1)
            self.assertTrue(reports[0].is_complete)
            text = reports[0].report_path.read_text(encoding="utf-8")
            self.assertIn("Grounding status: complete", text)
            self.assertNotIn("ERROR:", text)
            self.assertNotIn("error:", text.lower())
            self.assertIn("Search unavailable", text)
            self.assertIn("Real.sqrt", text)
            self.assertIn("Electromagnetism.ElectricField", text)

            doctor = run_blueprint_doctor(project)
            self.assertIsNotNone(doctor)
            self.assertEqual(doctor.physics_grounding_problems, [])

    def test_leanexplore_search_retries_transient_failures(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            src = project / "blueprint" / "src"
            chapters = src / "chapters"
            chapters.mkdir(parents=True)
            (src / "content.tex").write_text(
                "\\input{chapters/P}\n",
                encoding="utf-8",
            )
            (chapters / "P.tex").write_text(
                "% archon:physics\n"
                "% archon:covers P.lean\n"
                "\\begin{theorem}[Electric field]\n"
                "\\label{thm:field}\\lean{P.field}\n"
                "An electric field statement.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            (project / "P.lean").write_text(
                "theorem target : True := by sorry\n",
                encoding="utf-8",
            )

            calls = 0

            def fake_searcher(query: str, packages: list[str], limit: int):
                nonlocal calls
                calls += 1
                if calls == 1:
                    raise RuntimeError("temporary unavailable")
                return [
                    GroundingCandidate(
                        name="Electromagnetism.ElectricField",
                        module="Physlib.Electromagnetism.Basic",
                    )
                ]

            reports = run_physics_grounding(
                project,
                searcher=fake_searcher,
                max_attempts=2,
                retry_delay=0,
            )

            self.assertGreaterEqual(calls, 2)
            self.assertEqual(len(reports), 1)
            self.assertTrue(reports[0].is_complete)
            self.assertEqual(run_blueprint_doctor(project).physics_grounding_problems, [])

    def test_local_backend_generates_grounding_without_api_key(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            chapters = project / "blueprint" / "src" / "chapters"
            chapters.mkdir(parents=True)
            (chapters / "P.tex").write_text(
                "% archon:physics\n"
                "% archon:covers P.lean\n"
                "\\begin{theorem}[Dimensionful electric field]\n"
                "\\lean{P.field}\n"
                "An electric field theorem.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            (project / "P.lean").write_text("theorem target : True := by sorry\n")
            seen: list[tuple[str, tuple[str, ...]]] = []

            def fake_local(query: str, packages: list[str], limit: int):
                seen.append((query, tuple(packages)))
                return [
                    GroundingCandidate(
                        name="Electromagnetism.ElectricField",
                        module="Physlib.Electromagnetism.Basic",
                    )
                ][:limit]

            with patch(
                "archon.commands.loop.physics_grounding._local_searcher",
                return_value=fake_local,
            ) as build_local:
                reports = run_physics_grounding(
                    project,
                    backend="local",
                    api_key="",
                )

            build_local.assert_called_once_with()
            self.assertEqual(len(reports), 1)
            self.assertTrue(reports[0].is_complete)
            text = reports[0].report_path.read_text(encoding="utf-8")
            self.assertIn("Search backend: local", text)
            self.assertNotIn("LEANEXPLORE_API_KEY is missing", text)
            self.assertIn("Electromagnetism.ElectricField", text)
            self.assertTrue(seen)
            self.assertTrue(all(packages == ("Mathlib", "Physlib") for _, packages in seen))

    def test_local_backend_missing_index_writes_actionable_report(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            (project / ".archon").mkdir()
            chapters = project / "blueprint" / "src" / "chapters"
            chapters.mkdir(parents=True)
            (chapters / "P.tex").write_text(
                "% archon:physics\n"
                "% archon:covers P.lean\n"
                "\\begin{theorem}[Electric field]\n"
                "\\lean{P.field}\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            (project / "P.lean").write_text("theorem target : True := by sorry\n")

            with patch(
                "archon.commands.loop.physics_grounding._local_searcher",
                side_effect=FileNotFoundError("Required local index file is missing"),
            ):
                reports = run_physics_grounding(
                    project,
                    backend="local",
                    api_key="",
                    max_attempts=1,
                )

            self.assertEqual(len(reports), 1)
            self.assertFalse(reports[0].is_complete)
            text = reports[0].report_path.read_text(encoding="utf-8")
            self.assertIn("Search backend: local", text)
            self.assertIn("LeanExplore local backend is unavailable", text)
            self.assertIn("lean-explore data fetch", text)

    def test_phase_forwards_prover_harness_local_backend(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            descriptor = SimpleNamespace(raw={"lean_explore_backend": "local"})
            ctx = SimpleNamespace(
                skip_now=set(),
                dry_run=False,
                current_stage="prover",
                project_path=project,
                harness_descriptor_for=lambda role: descriptor,
            )
            with patch(
                "archon.commands.loop.phases.physics_grounding.run_physics_grounding",
                return_value=[],
            ) as run_grounding:
                PhysicsGroundingPhase(ctx).run()

            run_grounding.assert_called_once_with(project, backend="local")

    def test_archive_preserves_loop_owned_physics_grounding_log(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            task_results = state / "task_results"
            iter_dir = state / "logs" / "iter-001"
            task_results.mkdir(parents=True)
            iter_dir.mkdir(parents=True)
            grounding = task_results / "physics-grounding-P.md"
            ordinary = task_results / "writer-P.md"
            grounding.write_text("grounding\n", encoding="utf-8")
            ordinary.write_text("ordinary\n", encoding="utf-8")

            archive_task_results(state, iter_dir)

            self.assertTrue(grounding.is_file())
            self.assertFalse(ordinary.exists())
            self.assertTrue((iter_dir / "task_results-archive" / "writer-P.md").is_file())


class ParallelProverDryRunTest(unittest.TestCase):
    def test_parallel_dry_run_does_not_require_iter_dir(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n"
                "## Current Objectives\n\n"
                "- Autoformalize `P.lean` from `blueprint/src/chapters/P.tex`.\n",
                encoding="utf-8",
            )
            task_results = state / "task_results"
            task_results.mkdir()
            (task_results / "old.md").write_text("old result\n", encoding="utf-8")
            _write_mode(state, "formalize", default_for="autoformalize")

            runner = ParallelProverRunner(
                project_name="proj",
                project_path=project,
                state_dir=state,
                stage="autoformalize",
                iter_dir=None,  # dry-run bootstrap leaves this unset
                iter_meta=state / "meta.json",
                iter_num=0,
                max_parallel=1,
                max_objectives=10,
                block_on_blocked_deps=False,
                verbose_logs=False,
                model="opus",
            )

            runner.run(dry_run=True)

    def test_parallel_dry_run_reports_physics_formalize_mode(self):
        with tempfile.TemporaryDirectory() as d:
            project = Path(d)
            state = project / ".archon"
            state.mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n"
                "## Current Objectives\n\n"
                "- Autoformalize `P.lean` from `blueprint/src/chapters/P.tex`.\n",
                encoding="utf-8",
            )
            _write_mode(state, "formalize", default_for="autoformalize")
            _write_mode(state, "physics-formalize")
            (project / "P.lean").write_text("theorem placeholder : True := trivial\n")
            chapter = project / "blueprint" / "src" / "chapters" / "P.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text("% archon:physics\n", encoding="utf-8")

            runner = ParallelProverRunner(
                project_name="proj",
                project_path=project,
                state_dir=state,
                stage="autoformalize",
                iter_dir=None,
                iter_meta=state / "meta.json",
                iter_num=0,
                max_parallel=1,
                max_objectives=10,
                block_on_blocked_deps=False,
                verbose_logs=False,
                model="opus",
            )

            with patch("archon.commands.loop.prover.runners.log.step") as step:
                runner.run(dry_run=True)

            rendered = "\n".join(str(call.args[0]) for call in step.call_args_list)
            self.assertIn("(mode: physics-formalize)", rendered)


if __name__ == "__main__":
    unittest.main()
