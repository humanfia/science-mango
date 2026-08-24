from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.formalization_review_gate import STATE_VERSION
from archon.commands.loop.phases.plan import PlanPhase
from archon.state import parse_objective_files, read_stage


class _FakePlanAgent:
    def __init__(self, progress_file: Path, captured: list[str]) -> None:
        self.progress_file = progress_file
        self.captured = captured

    def run(self, prompt: str, **kwargs) -> None:
        self.captured.append(prompt)
        text = self.progress_file.read_text(encoding="utf-8")
        text = text.replace("A.lean", "ModelTriedToReplace.lean")
        self.progress_file.write_text(text, encoding="utf-8")


class DeterministicPlanPhaseTest(unittest.TestCase):
    def test_bypasses_full_prompt_and_restores_exact_objectives(self):
        with tempfile.TemporaryDirectory() as td:
            project = Path(td)
            state = project / ".archon"
            iter_dir = state / "logs" / "iter-001"
            iter_meta = iter_dir / "meta.json"
            chapters = project / "blueprint" / "src" / "chapters"
            iter_dir.mkdir(parents=True)
            chapters.mkdir(parents=True)
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Stages\n\n- prover\n\n"
                "## Current Objectives\n\n- `Old.lean`\n\n",
                encoding="utf-8",
            )
            for name in ("A", "B", "C"):
                (project / f"{name}.lean").write_text(
                    f"theorem {name.lower()} : True := by sorry\n", encoding="utf-8"
                )
                (chapters / f"{name}.tex").write_text(
                    f"% archon:physics\n% archon:covers {name}.lean\n"
                    f"\\begin{{theorem}}[{name}] prove True \\end{{theorem}}\n",
                    encoding="utf-8",
                )
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "targets": {
                        f"{name}.lean": {"status": "passed"}
                        for name in ("A", "B", "C")
                    },
                }),
                encoding="utf-8",
            )
            (state / "config.json").write_text(
                json.dumps({"loop": {"deterministic_plan": True}}),
                encoding="utf-8",
            )
            iter_meta.write_text("{}\n", encoding="utf-8")

            options = SimpleNamespace(
                max_parallel=1,
                max_objectives=3,
                formalization_review_gate=True,
                proof_review_gate=True,
                proof_review_max_iterations=3,
                compress_plan_review_inputs=False,
                prompt_compression_target_chars=40000,
                prompt_compression_section_chars=6000,
                multilane_preview=False,
                multilane_execute=False,
                debug_feedback=False,
            )
            prompts: list[str] = []
            ctx = SimpleNamespace(
                options=options,
                skip_now=set(),
                current_stage="prover",
                project_path=project,
                project_name="proj",
                state_dir=state,
                progress_file=progress,
                log_dir=state / "logs",
                iter_dir=iter_dir,
                iter_meta=iter_meta,
                iter_num=1,
                dry_run=False,
                verbose_logs=False,
                resume_phase=None,
                force_stage=lambda: None,
                make_agent=lambda role: _FakePlanAgent(progress, prompts),
            )

            with (
                patch(
                    "archon.commands.loop.phases.plan.build_plan_prompt",
                    side_effect=AssertionError("full frontier prompt must not run"),
                ),
                patch("archon.commands.loop.phases.plan.commit_phase"),
                patch("archon.commands.loop.phases.plan.check_mandatory_dispatched"),
                patch("archon.commands.loop.phases.plan.persist_session_id"),
            ):
                result = PlanPhase(ctx).run()

            self.assertFalse(result.completed)
            self.assertEqual(
                parse_objective_files(progress, project),
                [project / "A.lean", project / "B.lean", project / "C.lean"],
            )
            self.assertEqual(read_stage(progress), "prover")
            self.assertEqual(len(prompts), 1)
            self.assertIn("DETERMINISTIC BOUNDED PLAN MODE", prompts[0])
            self.assertIn("do not invoke leandag/frontier scans", prompts[0])
            meta = json.loads(iter_meta.read_text(encoding="utf-8"))
            self.assertTrue(meta["plan"]["deterministic"])
            self.assertEqual(
                meta["plan"]["deterministicCandidates"],
                ["A.lean", "B.lean", "C.lean"],
            )


    def test_autoformalize_retry_is_controller_owned_with_readonly_blueprint(self):
        with tempfile.TemporaryDirectory() as td:
            project = Path(td)
            state = project / ".archon"
            iter_dir = state / "logs" / "iter-002"
            iter_meta = iter_dir / "meta.json"
            chapters = project / "blueprint" / "src" / "chapters"
            iter_dir.mkdir(parents=True)
            chapters.mkdir(parents=True)
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nautoformalize\n\n"
                "## Stages\n\n- autoformalize\n- prover\n\n"
                "## Current Objectives\n\n- `PlannerSkip.lean`\n\n",
                encoding="utf-8",
            )
            target = project / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            chapter = chapters / "A.tex"
            chapter.write_text(
                "% archon:chemistry\n% archon:covers A.lean\n"
                "Immutable source strategy.\n",
                encoding="utf-8",
            )
            chapter.chmod(0o400)
            original_chapter = chapter.read_bytes()
            original_mode = chapter.stat().st_mode & 0o777
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "max_iterations": 3,
                    "targets": {
                        "A.lean": {
                            "status": "retry",
                            "reviews": 1,
                            "last_review_iter": 1,
                            "reason": "source bridge missing",
                        },
                    },
                }),
                encoding="utf-8",
            )
            (state / "config.json").write_text(
                json.dumps({
                    "loop": {
                        "deterministic_plan": True,
                        "domain_profile": {
                            "name": "chemistry-native",
                            "enforce_classical_physics_modeling": False,
                        },
                    }
                }),
                encoding="utf-8",
            )
            iter_meta.write_text("{}\n", encoding="utf-8")
            options = SimpleNamespace(
                max_parallel=1,
                max_objectives=1,
                formalization_review_gate=True,
                proof_review_gate=True,
                proof_review_max_iterations=3,
                compress_plan_review_inputs=False,
                prompt_compression_target_chars=40000,
                prompt_compression_section_chars=6000,
                multilane_preview=False,
                multilane_execute=False,
                debug_feedback=False,
            )
            ctx = SimpleNamespace(
                options=options,
                skip_now=set(),
                current_stage="autoformalize",
                project_path=project,
                project_name="proj",
                state_dir=state,
                progress_file=progress,
                log_dir=state / "logs",
                iter_dir=iter_dir,
                iter_meta=iter_meta,
                iter_num=2,
                dry_run=False,
                verbose_logs=False,
                resume_phase=None,
                force_stage=lambda: None,
                make_agent=lambda _role: self.fail(
                    "controller retry frontier must not spawn a model planner"
                ),
            )

            with (
                patch(
                    "archon.commands.loop.phases.plan.build_plan_prompt",
                    side_effect=AssertionError(
                        "full frontier prompt must not run for a retry"
                    ),
                ),
                patch("archon.commands.loop.phases.plan.commit_phase"),
                patch("archon.commands.loop.phases.plan.check_mandatory_dispatched"),
                patch("archon.commands.loop.phases.plan.persist_session_id"),
            ):
                result = PlanPhase(ctx).run()

            self.assertFalse(result.completed)
            self.assertEqual(
                parse_objective_files(progress, project), [target],
            )
            self.assertEqual(read_stage(progress), "autoformalize")
            self.assertEqual(chapter.read_bytes(), original_chapter)
            self.assertEqual(chapter.stat().st_mode & 0o777, original_mode)
            meta = json.loads(iter_meta.read_text(encoding="utf-8"))
            self.assertEqual(
                meta["plan"]["deterministicCandidates"], ["A.lean"],
            )
            sidecar = state / "iter" / "iter-002" / "objectives.md"
            self.assertIn(
                "mandatory formalization-Review retry",
                sidecar.read_text(encoding="utf-8"),
            )



if __name__ == "__main__":
    unittest.main()
