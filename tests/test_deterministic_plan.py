from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.deterministic_plan import (
    deterministic_plan_prompt_prefix,
    fast_open_sorry_count,
    select_deterministic_candidates,
    write_deterministic_candidate_pack,
    write_deterministic_objectives,
)
from archon.commands.loop.formalization_review_gate import STATE_VERSION
from archon.state import parse_objective_files, read_stage


class DeterministicPlanSelectionTest(unittest.TestCase):
    def _project(self, root: Path) -> tuple[Path, Path]:
        state = root / ".archon"
        state.mkdir()
        (state / "PROGRESS.md").write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Stages\n\n- prover\n\n"
            "## Current Objectives\n\n- `Old.lean`\n\n",
            encoding="utf-8",
        )
        chapters = root / "blueprint" / "src" / "chapters"
        chapters.mkdir(parents=True)
        return state, chapters

    @staticmethod
    def _target(root: Path, chapters: Path, rel: str, body: str) -> None:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        slug = rel.removesuffix(".lean").replace("/", "_")
        (chapters / f"{slug}.tex").write_text(
            "% archon:physics\n"
            f"% archon:covers {rel}\n"
            "\\begin{theorem}[Target] proof strategy \\end{theorem}\n",
            encoding="utf-8",
        )

    def test_retry_first_and_gate_statuses_are_enforced(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, chapters = self._project(root)
            files = {
                # Review retries remain eligible even after `sorry` was
                # replaced by a term that does not elaborate.
                "ZRetry.lean": "theorem z : True := by exact missingName\n",
                "BNew.lean": "theorem b : True := by sorry\n",
                "CSolved.lean": "theorem c : True := by sorry\n",
                "DFailedFormal.lean": "theorem d : True := by sorry\n",
                "EExhausted.lean": "theorem e : True := by sorry\n",
                "FNoop.lean": "theorem f : True := by trivial\n",
                "GRedraft.lean": "theorem g : True := by sorry\n",
                "HInfrastructure.lean": "theorem h : True := by sorry\n",
            }
            for rel, body in files.items():
                self._target(root, chapters, rel, body)
            formal = {
                "version": STATE_VERSION,
                "targets": {
                    rel: {"status": "failed" if rel == "DFailedFormal.lean" else "passed"}
                    for rel in files
                }
            }
            (state / "formalization-review-gate.json").write_text(
                json.dumps(formal), encoding="utf-8"
            )
            proof = {
                "targets": {
                    "ZRetry.lean": {"status": "retry", "attempts": 2, "reason": "review failed"},
                    "CSolved.lean": {"status": "solved", "attempts": 1},
                    "EExhausted.lean": {"status": "proof_review_exhausted", "attempts": 3},
                    "GRedraft.lean": {"status": "needs_redraft", "attempts": 1},
                    "HInfrastructure.lean": {
                        "status": "blocked_infrastructure", "attempts": 1,
                    },
                }
            }
            (state / "proof-review-gate.json").write_text(
                json.dumps(proof), encoding="utf-8"
            )

            candidates = select_deterministic_candidates(
                project_path=root,
                state_dir=state,
                stage="prover",
                limit=10,
                formalization_gate_enabled=True,
                proof_gate_enabled=True,
            )

            self.assertEqual(
                [item.relative_path for item in candidates],
                ["ZRetry.lean", "BNew.lean"],
            )
            self.assertTrue(all(item.physics for item in candidates))
            self.assertEqual(candidates[0].proof_attempts, 2)
            self.assertEqual(candidates[0].sorry_count, 0)

    def test_limit_and_non_prover_stage(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, chapters = self._project(root)
            for rel in ("A.lean", "B.lean", "C.lean"):
                self._target(root, chapters, rel, "theorem t : True := by sorry\n")
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "targets": {
                        rel: {"status": "passed"}
                        for rel in ("A.lean", "B.lean", "C.lean")
                    },
                }),
                encoding="utf-8",
            )
            selected = select_deterministic_candidates(
                project_path=root, state_dir=state, stage="prover", limit=2,
                formalization_gate_enabled=True, proof_gate_enabled=False,
            )
            skipped = select_deterministic_candidates(
                project_path=root, state_dir=state, stage="autoformalize", limit=2,
                formalization_gate_enabled=True, proof_gate_enabled=False,
            )
            self.assertEqual([item.relative_path for item in selected], ["A.lean", "B.lean"])
            self.assertEqual(skipped, [])

    def test_autoformalize_selects_only_controller_retry(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, chapters = self._project(root)
            (state / "config.json").write_text(
                json.dumps({
                    "loop": {
                        "domain_profile": {
                            "name": "chemistry-native",
                            "enforce_classical_physics_modeling": False,
                        }
                    }
                }),
                encoding="utf-8",
            )
            self._target(
                root, chapters, "Retry.lean",
                "theorem retry : True := by trivial\n",
            )
            self._target(
                root, chapters, "Passed.lean",
                "theorem passed : True := by sorry\n",
            )
            self._target(
                root, chapters, "Exhausted.lean",
                "theorem exhausted : True := by sorry\n",
            )
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "max_iterations": 3,
                    "targets": {
                        "Retry.lean": {
                            "status": "retry",
                            "reviews": 1,
                            "last_review_iter": 1,
                            "reason": "missing source bridge",
                        },
                        "Passed.lean": {"status": "passed"},
                        "Exhausted.lean": {
                            "status": "review_exhausted",
                        },
                    },
                }),
                encoding="utf-8",
            )

            candidates = select_deterministic_candidates(
                project_path=root,
                state_dir=state,
                stage="autoformalize",
                limit=3,
                formalization_gate_enabled=True,
                proof_gate_enabled=True,
            )

            self.assertEqual(
                [item.relative_path for item in candidates], ["Retry.lean"],
            )
            self.assertEqual(candidates[0].sorry_count, 0)
            self.assertEqual(candidates[0].proof_status, "formalization_retry")
            self.assertEqual(candidates[0].proof_attempts, 1)
            self.assertEqual(candidates[0].prover_mode, "chemistry-formalize")
            self.assertIn("blueprint as immutable", candidates[0].objective_task)

    def test_chemistry_profile_keeps_chemistry_mode_in_deterministic_prover(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, chapters = self._project(root)
            (state / "config.json").write_text(
                json.dumps({
                    "loop": {
                        "domain_profile": {
                            "name": "chemistry",
                            "enforce_classical_physics_modeling": False,
                        }
                    }
                }),
                encoding="utf-8",
            )
            self._target(root, chapters, "Chem.lean", "theorem c : True := by sorry\n")
            (chapters / "Chem.tex").write_text(
                "% archon:chemistry\n% archon:covers Chem.lean\n",
                encoding="utf-8",
            )
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "targets": {"Chem.lean": {"status": "passed"}},
                }),
                encoding="utf-8",
            )

            candidates = select_deterministic_candidates(
                project_path=root,
                state_dir=state,
                stage="prover",
                limit=1,
                formalization_gate_enabled=True,
                proof_gate_enabled=False,
            )
            self.assertEqual(len(candidates), 1)
            self.assertEqual(candidates[0].prover_mode, "chemistry")

            write_deterministic_objectives(
                progress_file=state / "PROGRESS.md",
                state_dir=state,
                iter_num=2,
                candidates=candidates,
            )
            self.assertIn(
                "[prover-mode: chemistry]",
                (state / "PROGRESS.md").read_text(encoding="utf-8"),
            )

    def test_fast_sorry_count_ignores_comments_and_strings(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "T.lean"
            path.write_text(
                '-- "sorry"\n/- sorry /- admit -/ -/\n'
                'def message := "sorry"\n'
                "theorem live : True := by sorry\n",
                encoding="utf-8",
            )
            self.assertEqual(fast_open_sorry_count(path), 1)

    def test_writes_exact_progress_sidecar_and_bounded_pack(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, chapters = self._project(root)
            self._target(root, chapters, "A.lean", "theorem a : True := by sorry\n")
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "targets": {"A.lean": {"status": "passed"}},
                }),
                encoding="utf-8",
            )
            candidates = select_deterministic_candidates(
                project_path=root, state_dir=state, stage="prover", limit=1,
                formalization_gate_enabled=True, proof_gate_enabled=True,
            )
            write_deterministic_objectives(
                progress_file=state / "PROGRESS.md",
                state_dir=state,
                iter_num=4,
                candidates=candidates,
            )
            iter_dir = state / "logs" / "iter-004"
            pack = write_deterministic_candidate_pack(
                project_path=root, iter_dir=iter_dir, iter_num=4,
                candidates=candidates,
            )
            prompt = deterministic_plan_prompt_prefix(
                candidate_pack=pack,
                plan_input_pack=iter_dir / "plan-input-pack.md",
                state_dir=state,
                iter_num=4,
            )

            self.assertEqual(parse_objective_files(state / "PROGRESS.md", root), [root / "A.lean"])
            self.assertEqual(read_stage(state / "PROGRESS.md"), "prover")
            self.assertTrue((state / "iter" / "iter-004" / "objectives.md").is_file())
            self.assertIn("theorem a", pack.read_text(encoding="utf-8"))
            self.assertIn("Do not run repository-wide", prompt)
            self.assertIn("Do not replace, reorder, add, or remove", prompt)


if __name__ == "__main__":
    unittest.main()
