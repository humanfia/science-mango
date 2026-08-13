from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.formalization_review_gate import STATE_VERSION
from archon.commands.loop.phases.review import ReviewPhase
from archon.commands.loop.review_preflight import (
    deterministic_review_prompt_prefix,
    run_parallel_review_preflight,
    write_deterministic_review_pack,
)


class ReviewPreflightTest(unittest.TestCase):
    def test_parallel_preflight_writes_stable_evidence(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            iter_dir = root / ".archon" / "logs" / "iter-003"
            a = root / "A.lean"
            b = root / "B.lean"
            a.write_text("theorem a : True := by trivial\n", encoding="utf-8")
            b.write_text("theorem b : True := by sorry\n", encoding="utf-8")

            def fake_run(command, **kwargs):
                failed = command[-1] == "B.lean"
                return SimpleNamespace(
                    returncode=1 if failed else 0,
                    stdout="" if not failed else "B.lean:1: error: failed",
                    stderr="",
                )

            with patch(
                "archon.commands.loop.review_preflight.subprocess.run",
                side_effect=fake_run,
            ):
                result = run_parallel_review_preflight(
                    project_path=root,
                    objectives=[a, b],
                    iter_dir=iter_dir,
                    iter_num=3,
                    jobs=2,
                )

            self.assertEqual(result["summary"], {
                "total": 2, "passed": 1, "failed": 1,
            })
            data = json.loads(
                (iter_dir / "review-preflight.json").read_text(encoding="utf-8")
            )
            self.assertEqual([row["file"] for row in data["targets"]], [
                "A.lean", "B.lean",
            ])
            self.assertEqual(data["targets"][0]["sorry_count"], 0)
            self.assertEqual(data["targets"][1]["sorry_count"], 1)
            self.assertIn(
                "B.lean:1: error",
                (iter_dir / "review-preflight.md").read_text(encoding="utf-8"),
            )

    def test_candidate_pack_and_prompt_are_bounded(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-004"
            task_dir = state / "task_results"
            chapter_dir = root / "blueprint" / "src" / "chapters"
            iter_dir.mkdir(parents=True)
            task_dir.mkdir(parents=True)
            chapter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by trivial\n", encoding="utf-8")
            (chapter_dir / "A.tex").write_text(
                "% archon:covers A.lean\n", encoding="utf-8"
            )
            (task_dir / "A.md").write_text("proof report\n", encoding="utf-8")
            preflight = {
                "targets": [{
                    "file": "A.lean",
                    "status": "passed",
                    "sorry_count": 0,
                    "duration_secs": 1.0,
                }]
            }
            pack = write_deterministic_review_pack(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=4,
                objectives=[target],
                preflight=preflight,
            )
            prompt = deterministic_review_prompt_prefix(
                preflight_path=iter_dir / "review-preflight.md",
                candidate_pack=pack,
                doctor_path=iter_dir / "blueprint-doctor.json",
            )

            pack_text = pack.read_text()
            self.assertIn("Exact review target count: 1", pack_text)
            self.assertLess(
                pack_text.index("### Blueprint excerpt"),
                pack_text.index("### Report excerpt"),
            )
            self.assertLess(
                pack_text.index("### Report excerpt"),
                pack_text.index("### Lean excerpt"),
            )
            self.assertIn("DETERMINISTIC BOUNDED REVIEW MODE", prompt)
            self.assertLess(
                prompt.index("project-local Review policy"),
                prompt.index(str(pack)),
            )
            self.assertIn("Do not run `lake env lean`", prompt)
            self.assertIn("Do not run leandag", prompt)


    def test_review_phase_enables_preflight_before_agent(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-005"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by trivial\n")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n1. **`A.lean`** — review.\n"
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "review_preflight_jobs": 2,
                }
            }))
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n")
            preflight_md = iter_dir / "review-preflight.md"
            preflight_md.write_text("# preflight\n")
            candidate_pack = iter_dir / "deterministic-review-candidates.md"
            candidate_pack.write_text("# candidates\n")
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=False, proof_review_gate=True,
                    no_review=False, max_parallel=2,
                ),
                current_stage="prover", progress_file=progress,
                project_path=root, state_dir=state, skip_now=set(),
                dry_run=False, iter_meta=meta, iter_dir=iter_dir, iter_num=5,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_review = lambda: False
            result = {
                "summary": {"total": 1, "passed": 1, "failed": 0},
                "jobs": 1, "duration_secs": 0.1, "md_path": preflight_md,
            }
            with (
                patch(
                    "archon.commands.loop.phases.review.run_parallel_review_preflight",
                    return_value=result,
                ) as preflight,
                patch(
                    "archon.commands.loop.phases.review.write_deterministic_review_pack",
                    return_value=candidate_pack,
                ),
            ):
                with self.assertRaises(RuntimeError):
                    phase.run()

            self.assertEqual(preflight.call_args.kwargs["objectives"], [target])
            data = json.loads(meta.read_text())
            self.assertTrue(data["review"]["deterministic"])
            self.assertEqual(data["review"]["preflightPassed"], 1)


    def test_proof_review_uses_parallel_target_path_when_enabled(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-006"
            session = state / "proof-journal" / "sessions" / "session_6"
            iter_dir.mkdir(parents=True)
            session.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by trivial\n")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n1. **`A.lean`** — review.\n"
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "review_preflight_jobs": 1,
                }
            }))
            (session / "milestones.jsonl").write_text(json.dumps({
                "target": {"file": "A.lean", "theorem": "a"},
                "status": "solved",
            }) + "\n")
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n")
            preflight_md = iter_dir / "review-preflight.md"
            preflight_md.write_text("# preflight\n")
            candidate_pack = iter_dir / "deterministic-review-candidates.md"
            candidate_pack.write_text("# candidates\n")
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=False,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=32,
                ),
                current_stage="prover", progress_file=progress,
                project_path=root, state_dir=state, skip_now=set(),
                dry_run=False, iter_meta=meta, iter_dir=iter_dir, iter_num=6,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            called = []
            phase._invoke_parallel_target_review = (
                lambda objectives, *, cfg: called.extend(objectives) or True
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            result = {
                "summary": {"total": 1, "passed": 1, "failed": 0},
                "jobs": 1, "duration_secs": 0.1, "md_path": preflight_md,
                "targets": [{
                    "file": "A.lean", "compiles": True, "sorry_count": 0,
                }],
            }
            with (
                patch(
                    "archon.commands.loop.phases.review.run_parallel_review_preflight",
                    return_value=result,
                ),
                patch(
                    "archon.commands.loop.phases.review.write_deterministic_review_pack",
                    return_value=candidate_pack,
                ),
                patch("archon.commands.loop.phases.review.commit_phase"),
            ):
                phase.run()

            self.assertEqual(called, [target])
            gate = json.loads((state / "proof-review-gate.json").read_text())
            self.assertEqual(gate["targets"]["A.lean"]["status"], "solved")

    def test_formalization_review_uses_parallel_target_path_when_enabled(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-008"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nautoformalize\n\n"
                "## Current Objectives\n\n1. **`A.lean`** — review.\n"
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_formalization_review": True,
                    "review_preflight_jobs": 1,
                }
            }))
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n")
            preflight_md = iter_dir / "review-preflight.md"
            preflight_md.write_text("# preflight\n")
            candidate_pack = iter_dir / "deterministic-review-candidates.md"
            candidate_pack.write_text("# candidates\n")
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=True,
                    formalization_review_max_iterations=3,
                    proof_review_gate=False,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=8,
                ),
                current_stage="autoformalize",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=meta,
                iter_dir=iter_dir,
                iter_num=8,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            called: list[Path] = []
            phase._invoke_parallel_formalization_review = (
                lambda objectives, *, cfg: called.extend(objectives) or True
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            phase._run_physics_doctor_gate = lambda: ([], False)
            result = {
                "summary": {"total": 1, "passed": 1, "failed": 0},
                "jobs": 1,
                "duration_secs": 0.1,
                "md_path": preflight_md,
                "targets": [{
                    "file": "A.lean", "compiles": True, "sorry_count": 1,
                }],
            }
            gate_result = SimpleNamespace(
                passed=("A.lean",), retry=(), exhausted=(), reviewed=("A.lean",),
            )
            with (
                patch(
                    "archon.commands.loop.phases.review.run_parallel_review_preflight",
                    return_value=result,
                ),
                patch(
                    "archon.commands.loop.phases.review.write_deterministic_review_pack",
                    return_value=candidate_pack,
                ),
                patch(
                    "archon.commands.loop.phases.review.apply_formalization_review",
                    return_value=gate_result,
                ) as apply_gate,
                patch("archon.commands.loop.phases.review.check_mandatory_dispatched"),
                patch("archon.commands.loop.phases.review.commit_phase"),
            ):
                phase.run()

            self.assertEqual(called, [target])
            self.assertEqual(
                apply_gate.call_args.kwargs["reviewed_objectives"], [target],
            )


    def test_review_phase_redraft_route_revokes_formalization_certificate(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-007"
            session = state / "proof-journal" / "sessions" / "session_7"
            iter_dir.mkdir(parents=True)
            session.mkdir(parents=True)
            target = root / "Problems" / "A.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Stages\n\n- autoformalize\n- prover\n\n"
                "## Current Objectives\n\n1. **`Problems/A.lean`** — prove.\n",
                encoding="utf-8",
            )
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": STATE_VERSION,
                    "max_iterations": 3,
                    "targets": {
                        "Problems/A.lean": {
                            "status": "passed",
                            "reviews": 1,
                            "certificate": {"old": "passing certificate"},
                        },
                    },
                }),
                encoding="utf-8",
            )
            (session / "milestones.jsonl").write_text(
                json.dumps({
                    "target": {"file": "Problems/A.lean", "theorem": "a"},
                    "status": "blocked",
                    "proof_review": {
                        "schema_version": 1,
                        "route": "needs_redraft",
                        "reason": "opaque relation admits a countermodel",
                        "evidence": "all hypotheses hold while the goal is false",
                        "redraft_kind": "underdetermined_contract",
                    },
                }) + "\n",
                encoding="utf-8",
            )
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n", encoding="utf-8")
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=True,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=1,
                ),
                current_stage="prover",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=meta,
                iter_dir=iter_dir,
                iter_num=7,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_review = lambda: True

            with (
                patch("archon.commands.loop.phases.review.commit_phase"),
                patch(
                    "archon.commands.loop.phases.review.check_mandatory_dispatched"
                ),
            ):
                phase.run()

            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            formal_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["Problems/A.lean"]["status"],
                             "needs_redraft")
            self.assertEqual(formal_gate["targets"]["Problems/A.lean"]["status"],
                             "retry")
            self.assertEqual(formal_gate["targets"]["Problems/A.lean"]["certificate"],
                             {})
            self.assertIn("autoformalize", progress.read_text(encoding="utf-8"))
            self.assertIn("physics-formalize", progress.read_text(encoding="utf-8"))
            metadata = json.loads(meta.read_text(encoding="utf-8"))
            self.assertEqual(metadata["review"]["proofGateNeedsRedraft"], 1)
            self.assertEqual(metadata["review"]["proofGateRedraftsReopened"], 1)


if __name__ == "__main__":
    unittest.main()
