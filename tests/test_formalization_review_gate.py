import json
import tempfile
import unittest
from types import SimpleNamespace
from pathlib import Path

from archon.commands.loop.command import parse_from_phase
from archon.commands.loop.phases.review import (
    ReviewPhase,
    _load_domain_reviewer_blockers,
)
from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    enforce_progress_review_gate,
    load_gate_state,
)
from archon.state import read_stage


class FormalizationReviewGateTests(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory()
        self.project = Path(self.tempdir.name)
        self.state = self.project / ".archon"
        self.state.mkdir()
        self.target = self.project / "Problems" / "p.lean"
        self.target.parent.mkdir()
        self.target.write_text("theorem p : True := by sorry\n", encoding="utf-8")
        self.progress = self.state / "PROGRESS.md"
        self._write_progress("autoformalize")

    def tearDown(self):
        self.tempdir.cleanup()

    def _write_progress(self, stage):
        self.progress.write_text(
            "# Progress\n\n## Current Stage\n\n"
            + stage
            + "\n\n## Stages\n\n- autoformalize\n- prover\n\n"
            + "## Current Objectives\n\n- **`Problems/p.lean`** — target\n",
            encoding="utf-8",
        )

    def _set_chemistry_profile(self):
        (self.state / "config.json").write_text(
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

    @staticmethod
    def _passing_certificate(reason="review verdict"):
        checks = {
            name: {"status": "passed", "evidence": f"{name} evidence"}
            for name in (
                "source_faithfulness",
                "derivability",
                "abstraction_sufficiency",
                "countermodel_resistance",
            )
        }
        checks["uncertainty_propagation"] = {
            "status": "not_applicable",
            "evidence": "source has no uncertainty",
        }
        checks["branch_orientation"] = {
            "status": "not_applicable",
            "evidence": "target is unsigned",
        }
        return {
            "status": "passed",
            "reason": reason,
            "checks": checks,
            "bridge_obligations": [{
                "claim": "source assumptions entail p",
                "carrier": "target contract",
                "status": "covered",
                "evidence": "the carrier states the required relation",
            }],
        }

    def _review(
        self,
        iteration,
        status,
        reason="review verdict",
        formalization_review=None,
        blockers=(),
    ):
        session = self.state / "proof-journal" / "sessions" / f"session_{iteration}"
        session.mkdir(parents=True)
        if formalization_review is None:
            if status == "passed":
                formalization_review = self._passing_certificate(reason)
            else:
                formalization_review = {"status": status, "reason": reason}
        milestone = {
            "status": "blocked" if status == "failed" else "solved",
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "formalization_review": formalization_review,
        }
        (session / "milestones.jsonl").write_text(
            json.dumps(milestone) + "\n", encoding="utf-8"
        )
        return apply_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            progress_file=self.progress,
            session_dir=session,
            iter_num=iteration,
            reviewed_objectives=[self.target],
            max_iterations=3,
            blockers=blockers,
        )

    def test_failed_review_retries_then_exhausts_on_third_attempt(self):
        first = self._review(1, "failed")
        self.assertEqual(first.retry, ("Problems/p.lean",))
        self.assertEqual(read_stage(self.progress), "autoformalize")
        second = self._review(2, "failed")
        self.assertEqual(second.retry, ("Problems/p.lean",))
        third = self._review(3, "failed")
        self.assertEqual(third.exhausted, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        self.assertEqual(state["targets"]["Problems/p.lean"]["reviews"], 3)
        self.assertEqual(read_stage(self.progress), "prover")

    def test_review_count_stays_capped_after_exhaustion(self):
        self._review(1, "failed")
        self._review(2, "failed")
        self._review(3, "failed")
        result = self._review(4, "failed")
        state = load_gate_state(self.state)
        self.assertEqual(result.exhausted, ("Problems/p.lean",))
        self.assertEqual(state["targets"]["Problems/p.lean"]["reviews"], 3)

    def test_passed_target_is_eligible_for_prover(self):
        result = self._review(1, "passed")
        self.assertEqual(result.passed, ("Problems/p.lean",))
        kept, dropped = enforce_progress_review_gate(
            progress_file=self.progress,
            state_dir=self.state,
            project_path=self.project,
            stage="prover",
            enabled=True,
        )
        self.assertEqual(kept, [self.target])
        self.assertEqual(dropped, [])

    def test_chemistry_modes_survive_retry_pass_and_gate_rewrite(self):
        self._set_chemistry_profile()

        failed = self._review(1, "failed")
        self.assertEqual(failed.retry, ("Problems/p.lean",))
        self.assertIn(
            "[prover-mode: chemistry-formalize]",
            self.progress.read_text(encoding="utf-8"),
        )

        passed = self._review(2, "passed")
        self.assertEqual(passed.passed, ("Problems/p.lean",))
        self.assertEqual(read_stage(self.progress), "prover")
        self.assertIn(
            "[prover-mode: chemistry]",
            self.progress.read_text(encoding="utf-8"),
        )

        blocked = self.project / "Problems" / "blocked.lean"
        blocked.write_text("theorem blocked : True := by sorry\n", encoding="utf-8")
        self.progress.write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Stages\n\n- autoformalize\n- prover\n\n"
            "## Current Objectives\n\n"
            "- **`Problems/p.lean`** — passed target\n"
            "- **`Problems/blocked.lean`** — missing certificate\n",
            encoding="utf-8",
        )
        kept, dropped = enforce_progress_review_gate(
            progress_file=self.progress,
            state_dir=self.state,
            project_path=self.project,
            stage="prover",
            enabled=True,
        )
        self.assertEqual(kept, [self.target])
        self.assertEqual(dropped, [(blocked, "missing formalization Review certificate")])
        progress = self.progress.read_text(encoding="utf-8")
        self.assertIn("[prover-mode: chemistry]", progress)
        self.assertNotIn("[prover-mode: physics]", progress)

    def test_chemistry_must_fix_overrides_passing_milestone(self):
        self._set_chemistry_profile()
        reports = self.state / "task_results"
        reports.mkdir()
        report = reports / "chemistry-reviewer-p.md"
        report.write_text(
            "## Must-fix-this-iter\n"
            "- Problems/p.lean:p — current answer is assumed by the contract.\n"
            "\n"
            "## Overall verdict\n"
            "SOUND\n",
            encoding="utf-8",
        )
        blockers = _load_domain_reviewer_blockers(self.state, self.project)

        result = self._review(1, "passed", blockers=blockers)

        self.assertEqual(len(blockers), 1)
        self.assertEqual(blockers[0]["source"], "chemistry-reviewer")
        self.assertEqual(result.passed, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        self.assertEqual(read_stage(self.progress), "autoformalize")
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "retry")
        self.assertEqual(
            record["reason"],
            "global semantics Review blocker; no per-target pass certificate",
        )

    def test_legacy_string_target_replay_preserves_review_count(self):
        (self.state / "formalization-review-gate.json").write_text(
            json.dumps({
                "version": 2,
                "max_iterations": 3,
                "targets": {
                    "Problems/p.lean": {
                        "status": "retry",
                        "reviews": 2,
                        "last_review_iter": 2,
                        "certificate": {},
                    },
                },
            }),
            encoding="utf-8",
        )
        session = self.state / "proof-journal" / "sessions" / "session_2"
        session.mkdir(parents=True)
        milestone = {
            "status": "solved",
            "target": "Problems/p.lean",
            "formalization_review": self._passing_certificate(),
        }
        (session / "milestones.jsonl").write_text(
            json.dumps(milestone) + "\n", encoding="utf-8",
        )

        result = apply_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            progress_file=self.progress,
            session_dir=session,
            iter_num=2,
            reviewed_objectives=[self.target],
            max_iterations=3,
        )

        self.assertEqual(result.passed, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        record = state["targets"]["Problems/p.lean"]
        self.assertEqual(record["reviews"], 2)
        self.assertEqual(record["status"], "passed")
        self.assertEqual(len(record["certificate"]["milestones"]), 1)

    def test_bare_pass_without_structured_checks_fails_closed(self):
        result = self._review(
            1,
            "passed",
            formalization_review={"status": "passed", "reason": "looks faithful"},
        )

        self.assertEqual(result.retry, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        reason = state["targets"]["Problems/p.lean"]["reason"]
        self.assertIn("missing structured formalization Review checks", reason)

    def test_failed_derivability_check_overrides_top_level_pass(self):
        review = self._passing_certificate()
        review["checks"]["derivability"] = {
            "status": "failed",
            "evidence": "opaque tangent predicate has no eliminator",
        }

        result = self._review(1, "passed", formalization_review=review)

        self.assertEqual(result.retry, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        reason = state["targets"]["Problems/p.lean"]["reason"]
        self.assertIn("derivability", reason)

    def test_empty_bridge_inventory_fails_closed(self):
        review = self._passing_certificate()
        review["bridge_obligations"] = []

        result = self._review(1, "passed", formalization_review=review)

        self.assertEqual(result.retry, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        reason = state["targets"]["Problems/p.lean"]["reason"]
        self.assertIn("must contain a source-to-target bridge", reason)

    def test_blocked_bridge_obligation_overrides_top_level_pass(self):
        review = self._passing_certificate()
        review["bridge_obligations"][0]["status"] = "blocked"
        review["bridge_obligations"][0]["evidence"] = "missing asymptotic lemma"

        result = self._review(1, "passed", formalization_review=review)

        self.assertEqual(result.retry, ("Problems/p.lean",))
        state = load_gate_state(self.state)
        reason = state["targets"]["Problems/p.lean"]["reason"]
        self.assertIn("bridge obligation 1", reason)

    def test_old_gate_state_is_not_a_valid_certificate(self):
        (self.state / "formalization-review-gate.json").write_text(
            json.dumps({
                "version": 1,
                "targets": {"Problems/p.lean": {"status": "passed"}},
            }),
            encoding="utf-8",
        )

        self.assertIsNone(load_gate_state(self.state))

    def test_from_review_skips_all_pre_review_auxiliary_phases(self):
        self.assertEqual(
            parse_from_phase("review"),
            {
                "plan", "physics-grounding", "prover", "marker-sync",
                "blueprint-doctor", "axiom-sweep",
            },
        )

    def test_from_prover_skips_plan_and_grounding(self):
        self.assertEqual(
            parse_from_phase("prover"),
            {"plan", "physics-grounding"},
        )

    def test_review_agent_failure_does_not_consume_gate_attempt(self):
        meta = self.state / "logs" / "iter-003" / "meta.json"
        meta.parent.mkdir(parents=True)
        ctx = SimpleNamespace(
            options=SimpleNamespace(
                formalization_review_gate=True,
                no_review=False,
            ),
            current_stage="autoformalize",
            progress_file=self.progress,
            project_path=self.project,
            skip_now=set(),
            dry_run=False,
            iter_meta=meta,
        )
        phase = ReviewPhase(ctx)
        phase._invoke_review = lambda: False

        with self.assertRaisesRegex(RuntimeError, "refusing to apply"):
            phase.run()

        self.assertFalse((self.state / "formalization-review-gate.json").exists())
        self.assertEqual(json.loads(meta.read_text())["review"]["status"], "error")

    def test_prover_fails_closed_without_pass_certificate(self):
        self._write_progress("prover")
        kept, dropped = enforce_progress_review_gate(
            progress_file=self.progress,
            state_dir=self.state,
            project_path=self.project,
            stage="prover",
            enabled=True,
        )
        self.assertEqual(kept, [])
        self.assertEqual(len(dropped), 1)
        self.assertIn("no dispatch", self.progress.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
