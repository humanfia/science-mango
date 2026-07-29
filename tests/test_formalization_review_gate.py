import json
import tempfile
import unittest
from types import SimpleNamespace
from pathlib import Path

from archon.commands.loop.command import parse_from_phase
from archon.commands.loop.phases.review import ReviewPhase
from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    apply_target_formalization_review,
    enforce_progress_review_gate,
    load_gate_state,
)
from archon.commands.loop.foundation_build_gate import (
    foundation_build_is_dispatchable,
    foundation_build_trigger,
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

    @classmethod
    def _foundation_certificate(cls):
        review = cls._passing_certificate(
            "faithful contract needs reusable local bridge lemmas"
        )
        review.update({
            "schema_version": 2,
            "status": "failed",
            "route": "foundation_build",
            "redraft_kind": "missing_foundational_bridge",
            "foundation_request": {
                "root_claim": "derive the target bridge from the base identity",
                "root_nodes": ["target_bridge"],
                "nodes": [
                    {
                        "id": "base_identity",
                        "claim": "the base identity holds",
                        "lean_goal": "theorem baseIdentity : True",
                        "depends_on": [],
                        "evidence": "the source derivation uses this identity first",
                    },
                    {
                        "id": "target_bridge",
                        "claim": "the reusable target bridge follows",
                        "lean_goal": "theorem targetBridge : True",
                        "depends_on": ["base_identity"],
                        "evidence": "this is the blocked source-to-Lean bridge",
                    },
                ],
            },
        })
        review["checks"]["derivability"] = {
            "status": "failed",
            "evidence": "the local library lacks targetBridge",
        }
        review["bridge_obligations"][0].update({
            "status": "blocked",
            "evidence": "targetBridge is not available in the local library",
        })
        return review

    def _review(
        self,
        iteration,
        status,
        reason="review verdict",
        formalization_review=None,
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

    def test_target_review_can_route_last_turn_to_foundation_dag(self):
        review = self._foundation_certificate()
        milestone = {
            "status": "blocked",
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "formalization_review": review,
        }

        update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=milestone,
            iter_num=1,
            max_iterations=1,
            event_id="formalization:event:1",
        )

        self.assertEqual(update.status, "retry")
        self.assertEqual(update.reviews, 1)
        self.assertEqual(update.route, "foundation_build")
        self.assertEqual(update.redraft_kind, "missing_foundational_bridge")
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["route"], "foundation_build")
        request = record["certificate"]["foundation_request"]
        self.assertEqual(
            request["build_order"], ["base_identity", "target_bridge"]
        )
        trigger = foundation_build_trigger(
            state_dir=self.state,
            target_rel="Problems/p.lean",
        )
        self.assertEqual(trigger["source_review_kind"], "formalization")
        self.assertEqual(
            trigger["source_review_event_id"], "formalization:event:1"
        )
        self.assertTrue(foundation_build_is_dispatchable(
            state_dir=self.state,
            project_path=self.project,
            target_rel="Problems/p.lean",
            max_iterations=2,
        ))

    def test_batch_review_binds_foundation_route_to_batch_event(self):
        result = self._review(
            1,
            "failed",
            formalization_review=self._foundation_certificate(),
        )

        self.assertEqual(result.retry, ("Problems/p.lean",))
        trigger = foundation_build_trigger(
            state_dir=self.state,
            target_rel="Problems/p.lean",
        )
        self.assertEqual(
            trigger["source_review_event_id"],
            "batch:1:Problems/p.lean:formalization",
        )
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(
            record["review_events"][-1]["route"], "foundation_build"
        )

    def test_invalid_foundation_dag_downgrades_to_redraft(self):
        review = self._foundation_certificate()
        review["foundation_request"]["nodes"][0]["depends_on"] = [
            "target_bridge"
        ]
        milestone = {
            "status": "blocked",
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "formalization_review": review,
        }

        update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=milestone,
            iter_num=1,
            max_iterations=3,
            event_id="formalization:event:cycle",
        )

        self.assertEqual(update.status, "retry")
        self.assertEqual(update.route, "redraft")
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["route"], "redraft")
        self.assertIn("cycle", record["certificate"]["routing_error"])
        self.assertIsNone(foundation_build_trigger(
            state_dir=self.state,
            target_rel="Problems/p.lean",
        ))

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
