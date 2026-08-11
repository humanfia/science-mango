from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    load_gate_state,
    reopen_formalization_targets,
)
from archon.commands.loop.proof_review_gate import (
    apply_proof_review,
    filter_objectives_for_proof_review_gate,
    load_proof_review_state,
    reopen_exhausted_proof_review_targets,
)
from archon.state import parse_objective_files, read_stage


class ProofReviewRoutingGateTest(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory()
        self.project = Path(self.tempdir.name)
        self.state = self.project / ".archon"
        self.state.mkdir()
        self.target = self.project / "Problems" / "p.lean"
        self.target.parent.mkdir()
        self.target.write_text("theorem p : True := by sorry\n", encoding="utf-8")
        self.progress = self.state / "PROGRESS.md"
        self._write_progress("prover")

    def tearDown(self):
        self.tempdir.cleanup()

    def _write_progress(self, stage: str) -> None:
        self.progress.write_text(
            "# Progress\n\n## Current Stage\n\n"
            + stage
            + "\n\n## Stages\n\n- autoformalize\n- prover\n\n"
            + "## Current Objectives\n\n- **`Problems/p.lean`** — target\n",
            encoding="utf-8",
        )

    def _proof_session(
        self,
        iteration: int,
        *,
        route: str,
        status: str,
        redraft_kind: str = "not_applicable",
    ) -> Path:
        session = self.state / "proof-journal" / "sessions" / f"session_{iteration}"
        session.mkdir(parents=True)
        row = {
            "status": status,
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "proof_review": {
                "schema_version": 1,
                "route": route,
                "reason": f"classified as {route}",
                "evidence": "goal and theorem contract audited",
                "redraft_kind": redraft_kind,
            },
        }
        (session / "milestones.jsonl").write_text(
            json.dumps(row) + "\n", encoding="utf-8",
        )
        return session

    def _apply_proof(self, iteration: int, session: Path, maximum: int = 3):
        return apply_proof_review(
            state_dir=self.state,
            project_path=self.project,
            session_dir=session,
            iter_num=iteration,
            reviewed_objectives=[self.target],
            max_iterations=maximum,
        )

    @staticmethod
    def _passing_formalization_review() -> dict:
        checks = {
            name: {"status": "passed", "evidence": f"{name} checked"}
            for name in (
                "source_faithfulness",
                "derivability",
                "abstraction_sufficiency",
                "countermodel_resistance",
            )
        }
        checks["uncertainty_propagation"] = {
            "status": "not_applicable", "evidence": "no uncertainty",
        }
        checks["branch_orientation"] = {
            "status": "not_applicable", "evidence": "no signed branch",
        }
        return {
            "status": "passed",
            "reason": "faithful and derivable",
            "checks": checks,
            "bridge_obligations": [{
                "claim": "source claim",
                "carrier": "Lean contract",
                "status": "covered",
                "evidence": "carrier supplies the bridge",
            }],
        }

    def _apply_formalization(self, iteration: int):
        session = self.state / "proof-journal" / "sessions" / f"session_{iteration}"
        session.mkdir(parents=True, exist_ok=True)
        row = {
            "status": "solved",
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "formalization_review": self._passing_formalization_review(),
        }
        (session / "milestones.jsonl").write_text(
            json.dumps(row) + "\n", encoding="utf-8",
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

    def test_modeling_failure_routes_to_redraft_even_at_attempt_limit(self):
        session = self._proof_session(
            1,
            route="needs_redraft",
            status="blocked",
            redraft_kind="underdetermined_contract",
        )
        result = self._apply_proof(1, session, maximum=1)

        self.assertEqual(result.needs_redraft, ("Problems/p.lean",))
        self.assertEqual(result.exhausted, ())
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "needs_redraft")
        self.assertEqual(record["redraft_kind"], "underdetermined_contract")
        kept, dropped = filter_objectives_for_proof_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            enabled=True,
        )
        self.assertEqual(kept, [])
        self.assertEqual(dropped, [(self.target, "needs_redraft")])

    def test_tactic_failure_retries_then_exhausts(self):
        first = self._proof_session(1, route="retry_proof", status="partial")
        self.assertEqual(self._apply_proof(1, first, maximum=2).retry,
                         ("Problems/p.lean",))
        second = self._proof_session(2, route="retry_proof", status="partial")
        result = self._apply_proof(2, second, maximum=2)
        self.assertEqual(result.exhausted, ("Problems/p.lean",))
        self.assertEqual(result.needs_redraft, ())

    def test_explicit_budget_extension_reopens_exhausted_target(self):
        session = self._proof_session(1, route="retry_proof", status="partial")
        self.assertEqual(
            self._apply_proof(1, session, maximum=1).exhausted,
            ("Problems/p.lean",),
        )

        reopened = reopen_exhausted_proof_review_targets(
            state_dir=self.state,
            targets=["Problems/p.lean"],
            iter_num=2,
            max_iterations=4,
            reason="user authorized another reviewed proof attempt",
        )

        self.assertEqual(reopened, ("Problems/p.lean",))
        state = load_proof_review_state(self.state)
        record = state["targets"]["Problems/p.lean"]
        self.assertEqual(state["max_iterations"], 4)
        self.assertEqual(record["status"], "retry")
        self.assertEqual(record["attempts"], 1)
        self.assertEqual(
            record["history"][-1]["event"],
            "proof_review_budget_extended",
        )
        kept, dropped = filter_objectives_for_proof_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            enabled=True,
        )
        self.assertEqual(kept, [self.target])
        self.assertEqual(dropped, [])

    def test_budget_extension_must_exceed_consumed_attempts(self):
        session = self._proof_session(1, route="retry_proof", status="partial")
        self._apply_proof(1, session, maximum=1)

        with self.assertRaisesRegex(ValueError, "must exceed"):
            reopen_exhausted_proof_review_targets(
                state_dir=self.state,
                targets=["Problems/p.lean"],
                iter_num=2,
                max_iterations=1,
                reason="insufficient extension",
            )

        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "proof_review_exhausted")

    def test_infrastructure_blocker_is_quarantined_without_retry(self):
        session = self._proof_session(
            1, route="blocked_infrastructure", status="blocked",
        )
        result = self._apply_proof(1, session)
        self.assertEqual(
            result.blocked_infrastructure, ("Problems/p.lean",),
        )
        self.assertEqual(result.retry, ())
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "blocked_infrastructure")

    def test_redraft_revokes_certificate_then_fresh_pass_resets_proof_budget(self):
        self._write_progress("autoformalize")
        initial = self._apply_formalization(1)
        self.assertEqual(initial.passed, ("Problems/p.lean",))
        old_certificate = load_gate_state(self.state)["targets"]["Problems/p.lean"][
            "certificate"
        ]

        proof_session = self._proof_session(
            2,
            route="needs_redraft",
            status="blocked",
            redraft_kind="missing_foundational_bridge",
        )
        proof_result = self._apply_proof(2, proof_session)
        proof_record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        reopened = reopen_formalization_targets(
            state_dir=self.state,
            project_path=self.project,
            progress_file=self.progress,
            redrafts={"Problems/p.lean": proof_record},
            iter_num=2,
            max_iterations=3,
        )

        self.assertEqual(reopened, ("Problems/p.lean",))
        formal_record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(formal_record["status"], "retry")
        self.assertEqual(formal_record["certificate"], {})
        self.assertEqual(
            formal_record["reopen_history"][-1]["previous_certificate"],
            old_certificate,
        )
        self.assertEqual(read_stage(self.progress), "autoformalize")
        self.assertEqual(parse_objective_files(self.progress, self.project), [self.target])
        formalizer_kept, formalizer_dropped = filter_objectives_for_proof_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            enabled=True,
            stage="autoformalize",
        )
        self.assertEqual(formalizer_kept, [self.target])
        self.assertEqual(formalizer_dropped, [])
        self.assertIn("physics-formalize", self.progress.read_text(encoding="utf-8"))
        self.assertEqual(proof_result.needs_redraft, ("Problems/p.lean",))

        repassed = self._apply_formalization(3)
        self.assertEqual(repassed.passed, ("Problems/p.lean",))
        proof_record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(proof_record["status"], "retry")
        self.assertEqual(proof_record["attempts"], 0)
        self.assertEqual(proof_record["redraft_resolved_iter"], 3)
        formal_record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(
            formal_record["reopen_history"][-1]["previous_certificate"],
            old_certificate,
        )
        self.assertEqual(read_stage(self.progress), "prover")

    def test_chemistry_proof_review_redraft_restores_chemistry_formalizer(self):
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
        self._write_progress("autoformalize")
        self._apply_formalization(1)
        proof_session = self._proof_session(
            2,
            route="needs_redraft",
            status="blocked",
            redraft_kind="answer_as_assumption",
        )
        self._apply_proof(2, proof_session)
        proof_record = load_proof_review_state(self.state)["targets"][
            "Problems/p.lean"
        ]

        reopened = reopen_formalization_targets(
            state_dir=self.state,
            project_path=self.project,
            progress_file=self.progress,
            redrafts={"Problems/p.lean": proof_record},
            iter_num=2,
            max_iterations=3,
        )

        self.assertEqual(reopened, ("Problems/p.lean",))
        progress = self.progress.read_text(encoding="utf-8")
        self.assertIn("[prover-mode: chemistry-formalize]", progress)
        self.assertNotIn("[prover-mode: physics-formalize]", progress)


if __name__ == "__main__":
    unittest.main()
