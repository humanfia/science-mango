from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    load_gate_state,
    reopen_formalization_targets,
)
from archon.commands.loop.proof_review_gate import (
    apply_proof_review,
    apply_target_proof_review,
    filter_objectives_for_proof_review_gate,
    load_proof_review_state,
    reopen_exhausted_proof_review_targets,
)
from archon.commands.loop import proof_review_gate
from archon.commands.loop.problem_only_review_contract import (
    ProblemOnlyReviewContractError,
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

    def test_state_writer_updates_precreated_inode_when_parent_blocks_tempfile(self):
        path = self.state / "proof-review-gate.json"
        path.write_text("{}\n", encoding="utf-8")
        inode = path.stat().st_ino
        with mock.patch.object(
            Path, "write_bytes", side_effect=PermissionError("controller-owned parent")
        ):
            proof_review_gate._write_state(
                self.state, {"version": 1, "targets": {}}
            )
        self.assertEqual(path.stat().st_ino, inode)
        self.assertEqual(json.loads(path.read_text()), {"version": 1, "targets": {}})
        self.assertFalse(path.with_suffix(".json.tmp").exists())

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
        legacy_string_target: bool = False,
    ) -> Path:
        session = self.state / "proof-journal" / "sessions" / f"session_{iteration}"
        session.mkdir(parents=True)
        row = {
            "status": status,
            "target": (
                "Problems/p.lean"
                if legacy_string_target
                else {"file": "Problems/p.lean", "theorem": "p"}
            ),
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

    def test_forged_native_batch_milestone_fails_closed(self):
        session = self._proof_session(1, route="solved", status="solved")
        with mock.patch.object(
            proof_review_gate,
            "resolve_target_review_source_contract",
            return_value={"contract_kind": "native_problem_input_only"},
        ):
            result = self._apply_proof(1, session)

        self.assertEqual(result.solved, ())
        self.assertEqual(result.needs_redraft, ("Problems/p.lean",))
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertIn(
            "problem-only source contract validation failed",
            record["reason"],
        )
        self.assertIn("source_contract provenance is missing", record["reason"])

    def test_forged_native_immediate_milestone_fails_closed(self):
        session = self._proof_session(1, route="solved", status="solved")
        milestone = json.loads(
            (session / "milestones.jsonl").read_text(encoding="utf-8")
        )

        update = apply_target_proof_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=milestone,
            iter_num=1,
            max_iterations=3,
            event_id="pipeline:1:Problems/p.lean:proof:1",
            expected_source_contract={
                "contract_kind": "native_problem_input_only",
            },
        )

        self.assertEqual(update.status, "needs_redraft")
        self.assertEqual(update.route, "needs_redraft")
        self.assertIn(
            "problem-only source contract validation failed",
            update.reason,
        )
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        candidate_sha256 = hashlib.sha256(self.target.read_bytes()).hexdigest()
        self.assertEqual(record["candidate_sha256"], candidate_sha256)
        self.assertEqual(
            record["repair_events"][-1]["candidate_sha256"], candidate_sha256
        )

    def test_bad_native_source_target_does_not_collapse_batch(self):
        session = self._proof_session(1, route="solved", status="solved")
        good = self.project / "Problems" / "good.lean"
        good.write_text("theorem good : True := by trivial\n", encoding="utf-8")
        good_row = {
            "status": "solved",
            "target": {"file": "Problems/good.lean", "theorem": "good"},
            "proof_review": {
                "schema_version": 1,
                "route": "solved",
                "reason": "proof and theorem contract audited",
                "evidence": "the target compiles without sorry",
                "redraft_kind": "not_applicable",
            },
        }
        milestone_path = session / "milestones.jsonl"
        milestone_path.write_text(
            milestone_path.read_text(encoding="utf-8")
            + json.dumps(good_row)
            + "\n",
            encoding="utf-8",
        )

        def resolve(*, target, **_kwargs):
            if target.name == "p.lean":
                raise ProblemOnlyReviewContractError("sealed report is invalid")
            return {}

        with mock.patch.object(
            proof_review_gate,
            "resolve_target_review_source_contract",
            side_effect=resolve,
        ):
            result = apply_proof_review(
                state_dir=self.state,
                project_path=self.project,
                session_dir=session,
                iter_num=1,
                reviewed_objectives=[self.target, good],
                max_iterations=3,
            )

        self.assertEqual(result.solved, ("Problems/good.lean",))
        self.assertEqual(result.needs_redraft, ("Problems/p.lean",))
        records = load_proof_review_state(self.state)["targets"]
        self.assertEqual(records["Problems/good.lean"]["status"], "solved")
        self.assertIn(
            "problem-only source contract validation failed",
            records["Problems/p.lean"]["reason"],
        )

    def test_native_proof_freshness_binds_candidate_hash(self):
        provenance = {
            "contract_kind": "native_problem_input_only",
            "candidate_sha256": "old-solved-candidate",
        }
        state = {
            "version": 2,
            "max_iterations": 3,
            "targets": {
                "Problems/p.lean": {
                    "status": "solved",
                    "attempts": 1,
                    "source_contract": provenance,
                },
            },
        }

        with mock.patch.object(
            proof_review_gate,
            "stored_review_provenance_matches_current",
            return_value=(False, "candidate_sha256 changed"),
        ) as freshness:
            current = proof_review_gate._invalidate_stale_solved_records(
                state_dir=self.state,
                project_path=self.project,
                state=state,
            )

        self.assertEqual(current["targets"]["Problems/p.lean"]["status"], "retry")
        freshness.assert_called_once_with(
            project_path=self.project,
            target=self.target,
            provenance=provenance,
            bind_candidate=True,
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

    def test_legacy_string_target_is_consumed_like_object_target(self):
        session = self._proof_session(
            1,
            route="solved",
            status="solved",
            legacy_string_target=True,
        )

        result = self._apply_proof(1, session)

        self.assertEqual(result.solved, ("Problems/p.lean",))
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "solved")
        self.assertEqual(record["proof_review_route"], "solved")

    def test_missing_target_bound_milestone_is_auditable_retry(self):
        session = self.state / "proof-journal" / "sessions" / "session_1"
        session.mkdir(parents=True)
        (session / "milestones.jsonl").write_text("\n", encoding="utf-8")

        result = self._apply_proof(1, session)

        self.assertEqual(result.solved, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "retry")
        self.assertEqual(record["reason"], "missing proof Review milestone")
        self.assertEqual(record["history"][-1]["route"], "retry_proof")
        self.assertFalse(record["history"][-1]["explicit_route"])

    def test_duplicate_target_bound_milestones_fail_closed(self):
        session = self._proof_session(1, route="solved", status="solved")
        path = session / "milestones.jsonl"
        row = json.loads(path.read_text(encoding="utf-8"))
        path.write_text(
            json.dumps(row) + "\n" + json.dumps(row) + "\n",
            encoding="utf-8",
        )

        result = self._apply_proof(1, session)

        self.assertEqual(result.solved, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        record = load_proof_review_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "retry")
        self.assertIn("expected exactly one", record["reason"])
        self.assertIn("found 2", record["reason"])
        self.assertIn("duplicate", record["history"][-1]["evidence"])

    def test_milestone_target_normalization_rejects_unsafe_paths_and_shapes(self):
        normalize = proof_review_gate._milestone_target_file
        self.assertEqual(
            normalize({"target": "Problems/p.lean"}, self.project),
            "Problems/p.lean",
        )
        self.assertEqual(
            normalize(
                {"target": {"file": str(self.target), "theorem": "p"}},
                self.project,
            ),
            "Problems/p.lean",
        )
        outside = self.project.parent / "outside-proof-review.lean"
        rejected = (
            {"target": str(outside)},
            {"target": "../outside-proof-review.lean"},
            {"target": "Problems/p.txt"},
            {"target": ""},
            {"target": {"file": ""}},
            {"target": ["Problems/p.lean"]},
        )
        for row in rejected:
            with self.subTest(target=row["target"]):
                self.assertEqual(normalize(row, self.project), "")

    def test_r6_shaped_legacy_string_batch_consumes_all_32_rows(self):
        session = self.state / "proof-journal" / "sessions" / "session_3"
        session.mkdir(parents=True)
        targets = []
        rows = []
        for index in range(32):
            rel = f"Problems/r6_{index:02d}.lean"
            target = self.project / rel
            target.write_text(
                f"theorem r6_{index:02d} : True := by trivial\n",
                encoding="utf-8",
            )
            targets.append(target)
            rows.append({
                "status": "solved",
                "target": rel,
                "proof_review": {
                    "schema_version": 1,
                    "route": "solved",
                    "reason": "proof and theorem contract audited",
                    "evidence": "the target compiles without sorry",
                    "redraft_kind": "not_applicable",
                },
            })
        (session / "milestones.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in rows),
            encoding="utf-8",
        )

        result = apply_proof_review(
            state_dir=self.state,
            project_path=self.project,
            session_dir=session,
            iter_num=3,
            reviewed_objectives=targets,
            max_iterations=3,
        )

        expected = {f"Problems/r6_{index:02d}.lean" for index in range(32)}
        self.assertEqual(set(result.solved), expected)
        self.assertEqual(set(result.reviewed), expected)
        self.assertEqual(result.retry, ())
        state = load_proof_review_state(self.state)
        self.assertTrue(all(
            state["targets"][rel]["status"] == "solved" for rel in expected
        ))

    def test_validate_review_accepts_legacy_string_target_without_crashing(self):
        session = self.state / "proof-journal" / "sessions" / "validator"
        session.mkdir(parents=True)
        row = {
            "status": "solved",
            "target": "Problems/p.lean",
            "proof_review": {
                "schema_version": 1,
                "route": "solved",
                "reason": "reviewed",
                "evidence": "compiled target inspected",
                "redraft_kind": "not_applicable",
            },
        }
        (session / "milestones.jsonl").write_text(
            json.dumps(row) + "\n", encoding="utf-8",
        )
        (session / "summary.md").write_text(
            "## Review\n\n" + ("evidence " * 30) + "\n\n## Outcome\n\nSolved.\n",
            encoding="utf-8",
        )
        script = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "archon"
            / ".archon-src"
            / "scripts"
            / "validate-review.py"
        )

        completed = subprocess.run(
            [sys.executable, str(script), str(session)],
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertEqual(completed.returncode, 1, completed.stderr)
        self.assertIn("missing target.theorem", completed.stdout)
        self.assertIn("but no attempts recorded", completed.stdout)
        self.assertIn("0 failures", completed.stdout)
        self.assertNotIn("Traceback", completed.stderr)

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
        candidate_sha256 = hashlib.sha256(self.target.read_bytes()).hexdigest()
        self.assertEqual(proof_record["candidate_sha256"], candidate_sha256)
        self.assertIsNone(proof_record["source_contract"])
        transition = proof_record["repair_events"][-1]
        self.assertEqual(
            transition["transition"], "formalization_redraft_passed"
        )
        self.assertEqual(transition["candidate_sha256"], candidate_sha256)
        self.assertEqual(transition["failed_check_ids"], [])
        self.assertEqual(proof_record["repair_handoff"], {})
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
