from __future__ import annotations

import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from archon.commands.loop.parallel_formalization_review import (
    build_target_formalization_review_prompt,
    load_target_formalization_milestone,
    run_parallel_formalization_reviews,
)
from archon.commands.loop.parallel_review import TargetReviewOutcome


def _blind_contract(rel: str) -> dict:
    digest = "b" * 64
    return {
        "schema_version": 3,
        "required": True,
        "available": True,
        "valid": True,
        "domain": "chemistry",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "authority": "problem-only",
        "target": rel,
        "lean_sha256": digest,
        "blueprint": "blueprint.tex",
        "blueprint_sha256": digest,
        "source_report": "problem.source.json",
        "source_sha256": digest,
        "entry_id": "problem_a",
        "blind_record_sha256": digest,
        "blind_candidate_record": "blind_candidates/problem_a.json",
        "blind_candidate_sha256": digest,
        "lean_result_contracts_sha256": digest,
        "question_field": "question",
        "question_sha256": digest,
        "previous_blind_sha256": digest,
        "previous_blind_hashes": [],
        "images": [],
        "errors": [],
        "problem_evidence": {
            "current_question": "Compute the requested quantity.",
            "previous_parts": [],
        },
    }


def _milestone(rel: str, *, passed: bool = True) -> dict:
    checks = {
        "source_faithfulness": {
            "status": "passed" if passed else "failed",
            "evidence": "the source quantity is represented explicitly",
        },
        "derivability": {
            "status": "passed",
            "evidence": "the conclusion follows without assuming the answer",
        },
        "abstraction_sufficiency": {
            "status": "passed",
            "evidence": "the model retains every relevant degree of freedom",
        },
        "uncertainty_propagation": {
            "status": "not_applicable",
            "evidence": "the source has no uncertainty calculation",
        },
        "branch_orientation": {
            "status": "not_applicable",
            "evidence": "the source has no branch choice",
        },
        "countermodel_resistance": {
            "status": "passed",
            "evidence": "no countermodel survives the explicit assumptions",
        },
    }
    return {
        "timestamp": "2026-07-28T00:00:00Z",
        "target": {"file": rel, "theorem": "example"},
        "status": "solved" if passed else "blocked",
        "formalization_review": {
            "schema_version": 2,
            "status": "passed" if passed else "failed",
            "reason": (
                "the contract is faithful"
                if passed else "the contract omits a source constraint"
            ),
            "checks": checks,
            "bridge_obligations": [{
                "claim": "source relation",
                "carrier": "hypothesis h_relation",
                "status": "covered",
                "evidence": "h_relation is used in the target derivation",
            }],
        },
        "attempts": [{
            "attempt": 1,
            "strategy": "formalization-review",
            "code_tried": "",
            "lean_error": "",
            "goal_before": "",
            "goal_after": "",
            "result": "success" if passed else "failed",
            "insight": "semantic contract inspected",
        }],
        "findings": {
            "blocker": "" if passed else "missing source constraint",
            "verification": "bounded semantic review",
            "key_lemmas_used": [],
        },
        "session": {"id": "session_1", "model": "test"},
        "next_steps": "" if passed else "restore the missing constraint",
    }


class ParallelFormalizationReviewTest(unittest.TestCase):
    def test_blind_prompt_uses_blind_schema_and_freeze_protocol(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target = root / "Problems" / "A.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem a : True := by sorry\n")
            prompt = build_target_formalization_review_prompt(
                project_path=root,
                state_dir=root / ".archon",
                iter_dir=root / ".archon" / "iter-1",
                iter_num=1,
                target=target,
                output_dir=root / ".archon" / "review",
                preflight={"compiles": True},
                prior_gate_record=None,
                source_contract=_blind_contract("Problems/A.lean"),
            )
            self.assertIn("Mandatory answer-blind derivation protocol", prompt)
            self.assertIn("symbolic specification", prompt)
            self.assertIn("frozen before any later reveal", prompt)
            for name in (
                "answer_independence", "raw_derivation",
                "reporting_rule_source", "tolerance_provenance",
                "candidate_domain_provenance", "lean_result_binding",
            ):
                self.assertIn(name, prompt)
            self.assertNotIn('"official_answer_alignment"', prompt)
            self.assertNotIn('"source_inconsistency"', prompt)

    def test_prompt_is_target_scoped_and_allows_sorry_bodies(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            target = root / "Problems" / "A.lean"
            output = (
                iter_dir / "formalization-review-targets" / "Problems_A"
                / "attempt-1"
            )
            target.parent.mkdir(parents=True)
            result_dir = state / "task_results"
            result_dir.mkdir(parents=True)
            flat_result = result_dir / "A.md"
            flat_result.write_text("current formalizer result\n")
            target.write_text("theorem a : True := by sorry\n")

            prompt = build_target_formalization_review_prompt(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                target=target,
                output_dir=output,
                preflight={"file": "Problems/A.lean", "compiles": True},
                prior_gate_record=None,
            )

            self.assertIn("Assigned target (review only this target)", prompt)
            self.assertIn("semantic formalization Review", prompt)
            self.assertIn("`sorry` proof bodies are", prompt)
            self.assertIn("Do not edit", prompt)
            self.assertIn("PROGRESS.md", prompt)
            self.assertIn(str(output / "milestones.jsonl"), prompt)
            self.assertIn("countermodel_resistance", prompt)

            self.assertIn(str(flat_result), prompt)

    def test_certificate_validation_is_target_strict_and_fail_closed(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "milestones.jsonl"
            path.write_text(json.dumps(_milestone("A.lean")) + "\n")

            row, error = load_target_formalization_milestone(path, "A.lean")
            self.assertEqual(row["status"], "solved")
            self.assertEqual(error, "")

            row, error = load_target_formalization_milestone(path, "B.lean")
            self.assertIsNone(row)
            self.assertIn("!=", error)

            contradictory = _milestone("A.lean")
            contradictory["formalization_review"]["checks"][
                "source_faithfulness"
            ]["status"] = "failed"
            path.write_text(json.dumps(contradictory) + "\n")
            row, error = load_target_formalization_milestone(path, "A.lean")
            self.assertIsNone(row)
            self.assertIn("contradicts", error)

    def test_transient_failures_halve_concurrency_then_merge_once(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            objectives = []
            for name in ("A", "B", "C", "D"):
                target = root / f"{name}.lean"
                target.write_text(f"theorem {name.lower()} : True := by sorry\n")
                objectives.append(target)

            calls: dict[str, int] = {}

            def fake_worker(spec, **_kwargs):
                calls[spec.rel] = calls.get(spec.rel, 0) + 1
                if spec.rel in {"B.lean", "D.lean"} and spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error="429 rate limit",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(
                        spec.rel, passed=spec.rel != "D.lean",
                    ),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=2,
                objectives=objectives,
                preflight={"targets": [
                    {"file": path.name, "compiles": True}
                    for path in objectives
                ]},
                prior_gate_targets={},
                requested_jobs=4,
                max_attempts=3,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=fake_worker,
                executor_factory=ThreadPoolExecutor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(
                [(item["jobs"], item["failed"]) for item in report["rounds"]],
                [(4, 2), (2, 0)],
            )
            self.assertEqual(calls, {
                "A.lean": 1,
                "B.lean": 2,
                "C.lean": 1,
                "D.lean": 2,
            })
            session = state / "proof-journal" / "sessions" / "session_2"
            rows = [
                json.loads(line)
                for line in (session / "milestones.jsonl").read_text().splitlines()
            ]
            self.assertEqual(
                [row["target"]["file"] for row in rows],
                ["A.lean", "B.lean", "C.lean", "D.lean"],
            )
            self.assertIn(
                "D.lean",
                (session / "recommendations.md").read_text(),
            )

    def test_incomplete_batch_does_not_replace_existing_session(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-003"
            session = state / "proof-journal" / "sessions" / "session_3"
            iter_dir.mkdir(parents=True)
            session.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n")
            milestone_path = session / "milestones.jsonl"
            milestone_path.write_text("preexisting journal\n")

            def failed_worker(spec, **_kwargs):
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=False,
                    milestone=None,
                    error="malformed output",
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=3,
                objectives=[target],
                preflight={"targets": []},
                prior_gate_targets={},
                requested_jobs=2,
                max_attempts=1,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=failed_worker,
                executor_factory=ThreadPoolExecutor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertFalse(report["complete"])
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertEqual(milestone_path.read_text(), "preexisting journal\n")


if __name__ == "__main__":
    unittest.main()
