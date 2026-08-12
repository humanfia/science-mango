from __future__ import annotations

import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from archon.commands.loop.parallel_review import (
    TargetReviewOutcome,
    build_target_review_prompt,
    load_target_milestone,
    run_parallel_target_reviews,
)


def _blind_contract(rel: str) -> dict:
    digest = "c" * 64
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
        "question_field": "current_question",
        "question_sha256": digest,
        "previous_blind_sha256": digest,
        "previous_blind_hashes": [],
        "images": [],
        "errors": [],
        "problem_evidence": {
            "current_question": "Derive the result from the given data.",
            "previous_parts": [],
        },
    }


def _milestone(rel: str, status: str = "solved") -> dict:
    return {
        "timestamp": "2026-07-23T00:00:00Z",
        "target": {"file": rel, "theorem": "example"},
        "status": status,
        "proof_review": {
            "schema_version": 1,
            "route": "solved" if status == "solved" else "retry_proof",
            "reason": "target audit completed",
            "evidence": "Lean and contract evidence checked",
            "redraft_kind": "not_applicable",
        },
        "attempts": [{
            "attempt": 1,
            "strategy": "review",
            "code_tried": "",
            "lean_error": "",
            "goal_before": "",
            "goal_after": "",
            "result": "success" if status == "solved" else "partial",
            "insight": "checked",
        }],
        "findings": {
            "blocker": "" if status == "solved" else "needs repair",
            "verification": "checked",
            "key_lemmas_used": [],
        },
        "session": {"id": "session_1", "model": "test"},
        "next_steps": "",
    }


class ParallelReviewTest(unittest.TestCase):
    def test_blind_prompt_has_no_official_alignment_schema(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target = root / "Problems" / "A.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem a : True := by trivial\n")
            prompt = build_target_review_prompt(
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
            self.assertIn("candidate-domain restriction", prompt)
            for name in (
                "answer_independence", "raw_derivation",
                "reporting_rule_source", "tolerance_provenance",
                "candidate_domain_provenance", "lean_result_binding",
            ):
                self.assertIn(name, prompt)
            self.assertNotIn('"official_answer_alignment"', prompt)
            self.assertNotIn('"source_inconsistency"', prompt)

    def test_target_prompt_isolated_and_forbids_shared_writes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            target = root / "Problems" / "A.lean"
            output = iter_dir / "review-targets" / "A" / "attempt-1"
            target.parent.mkdir(parents=True)
            target.write_text("theorem a : True := by trivial\n")
            result_dir = state / "task_results"
            result_dir.mkdir(parents=True)
            flat_result = result_dir / "A.lean.md"
            flat_result.write_text("current proof result\n")
            prompt = build_target_review_prompt(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                target=target,
                output_dir=output,
                preflight={"file": "Problems/A.lean", "compiles": True},
                prior_gate_record=None,
            )
            self.assertIn("Assigned target (the only target", prompt)
            self.assertIn("Problems/A.lean", prompt)
            self.assertIn(str(flat_result), prompt)
            self.assertIn("Do not fail a target", prompt)
            self.assertIn("Do not edit Lean, blueprint, PROGRESS.md", prompt)
            self.assertIn(str(output / "milestones.jsonl"), prompt)
            self.assertIn("needs_redraft", prompt)
            self.assertIn("missing foundational bridge", prompt)

    def test_milestone_validation_is_target_strict(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "milestones.jsonl"
            path.write_text(json.dumps(_milestone("A.lean")) + "\n")
            row, error = load_target_milestone(path, "A.lean")
            self.assertEqual(row["status"], "solved")
            self.assertEqual(error, "")
            row, error = load_target_milestone(path, "B.lean")
            self.assertIsNone(row)
            self.assertIn("!=", error)

            legacy = _milestone("A.lean")
            legacy.pop("proof_review")
            path.write_text(json.dumps(legacy) + "\n")
            row, error = load_target_milestone(path, "A.lean")
            self.assertIsNone(row)
            self.assertIn("routing certificate is missing", error)

    def test_failure_round_halves_concurrency_then_aggregates(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            objectives = []
            for name in ("A", "B", "C", "D"):
                path = root / f"{name}.lean"
                path.write_text(f"theorem {name.lower()} : True := by trivial\n")
                objectives.append(path)

            calls: dict[str, int] = {}

            def fake_worker(spec, **_kwargs):
                calls[spec.rel] = calls.get(spec.rel, 0) + 1
                # B and D simulate one transient harness/rate-limit failure.
                if spec.rel in {"B.lean", "D.lean"} and spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error="429 rate limit",
                    )
                out = Path(spec.output_dir)
                out.mkdir(parents=True, exist_ok=True)
                row = _milestone(spec.rel)
                (out / "milestones.jsonl").write_text(
                    json.dumps(row) + "\n", encoding="utf-8",
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=row,
                )

            report = run_parallel_target_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=2,
                objectives=objectives,
                preflight={"targets": [
                    {"file": p.name, "compiles": True, "sorry_count": 0}
                    for p in objectives
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
                [(r["jobs"], r["failed"]) for r in report["rounds"]],
                [(4, 2), (2, 0)],
            )
            self.assertEqual(calls, {"A.lean": 1, "B.lean": 2,
                                     "C.lean": 1, "D.lean": 2})
            session = state / "proof-journal" / "sessions" / "session_2"
            rows = [
                json.loads(line)
                for line in (session / "milestones.jsonl").read_text().splitlines()
            ]
            self.assertEqual(
                [row["target"]["file"] for row in rows],
                ["A.lean", "B.lean", "C.lean", "D.lean"],
            )


if __name__ == "__main__":
    unittest.main()
