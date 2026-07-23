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


def _milestone(rel: str, status: str = "solved") -> dict:
    return {
        "timestamp": "2026-07-23T00:00:00Z",
        "target": {"file": rel, "theorem": "example"},
        "status": status,
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
