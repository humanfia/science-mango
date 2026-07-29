from __future__ import annotations

import hashlib
import json
import tempfile
import threading
import time
import unittest
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.foundation_build_gate import (
    foundation_build_is_dispatchable,
    foundation_materialization_is_current,
    foundation_materialization_matches_proof_review,
    foundation_relpath,
    record_foundation_build_attempt,
)
from archon.commands.loop.formalization_review_gate import (
    apply_target_formalization_review,
)
from archon.commands.loop.parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewOutcome,
    load_pipelined_review_report,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from archon.commands.loop.phases.prover import ProverPhase
from archon.commands.loop.phases.review import ReviewPhase
from archon.commands.loop.proof_review_gate import apply_target_proof_review
from archon.commands.loop.prover.runners import ParallelProverRunner


def _milestone(rel: str) -> dict:
    return {
        "timestamp": "2026-07-28T00:00:00Z",
        "target": {"file": rel, "theorem": "example"},
        "status": "solved",
        "proof_review": {
            "schema_version": 1,
            "route": "solved",
            "reason": "proof and contract passed",
            "evidence": "direct Lean preflight and semantic audit passed",
            "redraft_kind": "not_applicable",
        },
        "attempts": [],
        "findings": {
            "blocker": "",
            "verification": "checked",
            "key_lemmas_used": [],
        },
        "session": {"id": "session_1", "model": "test"},
        "next_steps": "",
    }


def _redraft_milestone(rel: str) -> dict:
    row = _milestone(rel)
    row["status"] = "blocked"
    row["proof_review"] = {
        "schema_version": 1,
        "route": "needs_redraft",
        "reason": "the theorem assumes the requested conclusion",
        "evidence": "hypothesis h_answer is identical to the target",
        "redraft_kind": "answer_as_assumption",
    }
    row["findings"]["blocker"] = "answer is encoded as an assumption"
    row["next_steps"] = "remove h_answer and encode the governing law"
    return row


def _foundation_redraft_milestone(rel: str) -> dict:
    row = _redraft_milestone(rel)
    row["proof_review"] = {
        "schema_version": 1,
        "route": "needs_redraft",
        "reason": "the faithful target needs a missing entropy bridge",
        "evidence": "no local strong-subadditivity eliminator is available",
        "redraft_kind": "missing_foundational_bridge",
    }
    row["findings"]["blocker"] = "missing reusable entropy theorem"
    row["next_steps"] = "build the bridge before retrying the target"
    return row


def _retry_proof_milestone(rel: str) -> dict:
    row = _milestone(rel)
    row["status"] = "partial"
    row["proof_review"] = {
        "schema_version": 1,
        "route": "retry_proof",
        "reason": "the contract is faithful but the proof is incomplete",
        "evidence": "one Lean goal remains after a valid tactic attempt",
        "redraft_kind": "not_applicable",
    }
    row["findings"]["blocker"] = "remaining tactic and lemma search"
    row["next_steps"] = "retry the proof without changing the statement"
    return row


def _formalization_milestone(rel: str, *, passed: bool = True) -> dict:
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
            "evidence": "no countermodel survives the assumptions",
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
                if passed
                else "the contract omits a source constraint"
            ),
            "checks": checks,
            "bridge_obligations": [{
                "claim": "source relation",
                "carrier": "hypothesis h_relation",
                "status": "covered",
                "evidence": "h_relation carries the source relation",
            }],
        },
        "attempts": [],
        "findings": {
            "blocker": "" if passed else "missing source constraint",
            "verification": "semantic contract review",
            "key_lemmas_used": [],
        },
        "session": {"id": "session_1", "model": "test"},
        "next_steps": "" if passed else "restore the source constraint",
    }


def _process_prover(*_args, **_kwargs) -> bool:
    return True


def _process_review(spec, **_kwargs) -> TargetReviewOutcome:
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=True,
        milestone=_milestone(spec.rel),
    )


def _process_redraft_review(spec, **_kwargs) -> TargetReviewOutcome:
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=True,
        milestone=_redraft_milestone(spec.rel),
    )


def _process_pipeline_review(
    spec, *, project_path: Path, **_kwargs
) -> TargetReviewOutcome:
    redrafted = "h_law" in (project_path / spec.rel).read_text(encoding="utf-8")
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=True,
        milestone=_milestone(spec.rel) if redrafted else _redraft_milestone(spec.rel),
    )


def _process_formalization_review(spec, **_kwargs) -> TargetReviewOutcome:
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=True,
        milestone=_formalization_milestone(spec.rel),
    )


def _process_formalizer(_prompt, cwd, *_args, **_kwargs) -> bool:
    (Path(cwd) / "A.lean").write_text(
        "theorem a (h_law : True) : True := by sorry\n",
        encoding="utf-8",
    )
    (Path(cwd) / ".archon" / "task_results" / "A.lean.md").write_text(
        "# Redraft\n\nRemoved the answer-as-assumption contract.\n",
        encoding="utf-8",
    )
    return True


def _preflight(*, project_path: Path, target: Path, timeout_sec: int) -> dict:
    del timeout_sec
    rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    return {
        "file": rel,
        "status": "passed",
        "compiles": True,
        "returncode": 0,
        "sorry_count": 0,
        "duration_secs": 0.01,
        "diagnostics": "",
    }


class PipelinedReviewTest(unittest.TestCase):
    def _runner(
        self,
        *,
        root: Path,
        state: Path,
        iter_dir: Path,
        prover_worker,
        review_worker,
        formalizer_worker=None,
        max_parallel: int = 2,
        max_attempts: int = 3,
        executor_factory=ThreadPoolExecutor,
        resume_enabled: bool = False,
        full_pipeline: bool = False,
        formalization_review_worker=_process_formalization_review,
        formalization_max_iterations: int = 3,
        foundation_enabled: bool = False,
        foundation_max_iterations: int = 3,
        stage: str = "prover",
    ) -> ParallelProverRunner:
        return ParallelProverRunner(
            project_name="project",
            project_path=root,
            state_dir=state,
            stage=stage,
            iter_dir=iter_dir,
            iter_meta=iter_dir / "meta.json",
            iter_num=1,
            max_parallel=max_parallel,
            max_objectives=10,
            block_on_blocked_deps=False,
            verbose_logs=False,
            model="test",
            resume_enabled=resume_enabled,
            pipeline_review=PipelinedTargetReviewConfig(
                requested_jobs=max_parallel,
                max_attempts=max_attempts,
                backoff_sec=0,
                preflight_timeout_sec=30,
                formalization_review_enabled=full_pipeline,
                formalization_review_max_attempts=3,
                formalization_review_backoff_sec=0,
                formalization_review_max_iterations=formalization_max_iterations,
                foundation_build_enabled=foundation_enabled,
                foundation_build_max_iterations=foundation_max_iterations,
                foundation_root="ArchonFoundations",
            ),
            executor_factory=executor_factory,
            prover_worker=prover_worker,
            review_worker=review_worker,
            formalization_review_worker=formalization_review_worker,
            formalizer_worker=formalizer_worker,
            preflight_checker=_preflight,
        )

    def test_review_starts_before_slow_peer_prover_finishes_and_shares_cap(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            targets = []
            for name in ("A", "B"):
                target = root / f"{name}.lean"
                target.write_text(
                    f"theorem {name.lower()} : True := by sorry\n",
                    encoding="utf-8",
                )
                targets.append(target)

            review_a_started = threading.Event()
            lock = threading.Lock()
            order: list[str] = []
            active = 0
            max_active = 0

            def enter(label: str) -> None:
                nonlocal active, max_active
                with lock:
                    active += 1
                    max_active = max(max_active, active)
                    order.append(f"{label}:start")

            def leave(label: str) -> None:
                nonlocal active
                with lock:
                    order.append(f"{label}:end")
                    active -= 1

            def fake_prover(*args, **_kwargs):
                slug = Path(args[2]).name
                enter(f"prover-{slug}")
                try:
                    if slug == "B":
                        self.assertTrue(review_a_started.wait(timeout=5))
                    return True
                finally:
                    leave(f"prover-{slug}")

            def fake_review(spec, **_kwargs):
                label = f"review-{Path(spec.rel).stem}"
                enter(label)
                try:
                    if spec.rel == "A.lean":
                        review_a_started.set()
                    time.sleep(0.02)
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=_milestone(spec.rel),
                    )
                finally:
                    leave(label)

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_review,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="prove",
                ),
                patch(
                    "archon.commands.loop.prover.runners.snapshot_baseline"
                ),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout(targets, file_modes={})

            self.assertLess(order.index("review-A:start"), order.index("prover-B:end"))
            self.assertLessEqual(max_active, 2)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["target_files"], ["A.lean", "B.lean"])

    def test_needs_redraft_starts_formalizer_before_slow_peer_finishes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            targets = []
            for name in ("A", "B"):
                target = root / f"{name}.lean"
                target.write_text(
                    f"theorem {name.lower()} : True := by sorry\n",
                    encoding="utf-8",
                )
                targets.append(target)

            formalizer_started = threading.Event()
            order: list[str] = []
            lock = threading.Lock()
            formalizer_prompts: list[str] = []

            def record(event: str) -> None:
                with lock:
                    order.append(event)

            def fake_prover(*args, **_kwargs):
                slug = Path(args[2]).name
                record(f"prover-{slug}:start")
                if slug == "B":
                    self.assertTrue(formalizer_started.wait(timeout=5))
                record(f"prover-{slug}:end")
                return True

            def fake_review(spec, **_kwargs):
                record(f"review-{Path(spec.rel).stem}:start")
                milestone = (
                    _redraft_milestone(spec.rel)
                    if spec.rel == "A.lean"
                    else _milestone(spec.rel)
                )
                record(f"review-{Path(spec.rel).stem}:end")
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def fake_formalizer(*args, **_kwargs):
                formalizer_prompts.append(args[0])
                targets[0].write_text(
                    "theorem a (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Redraft\n\nRemoved the answer-as-assumption contract.\n",
                    encoding="utf-8",
                )
                record("formalizer-A:start")
                formalizer_started.set()
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_review,
                formalizer_worker=fake_formalizer,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout(targets, file_modes={})

            self.assertLess(
                order.index("formalizer-A:start"),
                order.index("prover-B:end"),
            )
            self.assertEqual(len(formalizer_prompts), 1)
            self.assertIn("global PROGRESS stage intentionally remains", formalizer_prompts[0])
            self.assertIn("the theorem assumes the requested conclusion", formalizer_prompts[0])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["formalizers"]["requested"], 1)
            self.assertEqual(report["formalizers"]["materialized"], 1)
            handoff = report["formalization_handoffs"]["A.lean"]
            self.assertEqual(handoff["status"], "materialized")
            self.assertEqual(handoff["lean_sha256"], hashlib.sha256(
                targets[0].read_bytes()
            ).hexdigest())

    def test_transient_review_failure_retries_without_new_proof_attempt(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            review_attempts: list[int] = []
            prover_calls = 0

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_review(spec, **_kwargs):
                review_attempts.append(spec.attempt)
                if spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error="transient 429",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_review,
                max_parallel=1,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="prove",
                ),
                patch(
                    "archon.commands.loop.prover.runners.snapshot_baseline"
                ),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(prover_calls, 1)
            self.assertEqual(review_attempts, [1, 2])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(
                [(row["attempt"], row["failed"]) for row in report["rounds"]],
                [(1, 1), (2, 0)],
            )

    def test_real_process_pool_smoke(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                max_parallel=1,
                executor_factory=ProcessPoolExecutor,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="prove",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])

    def test_real_process_pool_redraft_smoke(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_redraft_review,
                formalizer_worker=_process_formalizer,
                max_parallel=1,
                executor_factory=ProcessPoolExecutor,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["formalizers"], {
                "requested": 1,
                "materialized": 1,
                "failed": 0,
            })
            self.assertEqual(
                report["formalization_handoffs"]["A.lean"]["status"],
                "materialized",
            )

    def test_real_process_pool_full_target_loop_smoke(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8"
            )
            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_pipeline_review,
                formalizer_worker=_process_formalizer,
                formalization_review_worker=_process_formalization_review,
                max_parallel=1,
                executor_factory=ProcessPoolExecutor,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertTrue(report["gate_events_applied"])
            self.assertEqual(
                [event["kind"] for event in report["gate_events"]],
                ["proof", "formalization", "proof"],
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["status"], "solved")
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)

    def test_incomplete_formalizer_preserves_target_local_checkpoint(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")

            def durable_redraft_review(spec, **_kwargs):
                milestone = _redraft_milestone(spec.rel)
                output_dir = Path(spec.output_dir)
                output_dir.mkdir(parents=True, exist_ok=True)
                (output_dir / "milestones.jsonl").write_text(
                    json.dumps(milestone) + "\n", encoding="utf-8"
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def incomplete_formalizer(*_args, **_kwargs):
                target.write_text(
                    "theorem a (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=durable_redraft_review,
                formalizer_worker=incomplete_formalizer,
                max_parallel=1,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertFalse(report["complete"])
            self.assertTrue(report["gate_events_applied"])
            self.assertEqual(report["reviewed"], 1)
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertEqual(report["formalizers"]["failed"], 1)
            self.assertEqual(report["formalization_handoffs"], {})
            failure = report["formalizer_results"]["A.lean"]
            self.assertFalse(failure["task_result_updated"])
            self.assertIn("did not update its task result", failure["error"])
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                proof_gate["targets"]["A.lean"]["status"], "needs_redraft"
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)

            def recovered_formalizer(_prompt, cwd, *_args, **_kwargs):
                (Path(cwd) / "A.lean").write_text(
                    "theorem a (h_law h_bridge : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Recovered redraft\n\nAdded the missing bridge.\n",
                    encoding="utf-8",
                )
                return True

            resumed_runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_pipeline_review,
                formalizer_worker=recovered_formalizer,
                max_parallel=1,
                resume_enabled=True,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                resumed_runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(
                [row["cycle"] for row in report["formalizer_history"]["A.lean"]],
                [1, 2],
            )
            self.assertEqual(
                [
                    event["route"]
                    for event in report["gate_events"]
                    if event["kind"] == "proof"
                ],
                ["needs_redraft", "solved"],
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["status"], "solved")
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)

    def test_formalizer_accepts_stem_report_and_same_content_rewrite(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = (
                root
                / "IPhO2026Problems"
                / "problem_IPhO_2026_1_B_2.lean"
            )
            target.parent.mkdir()
            target.write_text(
                "theorem scattering : True := by sorry\n",
                encoding="utf-8",
            )
            task_result = (
                state
                / "task_results"
                / "problem_IPhO_2026_1_B_2.md"
            )
            evidence = "# Redraft evidence\n\nCentral-force bridge added.\n"
            task_result.write_text(evidence, encoding="utf-8")

            def stem_formalizer(*_args, **_kwargs):
                target.write_text(
                    "theorem scattering (h_law : True) : True := by trivial\n",
                    encoding="utf-8",
                )
                time.sleep(0.01)
                task_result.write_text(evidence, encoding="utf-8")
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                formalizer_worker=stem_formalizer,
                max_parallel=1,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            result = report["formalizer_results"][
                "IPhO2026Problems/problem_IPhO_2026_1_B_2.lean"
            ]
            self.assertTrue(result["task_result_updated"])
            self.assertIn(
                str(task_result), result["task_result_fingerprints"]
            )
            self.assertIn(str(task_result), result["task_result_mtimes"])

    def test_resume_recovers_legacy_unrecognized_stem_report(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            rel = "IPhO2026Problems/problem_IPhO_2026_1_B_2.lean"
            target = root / rel
            target.parent.mkdir()
            target.write_text(
                "theorem scattering (h_law : True) : True := by trivial\n",
                encoding="utf-8",
            )
            digest = hashlib.sha256(target.read_bytes()).hexdigest()
            time.sleep(0.01)
            task_result = (
                state
                / "task_results"
                / "problem_IPhO_2026_1_B_2.md"
            )
            task_result.write_text(
                "# Durable redraft\n\nCentral-force bridge added.\n",
                encoding="utf-8",
            )
            preflight = _preflight(
                project_path=root,
                target=target,
                timeout_sec=30,
            )
            legacy_result = {
                "iteration": 1,
                "file": rel,
                "cycle": 2,
                "status": "error",
                "review_attempt": 2,
                "runner_ok": True,
                "baseline_sha256": "0" * 64,
                "lean_sha256": digest,
                "changed": True,
                "task_result_updated": False,
                "task_result_fingerprints": {},
                "preflight": preflight,
                "error": "formalizer did not update its task result",
            }
            write_pipelined_review_report(
                iter_dir=iter_dir,
                report={
                    "iteration": 1,
                    "complete": False,
                    "status": "incomplete",
                    "pipeline_mode": "target_lifecycle",
                    "starts_at": "formalizer",
                    "target_files": [rel],
                    "settled_target_files": [],
                    "proof_review_target_files": [],
                    "targets": 1,
                    "reviewed": 0,
                    "unresolved": [rel],
                    "errors": {
                        rel: "formalizer did not update its task result",
                    },
                    "preflight": {
                        "iteration": 1,
                        "jobs": 1,
                        "duration_secs": 0.01,
                        "summary": {
                            "total": 1,
                            "passed": 1,
                            "failed": 0,
                        },
                        "targets": [preflight],
                    },
                    "formalizer_results": {rel: legacy_result},
                    "formalizer_history": {rel: [legacy_result]},
                    "pending_formalization_targets": [rel],
                    "gate_events": [],
                },
            )
            formalizer_calls: list[str] = []

            def unexpected_formalizer(*_args, **_kwargs):
                formalizer_calls.append(rel)
                return False

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                formalizer_worker=unexpected_formalizer,
                max_parallel=1,
                resume_enabled=True,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(formalizer_calls, [])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            recovered = report["formalizer_results"][rel]
            self.assertEqual(recovered["status"], "materialized")
            self.assertTrue(recovered["recovered_task_result_detection"])
            self.assertIn(str(task_result), recovered["task_result_fingerprints"])
            self.assertEqual(
                [
                    event["cycle"]
                    for event in report["gate_events"]
                    if event["kind"] == "formalization"
                ],
                [2],
            )

    def test_resume_reuses_settled_peer_and_reviews_only_unresolved_lane(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            targets = []
            for name in ("A", "B"):
                target = root / f"{name}.lean"
                target.write_text(
                    f"theorem {name.lower()} : True := by sorry\n",
                    encoding="utf-8",
                )
                targets.append(target)

            first_review_calls: list[str] = []

            def durable_outcome(spec, milestone):
                output_dir = Path(spec.output_dir)
                output_dir.mkdir(parents=True, exist_ok=True)
                (output_dir / "milestones.jsonl").write_text(
                    json.dumps(milestone) + "\n", encoding="utf-8"
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def first_review(spec, **_kwargs):
                first_review_calls.append(spec.rel)
                if spec.rel == "A.lean":
                    return durable_outcome(spec, _milestone(spec.rel))
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=False,
                    milestone=None,
                    error="temporary 429 without milestone",
                )

            first_runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=first_review,
                max_parallel=2,
                max_attempts=2,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                first_runner._run_fanout(targets, file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["settled_target_files"], ["A.lean"])
            self.assertEqual(report["unresolved"], ["B.lean"])
            self.assertEqual(first_review_calls.count("A.lean"), 1)
            self.assertEqual(first_review_calls.count("B.lean"), 2)

            resumed_review_calls: list[str] = []
            resumed_prover_calls: list[str] = []
            resumed_formalizer_calls: list[str] = []

            def resumed_prover(*args, **_kwargs):
                resumed_prover_calls.append(Path(args[2]).name)
                return True

            def resumed_formalizer(_prompt, cwd, *_args, **_kwargs):
                resumed_formalizer_calls.append("B.lean")
                (Path(cwd) / "B.lean").write_text(
                    "theorem b (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "B.lean.md").write_text(
                    "# Redraft\n\nRestored the governing law.\n",
                    encoding="utf-8",
                )
                return True

            def resumed_review(spec, **_kwargs):
                resumed_review_calls.append(spec.rel)
                redrafted = "h_law" in (root / spec.rel).read_text(
                    encoding="utf-8"
                )
                milestone = (
                    _milestone(spec.rel)
                    if redrafted else _redraft_milestone(spec.rel)
                )
                return durable_outcome(spec, milestone)

            resumed_runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=resumed_prover,
                review_worker=resumed_review,
                formalizer_worker=resumed_formalizer,
                max_parallel=2,
                max_attempts=2,
                resume_enabled=True,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                resumed_runner._run_fanout(targets, file_modes={})

            self.assertEqual(resumed_review_calls, ["B.lean", "B.lean"])
            self.assertEqual(resumed_formalizer_calls, ["B.lean"])
            self.assertEqual(resumed_prover_calls, ["B"])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(
                report["settled_target_files"], ["A.lean", "B.lean"]
            )
            self.assertTrue(report["gate_events_applied"])
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)
            self.assertEqual(proof_gate["targets"]["B.lean"]["attempts"], 1)

    def test_full_target_loop_requeues_after_formalization_review(self):
        cases = (
            ("passes", [True], 2, "passed", "solved"),
            ("retries_then_passes", [False, True], 2, "passed", "solved"),
            (
                "exhausts_three_formalization_reviews",
                [False, False, False],
                1,
                "review_exhausted",
                "needs_redraft",
            ),
        )
        for (
            label,
            formalization_verdicts,
            expected_provers,
            expected_formalization_status,
            expected_proof_status,
        ) in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                state = root / ".archon"
                iter_dir = state / "logs" / "iter-001"
                (iter_dir / "provers").mkdir(parents=True)
                (state / "task_results").mkdir()
                (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
                target = root / "A.lean"
                target.write_text(
                    "theorem a : True := by sorry\n", encoding="utf-8"
                )
                prover_calls = 0
                proof_review_calls = 0
                formalizer_calls = 0
                formalization_review_calls: list[bool] = []

                def fake_prover(*_args, **_kwargs):
                    nonlocal prover_calls
                    prover_calls += 1
                    return True

                def fake_proof_review(spec, **_kwargs):
                    nonlocal proof_review_calls
                    proof_review_calls += 1
                    if proof_review_calls > 1:
                        self.assertIn('"attempts": 0', spec.prompt)
                        self.assertIn(
                            "formalization redraft passed", spec.prompt
                        )
                    milestone = (
                        _redraft_milestone(spec.rel)
                        if proof_review_calls == 1
                        else _milestone(spec.rel)
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=milestone,
                    )

                def fake_formalizer(*_args, **_kwargs):
                    nonlocal formalizer_calls
                    formalizer_calls += 1
                    target.write_text(
                        f"theorem a (h_law_{formalizer_calls} : True) : "
                        "True := by sorry\n",
                        encoding="utf-8",
                    )
                    (state / "task_results" / "A.lean.md").write_text(
                        f"# Redraft {formalizer_calls}\n",
                        encoding="utf-8",
                    )
                    return True

                def fake_formalization_review(spec, **_kwargs):
                    if not formalization_review_calls:
                        self.assertIn('"status": "retry"', spec.prompt)
                        self.assertIn(
                            "proof Review redraft", spec.prompt
                        )
                    passed = formalization_verdicts[
                        len(formalization_review_calls)
                    ]
                    formalization_review_calls.append(passed)
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=_formalization_milestone(
                            spec.rel, passed=passed
                        ),
                    )

                runner = self._runner(
                    root=root,
                    state=state,
                    iter_dir=iter_dir,
                    prover_worker=fake_prover,
                    review_worker=fake_proof_review,
                    formalizer_worker=fake_formalizer,
                    formalization_review_worker=fake_formalization_review,
                    max_parallel=1,
                    full_pipeline=True,
                    formalization_max_iterations=3,
                )
                with (
                    patch(
                        "archon.commands.loop.prover.runners."
                        "build_parallel_prover_prompt",
                        return_value="work",
                    ),
                    patch(
                        "archon.commands.loop.prover.runners.snapshot_baseline"
                    ),
                    patch(
                        "archon.commands.loop.prover.runners.pick_resume_session",
                        return_value=None,
                    ),
                    patch(
                        "archon.commands.loop.prover.runners.persist_session_id"
                    ),
                ):
                    runner._run_fanout([target], file_modes={})

                report = json.loads(
                    (iter_dir / "pipelined-review.json").read_text(
                        encoding="utf-8"
                    )
                )
                proof_gate = json.loads(
                    (state / "proof-review-gate.json").read_text(encoding="utf-8")
                )
                formalization_gate = json.loads(
                    (state / "formalization-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertTrue(report["complete"])
                self.assertTrue(report["gate_events_applied"])
                self.assertEqual(prover_calls, expected_provers)
                self.assertEqual(proof_review_calls, expected_provers)
                self.assertEqual(formalizer_calls, len(formalization_verdicts))
                self.assertEqual(
                    formalization_review_calls, formalization_verdicts
                )
                self.assertEqual(
                    formalization_gate["targets"]["A.lean"]["status"],
                    expected_formalization_status,
                )
                self.assertEqual(
                    formalization_gate["targets"]["A.lean"]["reviews"],
                    len(formalization_verdicts),
                )
                proof_record = proof_gate["targets"]["A.lean"]
                self.assertEqual(proof_record["status"], expected_proof_status)
                self.assertEqual(proof_record["attempts"], 1)
                self.assertEqual(
                    report["formalizers"]["requested"],
                    len(formalization_verdicts),
                )
                self.assertEqual(
                    [event["kind"] for event in report["gate_events"]],
                    ["proof"]
                    + ["formalization"] * len(formalization_verdicts)
                    + (["proof"] if formalization_verdicts[-1] else []),
                )

    def test_foundation_gate_is_digest_bound_and_idempotent(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            state.mkdir()
            target = root / "QIT" / "A.lean"
            target.parent.mkdir()
            target.write_text("theorem a : True := by trivial\n", encoding="utf-8")
            foundation_rel = foundation_relpath(
                "QIT/A.lean", "ArchonFoundations",
            )
            foundation = root / foundation_rel
            foundation.parent.mkdir()
            foundation.write_text(
                "theorem entropyBridge : True := by trivial\n",
                encoding="utf-8",
            )
            proof_record = {
                "status": "needs_redraft",
                "attempts": 1,
                "redraft_kind": "missing_foundational_bridge",
                "history": [{"event_id": "proof:event:1"}],
            }
            (state / "proof-review-gate.json").write_text(
                json.dumps({
                    "targets": {"QIT/A.lean": proof_record},
                }),
                encoding="utf-8",
            )
            result = {"status": "materialized", "error": ""}
            certificate = _foundation_redraft_milestone(
                "QIT/A.lean"
            )["proof_review"]
            certificate["source_proof_event_id"] = "proof:event:1"

            first = record_foundation_build_attempt(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
                foundation_file=foundation_rel,
                certificate=certificate,
                result=result,
                iter_num=1,
                max_iterations=3,
                event_id="foundation:event:1",
            )
            replay = record_foundation_build_attempt(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
                foundation_file=foundation_rel,
                certificate=certificate,
                result=result,
                iter_num=1,
                max_iterations=3,
                event_id="foundation:event:1",
            )

            self.assertEqual(first.status, "materialized")
            self.assertEqual(first.attempts, 1)
            self.assertFalse(replay.applied)
            self.assertEqual(replay.attempts, 1)
            self.assertTrue(foundation_materialization_is_current(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
            ))
            self.assertTrue(
                foundation_materialization_matches_proof_review(
                    state_dir=state,
                    project_path=root,
                    target_rel="QIT/A.lean",
                )
            )
            proof_record["history"].append({"event_id": "proof:event:2"})
            (state / "proof-review-gate.json").write_text(
                json.dumps({
                    "targets": {"QIT/A.lean": proof_record},
                }),
                encoding="utf-8",
            )
            self.assertFalse(
                foundation_materialization_matches_proof_review(
                    state_dir=state,
                    project_path=root,
                    target_rel="QIT/A.lean",
                )
            )
            self.assertTrue(foundation_build_is_dispatchable(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
                max_iterations=2,
            ))
            self.assertFalse(foundation_build_is_dispatchable(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
                max_iterations=1,
            ))
            target.write_text(
                "theorem a : True := by\n  trivial\n", encoding="utf-8",
            )
            self.assertFalse(foundation_materialization_is_current(
                state_dir=state,
                project_path=root,
                target_rel="QIT/A.lean",
            ))

    def test_zero_sorry_foundation_target_bypasses_noop_filter(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by exact True.intro\n",
                encoding="utf-8",
            )
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n"
                "1. **`A.lean`** — build missing foundation. "
                "[prover-mode: mathlib-build]\n",
                encoding="utf-8",
            )
            (state / "proof-review-gate.json").write_text(
                json.dumps({
                    "targets": {
                        "A.lean": {
                            "status": "needs_redraft",
                            "attempts": 1,
                            "redraft_kind": "missing_foundational_bridge",
                            "reason": "missing reusable entropy bridge",
                        },
                    },
                }),
                encoding="utf-8",
            )
            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=lambda *_args, **_kwargs: True,
                review_worker=lambda *_args, **_kwargs: True,
                full_pipeline=True,
                foundation_enabled=True,
                foundation_max_iterations=2,
            )
            with (
                patch.object(runner, "_run_fanout") as run_fanout,
                patch(
                    "archon.commands.loop.prover.runners."
                    "archive_task_results"
                ),
            ):
                runner.run(dry_run=False)

            run_fanout.assert_called_once()
            dispatched = run_fanout.call_args.args[0]
            self.assertEqual(dispatched, [target])


    def test_missing_bridge_builds_foundation_then_resumes_target(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": 2,
                    "max_iterations": 3,
                    "targets": {
                        "A.lean": {
                            "status": "review_exhausted",
                            "reviews": 3,
                            "reason": "old statement Review budget exhausted",
                            "certificate": {"old": True},
                        }
                    },
                }),
                encoding="utf-8",
            )
            prover_calls = 0
            proof_review_calls = 0
            foundation_prompts: list[str] = []
            formalization_prompts: list[str] = []

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_proof_review(spec, **_kwargs):
                nonlocal proof_review_calls
                proof_review_calls += 1
                milestone = (
                    _foundation_redraft_milestone(spec.rel)
                    if proof_review_calls == 1 else _milestone(spec.rel)
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def fake_foundation_builder(*args, **_kwargs):
                foundation_prompts.append(args[0])
                foundation = root / "ArchonFoundations" / "A_Foundation.lean"
                foundation.parent.mkdir(parents=True, exist_ok=True)
                foundation.write_text(
                    "theorem entropyBridge : True := by trivial\n",
                    encoding="utf-8",
                )
                target.write_text(
                    "import ArchonFoundations.A_Foundation\n\n"
                    "theorem a : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Foundation\n\nBuilt `entropyBridge`; #print axioms clean.\n",
                    encoding="utf-8",
                )
                return True

            def fake_formalization_review(spec, **_kwargs):
                formalization_prompts.append(spec.prompt)
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel, passed=True),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_proof_review,
                formalizer_worker=fake_foundation_builder,
                formalization_review_worker=fake_formalization_review,
                max_parallel=1,
                full_pipeline=True,
                formalization_max_iterations=3,
                foundation_enabled=True,
                foundation_max_iterations=2,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(prover_calls, 2)
            self.assertEqual(proof_review_calls, 2)
            self.assertEqual(len(foundation_prompts), 1)
            self.assertEqual(len(formalization_prompts), 1)
            self.assertIn("missing entropy bridge", foundation_prompts[0])
            self.assertIn(
                "no local strong-subadditivity eliminator",
                foundation_prompts[0],
            )
            self.assertIn("ArchonFoundations/A_Foundation.lean", foundation_prompts[0])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["foundation_builds"]["requested"], 1)
            self.assertEqual(report["foundation_builds"]["materialized"], 1)
            foundation_gate = json.loads(
                (state / "foundation-build-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                foundation_gate["targets"]["A.lean"]["status"],
                "materialized",
            )
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            formalization_record = formalization_gate["targets"]["A.lean"]
            self.assertEqual(formalization_record["status"], "passed")
            self.assertEqual(formalization_record["reviews"], 1)
            self.assertEqual(
                formalization_record["budget_reset_history"][-1][
                    "previous_reviews"
                ],
                3,
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["status"], "solved")
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)

    def test_foundation_exhaustion_does_not_consume_review_budget(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            (state / "formalization-review-gate.json").write_text(
                json.dumps({
                    "version": 2,
                    "max_iterations": 3,
                    "targets": {"A.lean": {
                        "status": "review_exhausted",
                        "reviews": 3,
                        "reason": "old budget exhausted",
                    }},
                }),
                encoding="utf-8",
            )
            foundation_calls = 0

            def fake_builder(*_args, **_kwargs):
                nonlocal foundation_calls
                foundation_calls += 1
                foundation = root / "ArchonFoundations" / "A_Foundation.lean"
                foundation.parent.mkdir(parents=True, exist_ok=True)
                foundation.write_text(
                    "axiom fraudulentBridge : True\n",
                    encoding="utf-8",
                )
                if foundation_calls == 1:
                    target.write_text(
                        "import ArchonFoundations.A_Foundation\n\n"
                        "theorem a : True := by sorry\n",
                        encoding="utf-8",
                    )
                (state / "task_results" / "A.lean.md").write_text(
                    f"# Invalid foundation attempt {foundation_calls}\n",
                    encoding="utf-8",
                )
                return True

            def fake_review(spec, **_kwargs):
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_foundation_redraft_milestone(spec.rel),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=lambda *_args, **_kwargs: True,
                review_worker=fake_review,
                formalizer_worker=fake_builder,
                max_parallel=1,
                full_pipeline=True,
                foundation_enabled=True,
                foundation_max_iterations=2,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(foundation_calls, 2)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["foundation_builds"]["failed"], 2)
            history = report["foundation_builds"]["history"]["A.lean"]
            first_attempt = history[0]
            second_attempt = history[1]
            self.assertEqual(first_attempt["forbidden_declarations"][0]["line"], 1)
            self.assertFalse(second_attempt["attempt_target_changed"])
            self.assertTrue(second_attempt["target_changed"])
            gate = json.loads(
                (state / "foundation-build-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                gate["targets"]["A.lean"]["status"],
                "foundation_exhausted",
            )
            form_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(form_gate["targets"]["A.lean"]["reviews"], 3)

    def test_prover_phase_enables_lifecycle_from_autoformalize(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            iter_dir.mkdir(parents=True)
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "pipeline_target_review": True,
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                    "pipeline_foundation_build": True,
                    "pipeline_foundation_build_max_iterations": 7,
                    "pipeline_foundation_root": "QITFoundations",
                }
            }), encoding="utf-8")
            captured: dict = {}

            class FakeRunner:
                def __init__(self, **kwargs):
                    captured.update(kwargs)

                def run(self, *, dry_run: bool):
                    captured["dry_run"] = dry_run

            options = SimpleNamespace(
                no_review=False,
                proof_review_gate=True,
                formalization_review_gate=True,
                formalization_review_max_iterations=3,
                proof_review_max_iterations=3,
                max_parallel=28,
                max_objectives=28,
                block_on_blocked_deps=False,
                debug_feedback=False,
            )
            ctx = SimpleNamespace(
                project_name="project",
                project_path=root,
                state_dir=state,
                current_stage="autoformalize",
                iter_dir=iter_dir,
                iter_meta=iter_dir / "meta.json",
                iter_num=1,
                options=options,
                verbose_logs=False,
                model="test",
                dashboard_url=None,
                blueprint_url=None,
                backend=None,
                resume_phase=None,
                dry_run=False,
                harness_descriptor_for=lambda _role: None,
            )
            with patch(
                "archon.commands.loop.phases.prover.ParallelProverRunner",
                FakeRunner,
            ):
                ProverPhase(ctx)._run_parallel()

            pipeline = captured["pipeline_review"]
            self.assertIsNotNone(pipeline)
            self.assertTrue(pipeline.formalization_review_enabled)
            self.assertTrue(pipeline.foundation_build_enabled)
            self.assertEqual(pipeline.foundation_build_max_iterations, 7)
            self.assertEqual(pipeline.foundation_root, "QITFoundations")
            self.assertEqual(captured["stage"], "autoformalize")
            self.assertEqual(captured["max_parallel"], 28)
            self.assertFalse(captured["dry_run"])

    def test_autoformalize_targets_run_independent_full_lifecycles(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            targets = {name: root / f"{name}.lean" for name in ("A", "B")}
            for name, target in targets.items():
                target.write_text(
                    f"theorem {name.lower()} : True := by sorry\n",
                    encoding="utf-8",
                )

            proof_review_a_started = threading.Event()
            lock = threading.Lock()
            order: list[str] = []
            stage_calls = {
                name: {"formalizer": 0, "formalization_review": 0,
                       "prover": 0, "proof_review": 0}
                for name in targets
            }

            def record(event: str) -> None:
                with lock:
                    order.append(event)

            def fake_formalizer(*args, **_kwargs):
                name = Path(args[2]).name
                stage_calls[name]["formalizer"] += 1
                record(f"formalizer-{name}:start")
                if name == "B":
                    self.assertTrue(proof_review_a_started.wait(timeout=5))
                targets[name].write_text(
                    f"theorem {name.lower()} (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / f"{name}.lean.md").write_text(
                    f"# Formalization {name}\n", encoding="utf-8",
                )
                record(f"formalizer-{name}:end")
                return True

            def fake_formalization_review(spec, **_kwargs):
                name = Path(spec.rel).stem
                stage_calls[name]["formalization_review"] += 1
                record(f"formalization-review-{name}")
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel),
                )

            def fake_prover(*args, **_kwargs):
                name = Path(args[2]).name
                stage_calls[name]["prover"] += 1
                record(f"prover-{name}")
                return True

            def fake_proof_review(spec, **_kwargs):
                name = Path(spec.rel).stem
                stage_calls[name]["proof_review"] += 1
                record(f"proof-review-{name}")
                if name == "A":
                    proof_review_a_started.set()
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_proof_review,
                formalizer_worker=fake_formalizer,
                formalization_review_worker=fake_formalization_review,
                max_parallel=2,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout(list(targets.values()), file_modes={})

            self.assertLess(
                order.index("proof-review-A"),
                order.index("formalizer-B:end"),
            )
            for calls in stage_calls.values():
                self.assertEqual(calls, {
                    "formalizer": 1,
                    "formalization_review": 1,
                    "prover": 1,
                    "proof_review": 1,
                })
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["pipeline_mode"], "target_lifecycle")
            self.assertEqual(report["starts_at"], "formalizer")
            self.assertEqual(report["settled_target_files"], ["A.lean", "B.lean"])
            self.assertEqual(
                report["proof_review_target_files"], ["A.lean", "B.lean"]
            )
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            for rel in ("A.lean", "B.lean"):
                self.assertEqual(
                    formalization_gate["targets"][rel]["status"], "passed"
                )
                self.assertEqual(proof_gate["targets"][rel]["status"], "solved")

    def test_zero_sorry_formalization_still_runs_proof_verifier_with_proof_mode(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            modes = state / "prover-modes"
            modes.mkdir()
            (modes / "physics-formalize.md").write_text(
                "# Physics formalization\n", encoding="utf-8",
            )
            (modes / "physics.md").write_text(
                "# Physics proof\n", encoding="utf-8",
            )
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            prover_calls = 0
            prompt_routes: list[tuple[str, str | None]] = []

            def fake_formalizer(*_args, **_kwargs):
                target.write_text(
                    "theorem a : True := by trivial\n", encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Formalization\n", encoding="utf-8",
                )
                return True

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_prompt(*args, **kwargs):
                prompt_routes.append((args[3], kwargs.get("mode_name")))
                return "work"

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=_process_review,
                formalizer_worker=fake_formalizer,
                max_parallel=1,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    side_effect=fake_prompt,
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout(
                    [target],
                    file_modes={str(target): "physics-formalize"},
                )

            self.assertEqual(prover_calls, 1)
            self.assertEqual(prompt_routes, [
                ("autoformalize", "physics-formalize"),
                ("prover", "physics"),
            ])
            meta = json.loads(
                (iter_dir / "meta.json").read_text(encoding="utf-8")
            )
            self.assertEqual(meta["provers"]["A"]["stage"], "prover")
            self.assertEqual(meta["provers"]["A"]["mode"], "physics")

    def test_autoformalize_exhaustion_settles_without_fake_proof_review(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            formalizer_calls = 0
            prover_calls = 0
            proof_review_calls = 0

            def fake_formalizer(*_args, **_kwargs):
                nonlocal formalizer_calls
                formalizer_calls += 1
                target.write_text(
                    f"theorem a (h_{formalizer_calls} : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    f"# Attempt {formalizer_calls}\n", encoding="utf-8",
                )
                return True

            def fake_formalization_review(spec, **_kwargs):
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel, passed=False),
                )

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_proof_review(spec, **_kwargs):
                nonlocal proof_review_calls
                proof_review_calls += 1
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_proof_review,
                formalizer_worker=fake_formalizer,
                formalization_review_worker=fake_formalization_review,
                max_parallel=1,
                full_pipeline=True,
                formalization_max_iterations=2,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(formalizer_calls, 2)
            self.assertEqual(prover_calls, 0)
            self.assertEqual(proof_review_calls, 0)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["settled_target_files"], ["A.lean"])
            self.assertEqual(report["proof_review_target_files"], [])
            loaded, error = load_pipelined_review_report(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                objectives=[target],
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(loaded)
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                formalization_gate["targets"]["A.lean"]["status"],
                "review_exhausted",
            )

    def test_full_target_loop_retries_proof_before_finishing_lane(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")
            prover_calls = 0
            review_calls = 0

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_review(spec, **_kwargs):
                nonlocal review_calls
                review_calls += 1
                milestone = (
                    _retry_proof_milestone(spec.rel)
                    if review_calls == 1 else _milestone(spec.rel)
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_review,
                max_parallel=1,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(prover_calls, 2)
            self.assertEqual(review_calls, 2)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                [event["route"] for event in report["gate_events"]],
                ["retry_proof", "solved"],
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["status"], "solved")
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 2)

    def test_resume_reviews_done_lane_without_rerunning_zero_sorry_prover(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            done_target = root / "A.lean"
            live_target = root / "B.lean"
            done_target.write_text(
                "theorem a : True := by trivial\n", encoding="utf-8",
            )
            live_target.write_text(
                "theorem b : True := by sorry\n", encoding="utf-8",
            )
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`** — done lane.\n"
                "- **`B.lean`** — interrupted lane.\n",
                encoding="utf-8",
            )
            (iter_dir / "meta.json").write_text(json.dumps({
                "provers": {
                    "A": {"status": "done"},
                    "B": {"status": "running"},
                }
            }), encoding="utf-8")
            prover_targets: list[str] = []
            reviewed: list[str] = []

            def fake_prover(*args, **_kwargs):
                prover_targets.append(Path(args[2]).name)
                return True

            def fake_review(spec, **_kwargs):
                reviewed.append(spec.rel)
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=fake_prover,
                review_worker=fake_review,
                resume_enabled=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners.build_parallel_prover_prompt",
                    return_value="prove",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner.run(dry_run=False)

            self.assertEqual(prover_targets, ["B"])
            self.assertEqual(sorted(reviewed), ["A.lean", "B.lean"])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["target_files"], ["A.lean", "B.lean"])

    def test_review_phase_recovers_incomplete_lifecycle_without_batch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by trivial\n", encoding="utf-8"
            )
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n- **`A.lean`** — recover.\n",
                encoding="utf-8",
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                    "pipeline_target_review": True,
                }
            }), encoding="utf-8")
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            (iter_dir / "pipelined-review.json").write_text(
                "{}\n", encoding="utf-8"
            )
            checkpoint = {
                "iteration": 1,
                "complete": False,
                "pipeline_mode": "target_lifecycle",
                "starts_at": "prover",
                "target_files": ["A.lean"],
                "targets": 1,
                "reviewed": 0,
                "unresolved": ["A.lean"],
            }
            complete = {
                **checkpoint,
                "complete": True,
                "settled_target_files": ["A.lean"],
                "proof_review_target_files": ["A.lean"],
                "reviewed": 1,
                "unresolved": [],
                "preflight": {
                    "jobs": 1,
                    "duration_secs": 0.01,
                    "summary": {"total": 1, "passed": 1, "failed": 0},
                    "targets": [],
                },
                "gate_events_applied": True,
                "proof_gate_result": {
                    "solved": ["A.lean"],
                    "retry": [],
                    "needs_redraft": [],
                    "blocked_infrastructure": [],
                    "exhausted": [],
                    "reviewed": ["A.lean"],
                },
                "formalization_gate_result": {
                    "passed": [],
                    "retry": [],
                    "exhausted": [],
                    "reviewed": [],
                },
                "proof_redrafts_reopened": [],
                "pending_formalization_targets": [],
            }
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=True,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=2,
                ),
                current_stage="prover",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=iter_dir / "meta.json",
                iter_dir=iter_dir,
                iter_num=1,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_parallel_target_review = (
                lambda *_args, **_kwargs: self.fail(
                    "normal target Review batch was invoked"
                )
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            phase._run_physics_doctor_gate = lambda: ([], False)
            with (
                patch(
                    "archon.commands.loop.phases.review."
                    "load_pipelined_review_report",
                    side_effect=[
                        (None, "pipelined Review report is incomplete"),
                        (checkpoint, ""),
                        (complete, ""),
                    ],
                ) as load_report,
                patch.object(
                    ProverPhase, "resume_incomplete_pipeline", autospec=True,
                ) as resume_pipeline,
                patch("archon.commands.loop.phases.review.commit_phase"),
                patch(
                    "archon.commands.loop.phases.review."
                    "check_mandatory_dispatched"
                ),
            ):
                phase.run()

            self.assertEqual(load_report.call_count, 3)
            resume_pipeline.assert_called_once()
            self.assertEqual(
                resume_pipeline.call_args.kwargs["starts_at"], "prover"
            )
            metadata = json.loads(
                (iter_dir / "meta.json").read_text(encoding="utf-8")
            )
            self.assertTrue(metadata["review"]["pipelineTargetConsumed"])

    def test_review_phase_consumes_autoformalize_lifecycle_once(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            session_dir = state / "proof-journal" / "sessions" / "session_1"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by trivial\n", encoding="utf-8")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nautoformalize\n\n"
                "## Stages\n\n- autoformalize\n- prover\n\n"
                "## Current Objectives\n\n- **`A.lean`** — lifecycle.\n",
                encoding="utf-8",
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                    "pipeline_target_review": True,
                }
            }), encoding="utf-8")
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n", encoding="utf-8")
            formalization_milestone = _formalization_milestone("A.lean")
            proof_outcome = TargetReviewOutcome(
                rel="A.lean",
                attempt=1,
                runner_ok=True,
                milestone=_milestone("A.lean"),
            )
            apply_target_formalization_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=formalization_milestone,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:formalization:1",
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=proof_outcome.milestone,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            write_parallel_review_session(
                session_dir=session_dir,
                iter_num=1,
                outcomes={"A.lean": proof_outcome},
            )
            write_pipelined_review_report(
                iter_dir=iter_dir,
                report={
                    "iteration": 1,
                    "complete": True,
                    "pipeline_mode": "target_lifecycle",
                    "starts_at": "formalizer",
                    "target_files": ["A.lean"],
                    "settled_target_files": ["A.lean"],
                    "proof_review_target_files": ["A.lean"],
                    "targets": 1,
                    "reviewed": 1,
                    "unresolved": [],
                    "preflight": {
                        "jobs": 1,
                        "duration_secs": 0.01,
                        "summary": {"total": 1, "passed": 1, "failed": 0},
                        "targets": [_preflight(
                            project_path=root, target=target, timeout_sec=30,
                        )],
                    },
                    "gate_events_applied": True,
                    "gate_events": [
                        {
                            "kind": "formalization",
                            "event_id": "pipeline:1:A.lean:formalization:1",
                            "file": "A.lean",
                            "cycle": 1,
                            "decision": "passed",
                        },
                        {
                            "kind": "proof",
                            "event_id": "pipeline:1:A.lean:proof:1",
                            "file": "A.lean",
                            "cycle": 1,
                            "route": "solved",
                        },
                    ],
                    "proof_gate_result": {
                        "solved": ["A.lean"],
                        "retry": [],
                        "needs_redraft": [],
                        "blocked_infrastructure": [],
                        "exhausted": [],
                        "reviewed": ["A.lean"],
                    },
                    "formalization_gate_result": {
                        "passed": ["A.lean"],
                        "retry": [],
                        "exhausted": [],
                        "reviewed": ["A.lean"],
                    },
                    "proof_redrafts_reopened": [],
                    "pending_formalization_targets": [],
                },
            )
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=True,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=2,
                ),
                current_stage="autoformalize",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=meta,
                iter_dir=iter_dir,
                iter_num=1,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_parallel_formalization_review = (
                lambda *_args, **_kwargs: self.fail(
                    "formalization verdicts were reviewed twice"
                )
            )
            phase._invoke_parallel_target_review = (
                lambda *_args, **_kwargs: self.fail(
                    "proof verdicts were reviewed twice"
                )
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            phase._run_physics_doctor_gate = lambda: ([], False)
            with (
                patch(
                    "archon.commands.loop.phases.review."
                    "run_parallel_review_preflight"
                ) as preflight,
                patch("archon.commands.loop.phases.review.commit_phase"),
                patch(
                    "archon.commands.loop.phases.review."
                    "check_mandatory_dispatched"
                ),
            ):
                phase.run()

            preflight.assert_not_called()
            self.assertEqual(ctx.current_stage, "prover")
            progress_text = progress.read_text(encoding="utf-8")
            self.assertIn("selected target lifecycles are settled", progress_text)
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                formalization_gate["targets"]["A.lean"]["reviews"], 1
            )
            self.assertEqual(proof_gate["targets"]["A.lean"]["attempts"], 1)
            metadata = json.loads(meta.read_text(encoding="utf-8"))
            self.assertTrue(metadata["review"]["pipelineTargetConsumed"])
            self.assertTrue(metadata["review"]["pipelineGateEventsConsumed"])

    def test_review_phase_consumes_pipeline_once(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            session_dir = state / "proof-journal" / "sessions" / "session_1"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by trivial\n", encoding="utf-8")
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n- **`A.lean`** — review.\n",
                encoding="utf-8",
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "pipeline_target_review": True,
                }
            }), encoding="utf-8")
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n", encoding="utf-8")
            outcome = TargetReviewOutcome(
                rel="A.lean",
                attempt=1,
                runner_ok=True,
                milestone=_milestone("A.lean"),
            )
            write_parallel_review_session(
                session_dir=session_dir,
                iter_num=1,
                outcomes={"A.lean": outcome},
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=outcome.milestone,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            write_pipelined_review_report(
                iter_dir=iter_dir,
                report={
                    "iteration": 1,
                    "complete": True,
                    "target_files": ["A.lean"],
                    "targets": 1,
                    "reviewed": 1,
                    "unresolved": [],
                    "preflight": {
                        "jobs": 1,
                        "duration_secs": 0.01,
                        "summary": {"total": 1, "passed": 1, "failed": 0},
                        "targets": [_preflight(
                            project_path=root, target=target, timeout_sec=30,
                        )],
                    },
                    "gate_events_applied": True,
                    "gate_events": [{
                        "kind": "proof",
                        "event_id": "pipeline:1:A.lean:proof:1",
                        "file": "A.lean",
                        "cycle": 1,
                        "route": "solved",
                    }],
                    "proof_gate_result": {
                        "solved": ["A.lean"],
                        "retry": [],
                        "needs_redraft": [],
                        "blocked_infrastructure": [],
                        "exhausted": [],
                        "reviewed": ["A.lean"],
                    },
                    "proof_redrafts_reopened": [],
                    "pending_formalization_targets": [],
                },
            )
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=False,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=2,
                ),
                current_stage="prover",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=meta,
                iter_dir=iter_dir,
                iter_num=1,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_parallel_target_review = lambda *_args, **_kwargs: (
                self.fail("pipelined verdicts were reviewed twice")
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            phase._run_physics_doctor_gate = lambda: ([], False)
            with (
                patch(
                    "archon.commands.loop.phases.review.run_parallel_review_preflight"
                ) as preflight,
                patch("archon.commands.loop.phases.review.commit_phase"),
                patch(
                    "archon.commands.loop.phases.review.check_mandatory_dispatched"
                ),
            ):
                phase.run()

            preflight.assert_not_called()
            gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(gate["targets"]["A.lean"]["status"], "solved")
            self.assertEqual(gate["targets"]["A.lean"]["attempts"], 1)
            metadata = json.loads(meta.read_text(encoding="utf-8"))
            self.assertTrue(metadata["review"]["pipelineTargetConsumed"])
            self.assertEqual(len(gate["targets"]["A.lean"]["history"]), 1)
            self.assertTrue(metadata["review"]["pipelineGateEventsConsumed"])

    def test_materialized_redraft_is_reopened_but_not_formalized_twice(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            session_dir = state / "proof-journal" / "sessions" / "session_1"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text(
                "theorem a (h_law : True) : True := by sorry\n",
                encoding="utf-8",
            )
            digest = hashlib.sha256(target.read_bytes()).hexdigest()
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Stages\n\n- autoformalize\n- prover\n\n"
                "## Current Objectives\n\n- **`A.lean`** — review.\n",
                encoding="utf-8",
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "pipeline_target_review": True,
                }
            }), encoding="utf-8")
            meta = iter_dir / "meta.json"
            meta.write_text("{}\n", encoding="utf-8")
            outcome = TargetReviewOutcome(
                rel="A.lean",
                attempt=1,
                runner_ok=True,
                milestone=_redraft_milestone("A.lean"),
            )
            write_parallel_review_session(
                session_dir=session_dir,
                iter_num=1,
                outcomes={"A.lean": outcome},
            )
            preflight_row = _preflight(
                project_path=root, target=target, timeout_sec=30,
            )
            task_results = state / "task_results"
            task_results.mkdir()
            task_result = task_results / "A.lean.md"
            task_result.write_text("# Redraft evidence\n", encoding="utf-8")
            task_result_digest = hashlib.sha256(
                task_result.read_bytes()
            ).hexdigest()
            handoff = {
                "iteration": 1,
                "file": "A.lean",
                "status": "materialized",
                "review_attempt": 1,
                "runner_ok": True,
                "baseline_sha256": "0" * 64,
                "lean_sha256": digest,
                "changed": True,
                "task_result_updated": True,
                "task_result_fingerprints": {
                    str(task_result): task_result_digest,
                },
                "preflight": preflight_row,
                "error": "",
            }
            write_pipelined_review_report(
                iter_dir=iter_dir,
                report={
                    "iteration": 1,
                    "complete": True,
                    "target_files": ["A.lean"],
                    "targets": 1,
                    "reviewed": 1,
                    "unresolved": [],
                    "preflight": {
                        "jobs": 1,
                        "duration_secs": 0.01,
                        "summary": {"total": 1, "passed": 1, "failed": 0},
                        "targets": [preflight_row],
                    },
                    "formalization_handoffs": {"A.lean": handoff},
                },
            )
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=False,
                    formalization_review_max_iterations=3,
                    proof_review_gate=True,
                    proof_review_max_iterations=3,
                    no_review=False,
                    max_parallel=2,
                ),
                current_stage="prover",
                progress_file=progress,
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=meta,
                iter_dir=iter_dir,
                iter_num=1,
                dashboard_url=None,
            )
            phase = ReviewPhase(ctx)
            phase._invoke_parallel_target_review = lambda *_args, **_kwargs: (
                self.fail("pipelined verdicts were reviewed twice")
            )
            phase._invoke_review = lambda: self.fail("serial Review was invoked")
            phase._run_physics_doctor_gate = lambda: ([], False)
            with (
                patch("archon.commands.loop.phases.review.commit_phase"),
                patch(
                    "archon.commands.loop.phases.review.check_mandatory_dispatched"
                ),
            ):
                phase.run()

            formal_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            record = formal_gate["targets"]["A.lean"]
            self.assertEqual(record["status"], "retry")
            self.assertEqual(
                record["materialized_redraft"]["status"], "ready_for_review"
            )
            self.assertEqual(record["materialized_redraft"]["lean_sha256"], digest)
            self.assertIn("autoformalize", progress.read_text(encoding="utf-8"))

            next_iter = state / "logs" / "iter-002"
            next_iter.mkdir()
            (next_iter / "meta.json").write_text("{}\n", encoding="utf-8")
            runner = ParallelProverRunner(
                project_name="project",
                project_path=root,
                state_dir=state,
                stage="autoformalize",
                iter_dir=next_iter,
                iter_meta=next_iter / "meta.json",
                iter_num=2,
                max_parallel=2,
                max_objectives=10,
                block_on_blocked_deps=False,
                verbose_logs=False,
                model="test",
                prover_worker=lambda *_args, **_kwargs: self.fail(
                    "materialized redraft was formalized twice"
                ),
            )
            with patch(
                "archon.commands.loop.prover.runners.archive_task_results"
            ) as archive:
                runner.run(dry_run=False)
            archive.assert_not_called()
            self.assertIn("A.lean", progress.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
