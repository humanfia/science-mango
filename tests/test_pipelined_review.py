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

from archon.agent import QuotaExhaustedError
from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    apply_target_formalization_review,
    reopen_formalization_targets,
)
from archon.commands.loop.parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewOutcome,
    load_target_milestone,
    load_pipelined_review_report,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from archon.commands.loop.phases.prover import ProverPhase
from archon.commands.loop.phases.review import ReviewPhase
from archon.commands.loop.proof_review_gate import apply_target_proof_review
from archon.commands.loop.prover.runners import (
    ParallelProverRunner,
    _ImmediateRedraftPromptError,
    _answer_submission_repair_handoff,
    _pipeline_cycle,
)
from archon.commands.loop.problem_only_review_contract import (
    ProblemOnlyReviewContractError,
)


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


def _validated_review_outcome(spec, row: dict) -> TargetReviewOutcome:
    output_dir = Path(spec.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    milestone_path = output_dir / "milestones.jsonl"
    milestone_path.write_text(
        json.dumps(row) + "\n", encoding="utf-8",
    )
    milestone, error = load_target_milestone(
        milestone_path,
        spec.rel,
        final_attempt=spec.final_attempt,
    )
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=True,
        milestone=milestone,
        error=error,
    )


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
        "numeric_reporting": {
            "active": False,
            "status": "not_applicable",
            "reason": "domain profile is not chemistry-native",
        },
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
        stage: str = "prover",
        iter_num: int = 1,
    ) -> ParallelProverRunner:
        return ParallelProverRunner(
            project_name="project",
            project_path=root,
            state_dir=state,
            stage=stage,
            iter_dir=iter_dir,
            iter_meta=iter_dir / "meta.json",
            iter_num=iter_num,
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
            ),
            executor_factory=executor_factory,
            prover_worker=prover_worker,
            review_worker=review_worker,
            formalization_review_worker=formalization_review_worker,
            formalizer_worker=formalizer_worker,
            preflight_checker=_preflight,
        )

    def _run_initial_delivery_case(
        self,
        *,
        root: Path,
        state: Path,
        iter_dir: Path,
        target: Path,
        formalizer_worker,
        resume_enabled: bool = False,
        resume_session_id: str | None = None,
    ) -> tuple[dict, dict, dict[str, int]]:
        runner = self._runner(
            root=root,
            state=state,
            iter_dir=iter_dir,
            prover_worker=_process_prover,
            review_worker=_process_review,
            formalizer_worker=formalizer_worker,
            formalization_review_worker=_process_formalization_review,
            max_parallel=1,
            full_pipeline=True,
            stage="autoformalize",
            resume_enabled=resume_enabled,
        )
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "native_problem_only_enabled",
                return_value=False,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="CONTRACT",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "resolve_target_review_source_contract",
                return_value=None,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_target_formalization_review_prompt",
                return_value="formal-review",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_target_review_prompt",
                return_value="proof-review",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="work",
            ),
            patch(
                "archon.commands.loop.prover.runners.snapshot_baseline"
            ) as snapshot,
            patch(
                "archon.commands.loop.prover.runners.pick_resume_session",
                return_value=resume_session_id,
            ) as pick_resume,
            patch(
                "archon.commands.loop.prover.runners.persist_session_id"
            ),
        ):
            runner._run_fanout([target], file_modes={})
        report = json.loads(
            (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
        )
        meta = json.loads(
            (iter_dir / "meta.json").read_text(encoding="utf-8")
        )
        return report, meta, {
            "formalizer_pick_resume": sum(
                len(call.args) > 1
                and str(call.args[1]).startswith("pipelineFormalizers.")
                for call in pick_resume.call_args_list
            ),
            "formalizer_snapshot": sum(
                len(call.args) > 1
                and "formalizer-snapshots" in str(call.args[1])
                for call in snapshot.call_args_list
            ),
        }

    def test_resume_enabled_without_session_gets_fresh_delivery_retry(
        self,
    ):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            calls = 0
            resume_session_ids: list[str | None] = []

            def formalizer(*args, **_kwargs):
                nonlocal calls
                calls += 1
                resume_session_ids.append(args[7])
                if calls == 1:
                    return False
                target.write_text(
                    "theorem a (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Complete delivery\n", encoding="utf-8",
                )
                return True

            report, meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=formalizer,
                resume_enabled=True,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(calls, 2)
            self.assertEqual(resume_session_ids, [None, None])
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 1,
                "formalizer_snapshot": 1,
            })
            history = report["formalizer_history"]["A.lean"]
            self.assertEqual(
                [row["delivery_attempt"] for row in history], [1, 2]
            )
            self.assertEqual([row["cycle"] for row in history], [1, 1])
            self.assertEqual(
                [row["status"] for row in history],
                ["error", "materialized"],
            )
            self.assertEqual(
                [row["runner_ok"] for row in history], [False, True]
            )
            self.assertEqual(
                history[0]["baseline_sha256"],
                history[1]["baseline_sha256"],
            )
            self.assertEqual(
                meta["pipelineFormalizers"]["A"]["deliveryAttempt"], 2
            )

    def test_initial_delivery_retry_keeps_original_lean_and_result_baseline(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            calls = 0

            def formalizer(*_args, **_kwargs):
                nonlocal calls
                calls += 1
                if calls == 1:
                    target.write_text(
                        "theorem a (h_law : True) : True := by sorry\n",
                        encoding="utf-8",
                    )
                else:
                    (state / "task_results" / "A.lean.md").write_text(
                        "# Sidecar completed\n", encoding="utf-8",
                    )
                return True

            report, _meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=formalizer,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(calls, 2)
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 1,
                "formalizer_snapshot": 1,
            })
            history = report["formalizer_history"]["A.lean"]
            self.assertEqual(
                [row["delivery_attempt"] for row in history], [1, 2]
            )
            self.assertEqual([row["cycle"] for row in history], [1, 1])
            self.assertTrue(history[0]["changed"])
            self.assertFalse(history[0]["task_result_updated"])
            self.assertTrue(history[1]["changed"])
            self.assertTrue(history[1]["task_result_updated"])
            self.assertEqual(
                history[0]["baseline_sha256"],
                history[1]["baseline_sha256"],
            )
            self.assertEqual(
                history[0]["review_attempt"],
                history[1]["review_attempt"],
            )

    def test_initial_delivery_retry_is_bounded_after_two_failures(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            calls = 0
            resume_session_ids: list[str | None] = []

            def formalizer(*args, **_kwargs):
                nonlocal calls
                calls += 1
                resume_session_ids.append(args[7])
                return False

            report, meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=formalizer,
            )

            self.assertFalse(report["complete"])
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertEqual(report["pending_formalization_targets"], ["A.lean"])
            self.assertEqual(calls, 2)
            self.assertEqual(resume_session_ids, [None, None])
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 1,
                "formalizer_snapshot": 1,
            })
            self.assertEqual(report["formalizers"], {
                "requested": 2,
                "materialized": 0,
                "failed": 2,
            })
            history = report["formalizer_history"]["A.lean"]
            self.assertEqual(
                [row["delivery_attempt"] for row in history], [1, 2]
            )
            self.assertEqual([row["cycle"] for row in history], [1, 1])
            self.assertTrue(all(
                "formalizer runner did not complete" in row["error"]
                for row in history
            ))
            self.assertEqual(
                meta["pipelineFormalizers"]["A"]["deliveryAttempt"], 2
            )
            self.assertEqual(
                meta["pipelineFormalizers"]["A"]["status"], "error"
            )

    def test_delivery_retry_resume_uses_original_partial_baseline(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            task_results = state / "task_results"
            task_results.mkdir()
            target = root / "A.lean"
            original = b"theorem a : True := by sorry\n"
            target.write_bytes(original)
            original_sha256 = hashlib.sha256(original).hexdigest()
            task_result = task_results / "A.lean.md"
            original_result = b"# Initial result\n"
            task_result.write_bytes(original_result)
            original_result_sha256 = hashlib.sha256(
                original_result
            ).hexdigest()
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {
                        "status": "error",
                        "cycle": 1,
                        "deliveryAttempt": 1,
                        "sessionId": "attempt-1-session",
                        "baselineSha256": original_sha256,
                        "baselineTaskResultFingerprints": {
                            str(task_result): original_result_sha256,
                        },
                    },
                },
            }), encoding="utf-8")
            target.write_text(
                "theorem a (h_partial : True) : True := by sorry\n",
                encoding="utf-8",
            )
            resume_session_ids: list[str | None] = []

            def formalizer(*args, **_kwargs):
                resume_session_ids.append(args[7])
                task_result.write_text(
                    "# Completed result\n", encoding="utf-8",
                )
                return True

            report, meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=formalizer,
                resume_enabled=True,
                resume_session_id="attempt-1-session",
            )

            self.assertTrue(report["complete"])
            self.assertEqual(resume_session_ids, [None])
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 0,
                "formalizer_snapshot": 0,
            })
            history = report["formalizer_history"]["A.lean"]
            self.assertEqual(len(history), 1)
            self.assertEqual(history[0]["delivery_attempt"], 2)
            self.assertEqual(history[0]["baseline_sha256"], original_sha256)
            self.assertTrue(history[0]["changed"])
            self.assertTrue(history[0]["task_result_updated"])
            persisted = meta["pipelineFormalizers"]["A"]
            self.assertEqual(persisted["deliveryAttempt"], 2)
            self.assertEqual(persisted["baselineSha256"], original_sha256)
            self.assertEqual(
                persisted["baselineTaskResultFingerprints"],
                {str(task_result): original_result_sha256},
            )

    def test_delivery_retry_budget_survives_controller_abort(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            calls = 0
            resume_session_ids: list[str | None] = []

            def interrupted_formalizer(*args, **_kwargs):
                nonlocal calls
                calls += 1
                resume_session_ids.append(args[7])
                if calls == 1:
                    return False
                raise QuotaExhaustedError("simulated controller abort")

            with self.assertRaises(QuotaExhaustedError):
                self._run_initial_delivery_case(
                    root=root,
                    state=state,
                    iter_dir=iter_dir,
                    target=target,
                    formalizer_worker=interrupted_formalizer,
                    resume_enabled=True,
                )

            interrupted_meta = json.loads(
                (iter_dir / "meta.json").read_text(encoding="utf-8")
            )["pipelineFormalizers"]["A"]
            self.assertEqual(calls, 2)
            self.assertEqual(resume_session_ids, [None, None])
            self.assertEqual(interrupted_meta["deliveryAttempt"], 2)
            self.assertEqual(interrupted_meta["status"], "running")
            self.assertIn(
                "baselineTaskResultFingerprints", interrupted_meta,
            )
            calls_after_restart = 0

            def forbidden_formalizer(*_args, **_kwargs):
                nonlocal calls_after_restart
                calls_after_restart += 1
                return False

            report, meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=forbidden_formalizer,
                resume_enabled=True,
            )

            self.assertEqual(calls_after_restart, 0)
            self.assertFalse(report["complete"])
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertEqual(
                report["pending_formalization_targets"], ["A.lean"]
            )
            self.assertEqual(report["formalizers"]["requested"], 0)
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 0,
                "formalizer_snapshot": 0,
            })
            exhausted = meta["pipelineFormalizers"]["A"]
            self.assertEqual(exhausted["deliveryAttempt"], 2)
            self.assertEqual(exhausted["status"], "error")

    def test_initial_delivery_attempt_one_keeps_durable_session_resume(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            task_results = state / "task_results"
            task_results.mkdir()
            target = root / "A.lean"
            original = b"theorem a : True := by sorry\n"
            target.write_bytes(original)
            original_sha256 = hashlib.sha256(original).hexdigest()
            task_result = task_results / "A.lean.md"
            initial_result = b"# Initial result\n"
            task_result.write_bytes(initial_result)
            initial_result_sha256 = hashlib.sha256(
                initial_result
            ).hexdigest()
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {
                        "status": "running",
                        "cycle": 1,
                        "deliveryAttempt": 1,
                        "sessionId": "durable-session",
                        "baselineSha256": original_sha256,
                        "baselineTaskResultFingerprints": {
                            str(task_result): initial_result_sha256,
                        },
                    },
                },
            }), encoding="utf-8")
            resume_session_ids: list[str | None] = []

            def formalizer(*args, **_kwargs):
                resume_session_ids.append(args[7])
                target.write_text(
                    "theorem a (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                task_result.write_text(
                    "# Completed result\n", encoding="utf-8",
                )
                return True

            report, _meta, patch_calls = self._run_initial_delivery_case(
                root=root,
                state=state,
                iter_dir=iter_dir,
                target=target,
                formalizer_worker=formalizer,
                resume_enabled=True,
                resume_session_id="durable-session",
            )

            self.assertTrue(report["complete"])
            self.assertEqual(resume_session_ids, ["durable-session"])
            self.assertEqual(patch_calls, {
                "formalizer_pick_resume": 1,
                "formalizer_snapshot": 0,
            })
            history = report["formalizer_history"]["A.lean"]
            self.assertEqual(len(history), 1)
            self.assertEqual(history[0]["delivery_attempt"], 1)
            self.assertEqual(history[0]["baseline_sha256"], original_sha256)

    def test_a6_missing_prior_receipt_fails_before_any_worker(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = (
                root
                / "IChO2026Problems"
                / "icho_2026_t1_a6.lean"
            )
            target.parent.mkdir()
            target.write_text(
                "theorem a6 : True := by sorry\n",
                encoding="utf-8",
            )
            worker_calls: list[str] = []

            def forbidden_worker(*_args, **_kwargs):
                worker_calls.append("called")
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=forbidden_worker,
                review_worker=forbidden_worker,
                formalizer_worker=forbidden_worker,
                formalization_review_worker=forbidden_worker,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "native_problem_only_enabled",
                    return_value=True,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_native_formalizer_source_contract",
                    side_effect=ProblemOnlyReviewContractError(
                        "required certified prior-result context is missing"
                    ),
                ) as resolve_contract,
                self.assertRaisesRegex(
                    ProblemOnlyReviewContractError,
                    "required certified prior-result context is missing",
                ),
            ):
                runner._run_pipelined_fanout([target])

            resolve_contract.assert_called_once_with(
                project_path=root,
                target=target,
            )
            self.assertEqual(worker_calls, [])

    def test_pipeline_cycle_parser_is_fail_closed(self):
        cases = (
            (2, 2),
            ("2", 2),
            (True, 0),
            (2.9, 0),
            ("02", 0),
            (" 2", 0),
            ("2.0", 0),
        )
        for value, expected in cases:
            with self.subTest(value=value):
                self.assertEqual(_pipeline_cycle(value), expected)

    def test_preflight_exception_has_numeric_reporting_evidence(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n",
                encoding="utf-8",
            )
            observed: list[dict] = []
            preflight_calls: list[dict] = []

            def failed_preflight(**kwargs):
                preflight_calls.append(kwargs)
                raise RuntimeError("preflight exploded")

            def capture_contract(**kwargs):
                observed.append(kwargs["preflight"])
                return None

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                max_parallel=1,
                max_attempts=1,
            )
            runner.preflight_checker = failed_preflight
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_target_review_source_contract",
                    side_effect=capture_contract,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_target_review_prompt",
                    return_value="review",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
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

            self.assertTrue(observed)
            self.assertEqual(
                observed[0]["numeric_reporting"],
                {
                    "active": False,
                    "status": "error",
                    "reason": "RuntimeError: preflight exploded",
                },
            )
            self.assertEqual(
                observed[0]["diagnostics"],
                "RuntimeError: preflight exploded",
            )

    def test_invalid_native_answer_sidecar_gets_one_bounded_repair(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "problem_item_a.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            prompts: list[str] = []

            def fake_formalizer(prompt, *_args, **_kwargs):
                prompts.append(prompt)
                if len(prompts) == 1:
                    target.write_text(
                        "theorem a (h : True) : True := by sorry\n",
                        encoding="utf-8",
                    )
                    report = (
                        state / "task_results" / "problem_item_a.lean.md"
                    )
                    report.write_text("# materialized\n", encoding="utf-8")
                return True

            raw_error = (
                "target answer submission is invalid: submission "
                "item_a/value.display_value must be a finite decimal or "
                "scientific value; RAW_VALUE_SECRET"
            )
            validations = iter((
                (None, "target answer submission is missing"),
                (None, raw_error),
                ({"path": "answer.json", "sha256": "a" * 64}, ""),
            ))
            runner = self._runner(
                root=root, state=state, iter_dir=iter_dir,
                prover_worker=_process_prover, review_worker=_process_review,
                formalizer_worker=fake_formalizer,
                formalization_review_worker=_process_formalization_review,
                max_parallel=1, full_pipeline=True,
                formalization_max_iterations=3, stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "native_problem_only_enabled", return_value=True,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_native_formalizer_source_contract",
                    return_value={},
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "validate_native_answer_submission_current",
                    side_effect=lambda **_kwargs: next(validations),
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "_native_formalizer_semantic_dag_block",
                    return_value="CONTRACT",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_target_review_source_contract",
                    return_value=None,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_target_formalization_review_prompt",
                    return_value="formal-review",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_target_review_prompt", return_value="proof-review",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt", return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(len(prompts), 2)
            self.assertIn("numeric_display_syntax", prompts[1])
            self.assertIn("repair_answer_submission_contract", prompts[1])
            self.assertNotIn("RAW_VALUE_SECRET", prompts[1])
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            history = report["formalizer_history"]["problem_item_a.lean"]
            self.assertEqual(len(history), 2)
            self.assertFalse(history[0]["answer_submission_valid"])
            self.assertEqual(
                [row["delivery_attempt"] for row in history], [1, None]
            )
            self.assertEqual([row["cycle"] for row in history], [1, 2])
            self.assertEqual(
                [row["answer_submission_repair"] for row in history],
                [False, True],
            )
            self.assertTrue(history[1]["answer_submission_repair"])

    def test_answer_submission_repair_handoff_never_echoes_raw_error(self):
        handoff = _answer_submission_repair_handoff(
            "output 0 has invalid fields EXPECTED_1299_SECRET"
        )
        encoded = json.dumps(handoff, sort_keys=True)
        self.assertIn("invalid_output_fields", encoded)
        self.assertNotIn("EXPECTED_1299_SECRET", encoded)

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
            review_attempts: list[tuple[int, bool]] = []

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
                if spec.rel == "A.lean":
                    milestone = _redraft_milestone(spec.rel)
                    milestone["status"] = "partial"
                    review_attempts.append((spec.attempt, spec.final_attempt))
                    outcome = _validated_review_outcome(spec, milestone)
                else:
                    outcome = TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=_milestone(spec.rel),
                    )
                record(f"review-{Path(spec.rel).stem}:end")
                return outcome

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
            self.assertEqual(
                review_attempts,
                [(1, False), (2, False), (3, True)],
            )
            self.assertIn("global PROGRESS stage intentionally remains", formalizer_prompts[0])
            self.assertIn("controller-sanitized repair task", formalizer_prompts[0])
            self.assertIn("needs_redraft", formalizer_prompts[0])
            self.assertIn(
                hashlib.sha256(
                    b"theorem a : True := by sorry\n"
                ).hexdigest(),
                formalizer_prompts[0],
            )
            self.assertNotIn(
                "the theorem assumes the requested conclusion", formalizer_prompts[0]
            )
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

    def test_partial_needs_redraft_can_self_correct_on_attempt_three(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            attempts: list[tuple[int, bool]] = []

            def fake_prover(*_args, **_kwargs):
                return True

            def fake_review(spec, **_kwargs):
                attempts.append((spec.attempt, spec.final_attempt))
                if spec.attempt == 3:
                    milestone = _milestone(spec.rel)
                else:
                    milestone = _redraft_milestone(spec.rel)
                    milestone["status"] = "partial"
                return _validated_review_outcome(spec, milestone)

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

            self.assertEqual(
                attempts,
                [(1, False), (2, False), (3, True)],
            )
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["formalizers"]["requested"], 0)
            self.assertEqual(
                report["proof_review_target_files"], ["A.lean"],
            )

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
            review_prompts: list[str] = []
            validation_error = (
                "requested output 1 assembly_expression omits a product "
                'node id; missing=["terminal_fragment"]'
            )
            prover_calls = 0

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_review(spec, **_kwargs):
                review_attempts.append(spec.attempt)
                review_prompts.append(spec.prompt)
                if spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error=validation_error,
                        validation_error=validation_error,
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
            self.assertNotIn(validation_error, review_prompts[0])
            self.assertIn(json.dumps(validation_error), review_prompts[1])
            self.assertIn(
                "CONTROLLER SEALED-VALIDATOR RETRY FEEDBACK",
                review_prompts[1],
            )
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

    def test_incomplete_formalizer_falls_back_without_losing_review(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n", encoding="utf-8")

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
                review_worker=_process_redraft_review,
                formalizer_worker=incomplete_formalizer,
                max_parallel=1,
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
            self.assertEqual(report["reviewed"], 1)
            self.assertEqual(report["formalizers"]["failed"], 1)
            self.assertEqual(report["formalization_handoffs"], {})
            failure = report["formalizer_results"]["A.lean"]
            self.assertFalse(failure["task_result_updated"])
            self.assertIn("did not update its task result", failure["error"])

    def test_redraft_prompt_size_error_is_target_scoped(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            formalizer_calls = 0

            def unexpected_formalizer(*_args, **_kwargs):
                nonlocal formalizer_calls
                formalizer_calls += 1
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_redraft_review,
                formalizer_worker=unexpected_formalizer,
                max_parallel=1,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_immediate_redraft_prompt",
                    side_effect=_ImmediateRedraftPromptError(
                        "immediate redraft prompt exceeds 128 KiB"
                    ),
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(formalizer_calls, 0)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["formalizers"]["failed"], 1)
            failure = report["formalizer_results"]["A.lean"]
            self.assertIn(
                "safe immediate redraft prompt rejection: immediate redraft "
                "prompt exceeds 128 KiB",
                failure["error"],
            )

    def test_redraft_prompt_error_does_not_block_a_solved_peer(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            targets = [root / "A.lean", root / "B.lean"]
            for target in targets:
                target.write_text(
                    f"theorem {target.stem.lower()} : True := by sorry\n",
                    encoding="utf-8",
                )
            proof_reviews: list[str] = []
            formalizer_calls = 0

            def proof_review(spec, **_kwargs):
                proof_reviews.append(spec.rel)
                milestone = (
                    _redraft_milestone(spec.rel)
                    if spec.rel == "A.lean"
                    else _milestone(spec.rel)
                )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def unexpected_formalizer(*_args, **_kwargs):
                nonlocal formalizer_calls
                formalizer_calls += 1
                return True

            def prompt_builder(**kwargs):
                if kwargs["target"].name == "A.lean":
                    raise _ImmediateRedraftPromptError(
                        "immediate redraft prompt exceeds 128 KiB"
                    )
                return "valid target-local redraft prompt"

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=proof_review,
                formalizer_worker=unexpected_formalizer,
                max_parallel=2,
                full_pipeline=True,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_immediate_redraft_prompt",
                    side_effect=prompt_builder,
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout(targets, file_modes={})

            self.assertEqual(sorted(proof_reviews), ["A.lean", "B.lean"])
            self.assertEqual(formalizer_calls, 0)
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["status"], "incomplete")
            self.assertEqual(report["settled_target_files"], ["B.lean"])
            self.assertEqual(
                report["pending_formalization_targets"], ["A.lean"],
            )
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertIn(
                "safe immediate redraft prompt rejection: immediate redraft "
                "prompt exceeds 128 KiB",
                report["errors"]["A.lean"],
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(proof_gate["targets"]["B.lean"]["status"], "solved")
            self.assertEqual(
                proof_gate["targets"]["A.lean"]["status"], "needs_redraft",
            )

    def test_full_pipeline_formalization_retry_receives_validator_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            review_attempts: list[int] = []
            review_prompts: list[str] = []
            validation_error = (
                "source_contract does not match native problem-only evidence: "
                "source_record_sha256 actual length 60, expected 64"
            )

            def failing_formalization_review(spec, **_kwargs):
                review_attempts.append(spec.attempt)
                review_prompts.append(spec.prompt)
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=None,
                    error=validation_error,
                    validation_error=validation_error,
                )

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                formalizer_worker=_process_formalizer,
                formalization_review_worker=failing_formalization_review,
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
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(
                    encoding="utf-8",
                )
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["status"], "incomplete")
            self.assertEqual(report["settled_target_files"], [])
            self.assertEqual(
                report["pending_formalization_targets"],
                ["A.lean"],
            )
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertIn(
                validation_error,
                report["errors"]["A.lean"],
            )
            self.assertFalse(report["gate_events_applied"])
            self.assertEqual(review_attempts, [1, 2, 3])
            self.assertNotIn(validation_error, review_prompts[0])
            for prompt in review_prompts[1:]:
                self.assertIn(validation_error, prompt)
                self.assertIn(
                    "CONTROLLER SEALED-VALIDATOR RETRY FEEDBACK", prompt,
                )
            session = (
                state / "proof-journal" / "sessions" / "session_1"
                / "milestones.jsonl"
            )
            self.assertFalse(session.exists())
            loaded, error = load_pipelined_review_report(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                objectives=[target],
            )
            self.assertIsNone(loaded)
            self.assertIn("incomplete", error)

    def test_final_gate_retry_invalidates_complete_before_session(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n", encoding="utf-8",
            )
            proof_states = iter([
                {"targets": {}},
                {
                    "targets": {
                        "A.lean": {"status": "retry", "attempts": 0},
                    },
                },
                {
                    "targets": {
                        "A.lean": {
                            "status": "solved",
                            "history": [{
                                "event_id": "pipeline:1:A.lean:proof:1",
                            }],
                        },
                    },
                },
                {
                    "targets": {
                        "A.lean": {
                            "status": "solved",
                            "history": [{
                                "event_id": "pipeline:1:A.lean:proof:1",
                            }],
                        },
                    },
                },
            ])
            formalization_states = iter([
                {"targets": {}},
                {
                    "targets": {
                        "A.lean": {
                            "status": "passed",
                            "reviews": 1,
                            "review_events": [{
                                "event_id":
                                    "pipeline:1:A.lean:formalization:1",
                                "decision": "passed",
                            }],
                        },
                    },
                },
                {
                    "targets": {
                        "A.lean": {
                            "status": "retry",
                            "review_events": [{
                                "event_id":
                                    "pipeline:1:A.lean:formalization:1",
                                "decision": "passed",
                            }],
                        },
                    },
                },
            ])

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                formalizer_worker=_process_formalizer,
                formalization_review_worker=_process_formalization_review,
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
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "load_proof_review_state",
                    side_effect=lambda _state: next(proof_states),
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "load_formalization_review_state",
                    side_effect=lambda _state: next(formalization_states),
                ),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(
                    encoding="utf-8",
                )
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["status"], "incomplete")
            self.assertEqual(report["settled_target_files"], [])
            self.assertEqual(
                report["pending_formalization_targets"],
                ["A.lean"],
            )
            self.assertTrue(report["gate_events_applied"])
            session = (
                state / "proof-journal" / "sessions" / "session_1"
                / "milestones.jsonl"
            )
            self.assertFalse(session.exists())
            meta = json.loads(
                (iter_dir / "meta.json").read_text(encoding="utf-8")
            )
            self.assertFalse(meta["prover"]["pipelineReviewComplete"])

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
                formalizer_prompts: list[str] = []

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
                            "formalization_redraft_passed", spec.prompt
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
                    formalizer_prompts.append(_args[0])
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
                        self.assertIn('"current_status": "retry"', spec.prompt)
                        self.assertIn('"reopened_by": "proof_review"', spec.prompt)
                        self.assertNotIn(
                            "the theorem assumes the requested conclusion",
                            spec.prompt,
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
                    len(formalizer_prompts), len(formalization_verdicts)
                )
                self.assertIn("needs_redraft", formalizer_prompts[0])
                self.assertNotIn(
                    "the theorem assumes the requested conclusion",
                    formalizer_prompts[0],
                )
                for prior_cycle, prompt in enumerate(
                    formalizer_prompts[1:], start=1
                ):
                    self.assertIn("formalization_review_failed", prompt)
                    self.assertIn(
                        hashlib.sha256(
                            f"theorem a (h_law_{prior_cycle} : True) : "
                            "True := by sorry\n".encode()
                        ).hexdigest(),
                        prompt,
                    )
                    self.assertNotIn(
                        "the contract omits a source constraint",
                        prompt,
                    )
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

    def test_proof_redraft_requeues_after_three_prior_formalization_reviews(self):
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

            for cycle in (1, 2, 3):
                update = apply_target_formalization_review(
                    state_dir=state,
                    project_path=root,
                    target=target,
                    milestone=_formalization_milestone("A.lean"),
                    iter_num=0,
                    max_iterations=3,
                    event_id=f"pipeline:0:A.lean:formalization:{cycle}",
                )
                self.assertTrue(update.passed)
                self.assertEqual(update.reviews, cycle)

            prover_calls = 0
            proof_review_calls = 0
            formalizer_calls = 0
            formalization_review_calls = 0

            def fake_prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def fake_proof_review(spec, **_kwargs):
                nonlocal proof_review_calls
                proof_review_calls += 1
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
                    "theorem a (h_grounded : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Fresh proof-triggered redraft\n", encoding="utf-8"
                )
                return True

            def fake_formalization_review(spec, **_kwargs):
                nonlocal formalization_review_calls
                formalization_review_calls += 1
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel),
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
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(prover_calls, 2)
            self.assertEqual(proof_review_calls, 2)
            self.assertEqual(formalizer_calls, 1)
            self.assertEqual(formalization_review_calls, 1)
            formal_record = formalization_gate["targets"]["A.lean"]
            self.assertEqual(formal_record["status"], "passed")
            self.assertEqual(formal_record["reviews"], 4)
            self.assertEqual(
                formal_record["proof_redraft_resubmission"]["status"],
                "reviewed",
            )
            self.assertEqual(
                proof_gate["targets"]["A.lean"]["status"], "solved"
            )

    def test_two_proof_redrafts_do_not_regress_final_gate_state(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by sorry\n",
                encoding="utf-8",
            )
            proof_calls = 0
            formalizer_calls = 0

            def fake_review(spec, **_kwargs):
                nonlocal proof_calls
                proof_calls += 1
                milestone = (
                    _redraft_milestone(spec.rel)
                    if proof_calls <= 2
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
                    f"theorem a (h_{formalizer_calls} : True) : "
                    "True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    f"# Redraft {formalizer_calls}\n",
                    encoding="utf-8",
                )
                return True

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=fake_review,
                formalizer_worker=fake_formalizer,
                formalization_review_worker=_process_formalization_review,
                max_parallel=1,
                full_pipeline=True,
                formalization_max_iterations=4,
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

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(
                    encoding="utf-8",
                )
            )
            proof = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )["targets"]["A.lean"]
            formalization = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8",
                )
            )["targets"]["A.lean"]
            self.assertEqual((proof_calls, formalizer_calls), (3, 2))
            self.assertTrue(report["complete"])
            self.assertTrue(report["gate_events_applied"])
            self.assertEqual(report["pending_formalization_targets"], [])
            self.assertEqual(proof["status"], "solved")
            self.assertEqual(formalization["status"], "passed")
            self.assertEqual(len(formalization["reopen_history"]), 2)

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
            self.assertEqual(captured["stage"], "autoformalize")
            self.assertEqual(captured["max_parallel"], 28)
            self.assertFalse(captured["dry_run"])

    def test_resume_autoformalize_gate_preserves_only_live_lanes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            iter_dir.mkdir(parents=True)
            names = (
                "retry", "passed_unproved",
                "formal_exhausted", "proof_retry",
                "proof_terminal",
            )
            targets = {name: root / f"{name}.lean" for name in names}
            for name, target in targets.items():
                target.write_text(
                    f"theorem {name} : True := by sorry\n",
                    encoding="utf-8",
                )
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nautoformalize\n\n"
                "## Current Objectives\n\n"
                + "".join(
                    f"- **`{target.name}`** — resume lane.\n"
                    for target in targets.values()
                ),
                encoding="utf-8",
            )
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "pipeline_target_review": True,
                    "deterministic_review": True,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                }
            }), encoding="utf-8")

            for name, verdicts in {
                "retry": (False,),
                "passed_unproved": (True,),
                "formal_exhausted": (False, False, False),
                "proof_retry": (True,),
                "proof_terminal": (True,),
            }.items():
                for cycle, passed in enumerate(verdicts, start=1):
                    apply_target_formalization_review(
                        state_dir=state,
                        project_path=root,
                        target=targets[name],
                        milestone=_formalization_milestone(
                            f"{name}.lean", passed=passed,
                        ),
                        iter_num=1,
                        max_iterations=3,
                        event_id=(
                            f"pipeline:1:{name}.lean:formalization:{cycle}"
                        ),
                    )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=targets["proof_retry"],
                milestone=_retry_proof_milestone("proof_retry.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:proof_retry.lean:proof:1",
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=targets["proof_terminal"],
                milestone=_milestone("proof_terminal.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:proof_terminal.lean:proof:1",
            )

            dispatched_progress: list[str] = []

            class FakeRunner:
                def __init__(self, **_kwargs):
                    pass

                def run(self, *, dry_run: bool):
                    del dry_run
                    dispatched_progress.append(
                        progress.read_text(encoding="utf-8")
                    )

            options = SimpleNamespace(
                parallel=True,
                multilane_preview=False,
                multilane_execute=False,
                no_review=False,
                proof_review_gate=True,
                formalization_review_gate=True,
                formalization_review_max_iterations=3,
                proof_review_max_iterations=3,
                max_parallel=4,
                max_objectives=4,
                block_on_blocked_deps=False,
                debug_feedback=False,
            )
            ctx = SimpleNamespace(
                project_name="project",
                project_path=root,
                state_dir=state,
                progress_file=progress,
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
                resume_phase="prover",
                dry_run=False,
                harness_descriptor_for=lambda _role: None,
            )
            with (
                patch(
                    "archon.commands.loop.phases.prover.ParallelProverRunner",
                    FakeRunner,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "_restrict_progress_to_pending_shared_modules",
                    return_value=False,
                ),
            ):
                ProverPhase(ctx)._dispatch()

            self.assertEqual(len(dispatched_progress), 1)
            routed = dispatched_progress[0]
            self.assertIn("retry.lean", routed)
            self.assertIn("passed_unproved.lean", routed)
            self.assertIn("proof_retry.lean", routed)
            self.assertNotIn("formal_exhausted.lean", routed)
            self.assertNotIn("proof_terminal.lean", routed)

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

            mode_calls: list[tuple[str, str, str | None]] = []
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
                    deadline = time.monotonic() + 5
                    while time.monotonic() < deadline:
                        try:
                            proof_gate = json.loads(
                                (state / "proof-review-gate.json").read_text(
                                    encoding="utf-8"
                                )
                            )
                        except (OSError, json.JSONDecodeError):
                            proof_gate = {}
                        if proof_gate.get("targets", {}).get(
                            "A.lean", {}
                        ).get("status") == "solved":
                            break
                        time.sleep(0.01)
                    else:
                        self.fail("A proof gate was not persisted before B ended")
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
                prompt = args[0]
                self.assertIn("Target-lifecycle proof hand-off", prompt)
                self.assertIn("active mode\n`chemistry`", prompt)
                formal_gate = json.loads(
                    (state / "formalization-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertEqual(formal_gate["targets"][f"{name}.lean"]["status"], "passed")
                record(f"prover-{name}")
                return True

            def fake_proof_review(spec, **_kwargs):
                name = Path(spec.rel).stem
                stage_calls[name]["proof_review"] += 1
                record(f"proof-review-{name}")
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )


            def fake_mode_selector(
                _state, stage, _project, target, *, explicit_mode=None,
            ):
                mode_calls.append((
                    Path(target).stem, stage, explicit_mode,
                ))
                return (
                    explicit_mode
                    or ("chemistry" if stage == "prover" else "chemistry-formalize")
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
                patch(
                    "archon.commands.loop.prover.runners."
                    "select_prover_mode_for_target",
                    side_effect=fake_mode_selector,
                ),
            ):
                runner._run_fanout(
                    list(targets.values()),
                    file_modes={
                        str(target): "chemistry-formalize"
                        for target in targets.values()
                    },
                )

            self.assertLess(
                order.index("proof-review-A"),
                order.index("formalizer-B:end"),
            )
            self.assertEqual(
                sorted(mode_calls),
                [
                    ("A", "autoformalize", "chemistry-formalize"),
                    ("A", "prover", None),
                    ("B", "autoformalize", "chemistry-formalize"),
                    ("B", "prover", None),
                ],
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
            prover_prompts: list[str] = []
            prior_records: list[dict] = []

            def fake_prover(prompt, *_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                prover_prompts.append(prompt)
                return True

            def fake_review(spec, **_kwargs):
                nonlocal review_calls
                review_calls += 1
                milestone = (
                    _retry_proof_milestone(spec.rel)
                    if review_calls == 1 else _milestone(spec.rel)
                )
                if review_calls == 1:
                    milestone["proof_review"]["reason"] = (
                        "RAW_RETRY_REASON_SECRET"
                    )
                    milestone["proof_review"]["evidence"] = (
                        "RAW_RETRY_EVIDENCE_SECRET"
                    )
                    milestone["proof_review"]["result_spec"] = {
                        "value": "RETRY_RESULT_SPEC_SECRET",
                    }
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=milestone,
                )

            def capture_review_prompt(**kwargs):
                prior_records.append(json.loads(json.dumps(
                    kwargs.get("prior_gate_record") or {}
                )))
                return "review"

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
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_target_review_prompt",
                    side_effect=capture_review_prompt,
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
            self.assertEqual(len(prior_records), 2)
            self.assertEqual(prior_records[0], {})
            history = prior_records[1].get("history")
            self.assertIsInstance(history, list)
            self.assertEqual(len(history), 1)
            self.assertEqual(history[0]["route"], "retry_proof")
            self.assertEqual(history[0]["attempt"], 1)
            self.assertEqual(
                history[0]["event_id"],
                "pipeline:1:A.lean:proof:1",
            )

            self.assertEqual(len(prover_prompts), 2)
            self.assertNotIn("retry_proof", prover_prompts[0])
            self.assertIn("proof Review", prover_prompts[1])
            self.assertIn(
                hashlib.sha256(b"theorem a : True := by sorry\n").hexdigest(),
                prover_prompts[1],
            )
            self.assertIn("retry_proof", prover_prompts[1])
            for secret in (
                "RAW_RETRY_REASON_SECRET",
                "RAW_RETRY_EVIDENCE_SECRET",
                "RETRY_RESULT_SPEC_SECRET",
            ):
                self.assertNotIn(secret, prover_prompts[1])
            self.assertNotIn('"result_spec":', prover_prompts[1])

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

    def test_prover_resume_done_lane_requires_resolved_native_answer(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`** — resume done lane.\n",
                encoding="utf-8",
            )
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by trivial\n",
                encoding="utf-8",
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=_milestone("A.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            proof_gate_path = state / "proof-review-gate.json"
            proof_gate = json.loads(
                proof_gate_path.read_text(encoding="utf-8")
            )
            proof_gate["targets"]["A.lean"]["status"] = "  SOLVED  "
            proof_gate_path.write_text(json.dumps(proof_gate), encoding="utf-8")
            (iter_dir / "meta.json").write_text(json.dumps({
                "provers": {"A": {"status": "done", "cycle": 1}},
            }), encoding="utf-8")
            prover_calls = 0
            review_calls = 0

            def prover(*_args, **_kwargs):
                nonlocal prover_calls
                prover_calls += 1
                return True

            def review(spec, **_kwargs):
                nonlocal review_calls
                review_calls += 1
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
                prover_worker=prover,
                review_worker=review,
                resume_enabled=True,
                stage="prover",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "native_problem_only_enabled",
                    return_value=True,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "validate_native_answer_submission_current"
                ) as base_validator,
                patch(
                    "archon.commands.loop.prover.runners."
                    "validate_native_resolved_answer_submission_current",
                    return_value=(
                        None,
                        "resolved answer submission rejects operational "
                        "non-answer 'blocked_missing_source_closure'",
                    ),
                ) as resolved_validator,
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="prove",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_target_review_prompt",
                    return_value="review",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_target_review_source_contract",
                    return_value=None,
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

            resolved_validator.assert_called_once_with(
                project_path=root,
                target=target,
            )
            base_validator.assert_not_called()
            self.assertEqual(prover_calls, 1)
            self.assertEqual(review_calls, 1)

    def test_resume_restores_lifecycle_cycles_without_event_collision(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`** — resume.\n",
                encoding="utf-8",
            )
            target = root / "A.lean"
            target.write_text(
                "theorem a (h_initial : True) : True := by sorry\n",
                encoding="utf-8",
            )

            for cycle in (1, 2, 3):
                update = apply_target_formalization_review(
                    state_dir=state,
                    project_path=root,
                    target=target,
                    milestone=_formalization_milestone("A.lean"),
                    iter_num=1,
                    max_iterations=3,
                    event_id=f"pipeline:1:A.lean:formalization:{cycle}",
                )
                self.assertTrue(update.passed)
                self.assertEqual(update.reviews, cycle)
            redraft = _redraft_milestone("A.lean")
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=redraft,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            reopen_formalization_targets(
                state_dir=state,
                project_path=root,
                progress_file=state / "PROGRESS.md",
                redrafts={
                    "A.lean": {
                        "reason": "the theorem assumes the requested conclusion",
                        "redraft_kind": "answer_as_assumption",
                        "pipeline_event_id": "pipeline:1:A.lean:proof:1",
                    }
                },
                iter_num=1,
                max_iterations=3,
                route_progress=False,
                enforce_budget=True,
            )

            target.write_text(
                "theorem a (h_redraft : True) : True := by sorry\n",
                encoding="utf-8",
            )
            (state / "task_results" / "A.lean.md").write_text(
                "# Redraft 2\n", encoding="utf-8",
            )
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {"status": "materialized", "cycle": 4},
                },
                # Omit pipelineReviews.cycle: proof cycle 1 must also be
                # recoverable from the existing proof gate history.
                "pipelineReviews": {"A": {"status": "done"}},
            }), encoding="utf-8")

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=_process_prover,
                review_worker=_process_review,
                formalizer_worker=lambda *_args, **_kwargs: self.fail(
                    "materialized resume lane reran the formalizer"
                ),
                formalization_review_worker=_process_formalization_review,
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
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                [event["event_id"] for event in report["gate_events"]],
                [
                    "pipeline:1:A.lean:formalization:3",
                    "pipeline:1:A.lean:formalization:4",
                    "pipeline:1:A.lean:proof:2",
                ],
            )
            self.assertEqual(report["gate_events"][0]["decision"], "passed")
            formalization_gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )
            proof_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            formalization_record = formalization_gate["targets"]["A.lean"]
            self.assertEqual(formalization_record["status"], "passed")
            self.assertEqual(
                [event["event_id"] for event in formalization_record["review_events"]],
                [
                    "pipeline:1:A.lean:formalization:1",
                    "pipeline:1:A.lean:formalization:2",
                    "pipeline:1:A.lean:formalization:3",
                    "pipeline:1:A.lean:formalization:4",
                ],
            )
            self.assertEqual(formalization_record["reviews"], 4)
            self.assertEqual(
                formalization_record["proof_redraft_resubmission"]["status"],
                "reviewed",
            )
            proof_record = proof_gate["targets"]["A.lean"]
            self.assertEqual(proof_record["status"], "solved")
            self.assertEqual(proof_record["attempts"], 1)
            self.assertEqual(
                [
                    event["event_id"] for event in proof_record["history"]
                    if event.get("event_id")
                ],
                [
                    "pipeline:1:A.lean:proof:1",
                    "pipeline:1:A.lean:proof:2",
                ],
            )

    def test_resume_formal_pass_without_sorry_skips_models_before_proof_review(
        self,
    ):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`**  resume.\n",
                encoding="utf-8",
            )
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by trivial\n",
                encoding="utf-8",
            )
            apply_target_formalization_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=_formalization_milestone("A.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:formalization:1",
            )
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {"status": "materialized", "cycle": 1},
                },
                "pipelineFormalizationReviews": {
                    "A": {"status": "passed", "cycle": 1, "attempt": 1},
                },
            }), encoding="utf-8")
            calls = {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 0,
            }

            def unexpected(kind):
                def worker(*_args, **_kwargs):
                    calls[kind] += 1
                    return False
                return worker

            def proof_review(spec, **_kwargs):
                calls["proof_review"] += 1
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
                prover_worker=unexpected("prover"),
                review_worker=proof_review,
                formalizer_worker=unexpected("formalizer"),
                formalization_review_worker=unexpected(
                    "formalization_review"
                ),
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
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(calls, {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 1,
            })
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(
                [row.get("decision") for row in report["gate_events"]
                 if row["kind"] == "formalization"],
                ["passed"],
            )

    def test_resume_operational_answer_cannot_revive_successful_gate(self):
        cases = (
            ("formalization_passed", "blocked_missing_source_closure"),
            ("proof_solved", "needs_redraft"),
        )
        for durable_state, sentinel in cases:
            with self.subTest(durable_state=durable_state, sentinel=sentinel):
                with tempfile.TemporaryDirectory() as td:
                    root = Path(td)
                    state = root / ".archon"
                    iter_dir = state / "logs" / "iter-001"
                    (iter_dir / "provers").mkdir(parents=True)
                    (state / "task_results").mkdir()
                    (state / "PROGRESS.md").write_text(
                        "# Progress\n\n## Current Objectives\n\n"
                        "- **`A.lean`** — resume.\n",
                        encoding="utf-8",
                    )
                    target = root / "A.lean"
                    target.write_text(
                        "theorem a : True := by trivial\n",
                        encoding="utf-8",
                    )
                    formal_milestone = _formalization_milestone("A.lean")
                    apply_target_formalization_review(
                        state_dir=state,
                        project_path=root,
                        target=target,
                        milestone=formal_milestone,
                        iter_num=1,
                        max_iterations=3,
                        event_id="pipeline:1:A.lean:formalization:1",
                    )
                    if durable_state == "formalization_passed":
                        formal_gate_path = (
                            state / "formalization-review-gate.json"
                        )
                        formal_gate = json.loads(
                            formal_gate_path.read_text(encoding="utf-8")
                        )
                        formal_gate["targets"]["A.lean"]["status"] = (
                            " PASSED "
                        )
                        formal_gate_path.write_text(
                            json.dumps(formal_gate), encoding="utf-8",
                        )
                    if durable_state == "proof_solved":
                        proof_milestone = _milestone("A.lean")
                        apply_target_proof_review(
                            state_dir=state,
                            project_path=root,
                            target=target,
                            milestone=proof_milestone,
                            iter_num=1,
                            max_iterations=3,
                            event_id="pipeline:1:A.lean:proof:1",
                        )
                        review_dir = (
                            iter_dir / "review-targets" / "A"
                            / "cycle-1" / "attempt-1"
                        )
                        review_dir.mkdir(parents=True)
                        (review_dir / "milestones.jsonl").write_text(
                            json.dumps(proof_milestone) + "\n",
                            encoding="utf-8",
                        )
                    meta = {
                        "pipelineFormalizers": {
                            "A": {"status": "materialized", "cycle": 1},
                        },
                        "pipelineFormalizationReviews": {
                            "A": {
                                "status": "passed",
                                "cycle": 1,
                                "attempt": 1,
                            },
                        },
                    }
                    if durable_state == "proof_solved":
                        meta.update({
                            "provers": {
                                "A": {"status": "done", "cycle": 1},
                            },
                            "pipelineReviews": {
                                "A": {
                                    "status": "done",
                                    "route": "solved",
                                    "cycle": 1,
                                    "attempt": 1,
                                },
                            },
                        })
                    (iter_dir / "meta.json").write_text(
                        json.dumps(meta), encoding="utf-8",
                    )
                    calls = {
                        "formalizer": 0,
                        "formalization_review": 0,
                        "prover": 0,
                        "proof_review": 0,
                    }

                    def unexpected(kind):
                        def worker(*_args, **_kwargs):
                            calls[kind] += 1
                            return False
                        return worker

                    runner = self._runner(
                        root=root,
                        state=state,
                        iter_dir=iter_dir,
                        prover_worker=unexpected("prover"),
                        review_worker=unexpected("proof_review"),
                        formalizer_worker=unexpected("formalizer"),
                        formalization_review_worker=unexpected(
                            "formalization_review"
                        ),
                        max_parallel=1,
                        resume_enabled=True,
                        full_pipeline=True,
                        stage="autoformalize",
                    )
                    resolved_error = (
                        "resolved answer submission rejects operational "
                        f"non-answer {sentinel!r}"
                    )
                    with (
                        patch(
                            "archon.commands.loop.prover.runners."
                            "native_problem_only_enabled",
                            return_value=True,
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "resolve_native_formalizer_source_contract",
                            return_value={},
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "validate_native_answer_submission_current",
                            return_value=({
                                "path": "answer.json",
                                "sha256": "a" * 64,
                            }, ""),
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "validate_native_resolved_answer_submission_current",
                            return_value=(None, resolved_error),
                        ) as resolved_validator,
                        patch(
                            "archon.commands.loop.prover.runners."
                            "_native_formalizer_semantic_dag_block",
                            return_value="CONTRACT",
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "build_parallel_prover_prompt",
                            return_value="work",
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "snapshot_baseline"
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "pick_resume_session",
                            return_value=None,
                        ),
                        patch(
                            "archon.commands.loop.prover.runners."
                            "persist_session_id"
                        ),
                    ):
                        runner._run_fanout([target], file_modes={})

                    resolved_validator.assert_called_once_with(
                        project_path=root,
                        target=target,
                    )
                    self.assertEqual(calls, {
                        "formalizer": 1,
                        "formalization_review": 0,
                        "prover": 0,
                        "proof_review": 0,
                    })
                    report = json.loads(
                        (iter_dir / "pipelined-review.json").read_text(
                            encoding="utf-8"
                        )
                    )
                    self.assertFalse(report["complete"])
                    self.assertEqual(report["settled_target_files"], [])

    def test_new_iteration_formalization_retry_uses_bound_handoff(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-002"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
            target = root / "A.lean"
            original = b"theorem a (h_answer : True) : True := by sorry\n"
            target.write_bytes(original)
            original_digest = hashlib.sha256(original).hexdigest()
            progress = state / "PROGRESS.md"
            progress.write_text(
                "# Progress\n\n## Current Stage\n\nautoformalize\n\n"
                "## Current Objectives\n\n- **`A.lean`** — retry.\n",
                encoding="utf-8",
            )
            session = state / "proof-journal" / "sessions" / "session_1"
            session.mkdir(parents=True)
            (session / "milestones.jsonl").write_text(
                json.dumps(_formalization_milestone("A.lean", passed=False))
                + "\n",
                encoding="utf-8",
            )
            apply_formalization_review(
                state_dir=state,
                project_path=root,
                progress_file=progress,
                session_dir=session,
                iter_num=1,
                reviewed_objectives=[target],
                max_iterations=3,
            )
            gate_path = state / "formalization-review-gate.json"
            legacy_gate = json.loads(gate_path.read_text(encoding="utf-8"))
            legacy_record = legacy_gate["targets"]["A.lean"]
            legacy_record.pop("repair_events", None)
            legacy_record["repair_handoff"]["expected_answer"] = "INJECTED"
            gate_path.write_text(json.dumps(legacy_gate), encoding="utf-8")
            prompts: list[str] = []
            calls = {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 0,
            }

            def formalizer(prompt, *_args, **_kwargs):
                calls["formalizer"] += 1
                prompts.append(prompt)
                target.write_text(
                    "theorem a : True := by trivial\n", encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Review redraft\n\nRemoved the answer-shaped premise.\n",
                    encoding="utf-8",
                )
                return True

            def formalization_review(spec, **_kwargs):
                calls["formalization_review"] += 1
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel),
                )

            def prover(*_args, **_kwargs):
                calls["prover"] += 1
                return True

            def proof_review(spec, **_kwargs):
                calls["proof_review"] += 1
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
                prover_worker=prover,
                review_worker=proof_review,
                formalizer_worker=formalizer,
                formalization_review_worker=formalization_review,
                max_parallel=1,
                resume_enabled=False,
                full_pipeline=True,
                stage="autoformalize",
                iter_num=2,
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="fresh base prompt",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value=None,
                ),
                patch("archon.commands.loop.prover.runners.persist_session_id"),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(calls["formalizer"], 1)
            self.assertEqual(calls["formalization_review"], 1)
            self.assertEqual(calls["proof_review"], 1)
            self.assertEqual(len(prompts), 1)
            prompt = prompts[0]
            self.assertIn(
                "Immediate formalization Review redraft hand-off", prompt,
            )
            self.assertIn("controller-sanitized repair task", prompt)
            self.assertIn("controller_sanitized_review_repair", prompt)
            self.assertIn("source_faithfulness", prompt)
            self.assertIn(original_digest, prompt)
            self.assertNotIn("INJECTED", prompt)
            self.assertNotIn("expected_answer", prompt)
            self.assertIn(
                "PROGRESS.md, gate files, AUTO_NOTES.md, blueprint files",
                prompt,
            )
            meta = json.loads(
                (iter_dir / "meta.json").read_text(encoding="utf-8")
            )
            formalizer_meta = meta["pipelineFormalizers"]["A"]
            self.assertEqual(formalizer_meta["origin"], "review-redraft")
            self.assertEqual(formalizer_meta["cycle"], 2)
            gate = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8",
                )
            )["targets"]["A.lean"]
            self.assertEqual(
                [event["event_id"] for event in gate["review_events"]],
                ["pipeline:2:A.lean:formalization:2"],
            )
            self.assertEqual(
                [event["event_id"] for event in gate["repair_events"]],
                ["pipeline:2:A.lean:formalization:2"],
            )

    def test_resume_replays_durable_needs_redraft_before_model_dispatch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`**  resume.\n",
                encoding="utf-8",
            )
            target = root / "A.lean"
            target.write_text(
                "theorem a (h_initial : True) : True := by sorry\n",
                encoding="utf-8",
            )
            apply_target_formalization_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=_formalization_milestone("A.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:formalization:1",
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=_redraft_milestone("A.lean"),
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {"status": "materialized", "cycle": 1},
                },
                "pipelineFormalizationReviews": {
                    "A": {"status": "passed", "cycle": 1, "attempt": 1},
                },
                "provers": {"A": {"status": "done", "cycle": 1}},
                "pipelineReviews": {
                    "A": {
                        "status": "done",
                        "route": "needs_redraft",
                        "cycle": 1,
                        "attempt": 1,
                    },
                },
            }), encoding="utf-8")
            calls = {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 0,
            }

            def formalizer(*_args, **_kwargs):
                calls["formalizer"] += 1
                prompt = _args[0]
                self.assertIsNone(_args[7])
                self.assertIn("controller-sanitized repair task", prompt)
                self.assertIn("needs_redraft", prompt)
                self.assertIn(
                    hashlib.sha256(
                        b"theorem a (h_initial : True) : True := by sorry\n"
                    ).hexdigest(),
                    prompt,
                )
                self.assertNotIn("the theorem assumes the requested conclusion", prompt)
                record = json.loads(
                    (state / "formalization-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )["targets"]["A.lean"]
                self.assertEqual(record["status"], "retry")
                self.assertEqual(record["reopened_by"], "proof_review")
                target.write_text(
                    "theorem a (h_law : True) : True := by sorry\n",
                    encoding="utf-8",
                )
                (state / "task_results" / "A.lean.md").write_text(
                    "# Redraft 2\n",
                    encoding="utf-8",
                )
                return True

            def formalization_review(spec, **_kwargs):
                calls["formalization_review"] += 1
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_formalization_milestone(spec.rel),
                )

            def prover(prompt, *_args, **_kwargs):
                calls["prover"] += 1
                self.assertIn("Target-lifecycle proof hand-off", prompt)
                self.assertIn("Do not leave `sorry`", prompt)
                target.write_text(
                    "theorem a (h_law : True) : True := by trivial\n",
                    encoding="utf-8",
                )
                return True

            def proof_review(spec, **_kwargs):
                calls["proof_review"] += 1
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
                prover_worker=prover,
                review_worker=proof_review,
                formalizer_worker=formalizer,
                formalization_review_worker=formalization_review,
                max_parallel=1,
                resume_enabled=True,
                full_pipeline=True,
                stage="autoformalize",
            )
            with (
                patch(
                    "archon.commands.loop.prover.runners."
                    "native_problem_only_enabled",
                    return_value=True,
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "resolve_native_formalizer_source_contract",
                    return_value={},
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "validate_native_answer_submission_current",
                    return_value=({
                        "path": "answer.json",
                        "sha256": "a" * 64,
                    }, ""),
                ) as base_validator,
                patch(
                    "archon.commands.loop.prover.runners."
                    "validate_native_resolved_answer_submission_current",
                    return_value=(
                        None,
                        "resolved answer submission rejects operational "
                        "non-answer 'needs_redraft'",
                    ),
                ) as resolved_validator,
                patch(
                    "archon.commands.loop.prover.runners."
                    "_native_formalizer_semantic_dag_block",
                    return_value="CONTRACT",
                ),
                patch(
                    "archon.commands.loop.prover.runners."
                    "build_parallel_prover_prompt",
                    return_value="work",
                ),
                patch("archon.commands.loop.prover.runners.snapshot_baseline"),
                patch(
                    "archon.commands.loop.prover.runners.pick_resume_session",
                    return_value="STALE_FORMALIZER_SESSION_MUST_NOT_RESUME",
                ),
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            resolved_validator.assert_called_once_with(
                project_path=root,
                target=target,
            )
            base_validator.assert_called_once_with(
                project_path=root,
                target=target,
            )
            self.assertEqual(calls, {
                "formalizer": 1,
                "formalization_review": 1,
                "prover": 1,
                "proof_review": 1,
            })
            formal = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )["targets"]["A.lean"]
            proof = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )["targets"]["A.lean"]
            self.assertEqual(formal["status"], "passed")
            self.assertEqual(
                [row["event_id"] for row in formal["review_events"]],
                [
                    "pipeline:1:A.lean:formalization:1",
                    "pipeline:1:A.lean:formalization:2",
                ],
            )
            self.assertEqual(proof["status"], "solved")
            for key in (
                "reopened_by", "redraft_kind", "certificate_revoked_at",
            ):
                self.assertNotIn(key, formal)
            transition = next(
                event
                for event in proof["repair_events"]
                if event.get("transition") == "formalization_redraft_passed"
            )
            self.assertEqual(
                transition["candidate_sha256"],
                hashlib.sha256(
                    b"theorem a (h_law : True) : True := by sorry\n"
                ).hexdigest(),
            )
            self.assertEqual(transition["failed_check_ids"], [])
            self.assertEqual(
                [row["event_id"] for row in proof["history"]
                 if row.get("event_id")],
                ["pipeline:1:A.lean:proof:1", "pipeline:1:A.lean:proof:2"],
            )

    def test_resume_terminal_proof_restores_without_any_model_call(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            (iter_dir / "provers").mkdir(parents=True)
            (state / "task_results").mkdir()
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Objectives\n\n"
                "- **`A.lean`**  resume.\n",
                encoding="utf-8",
            )
            target = root / "A.lean"
            target.write_text(
                "theorem a : True := by trivial\n",
                encoding="utf-8",
            )
            formal_milestone = _formalization_milestone("A.lean")
            proof_milestone = _milestone("A.lean")
            apply_target_formalization_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=formal_milestone,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:formalization:1",
            )
            apply_target_proof_review(
                state_dir=state,
                project_path=root,
                target=target,
                milestone=proof_milestone,
                iter_num=1,
                max_iterations=3,
                event_id="pipeline:1:A.lean:proof:1",
            )
            review_dir = (
                iter_dir / "review-targets" / "A"
                / "cycle-1" / "attempt-1"
            )
            review_dir.mkdir(parents=True)
            (review_dir / "milestones.jsonl").write_text(
                json.dumps(proof_milestone) + "\n",
                encoding="utf-8",
            )
            (iter_dir / "meta.json").write_text(json.dumps({
                "pipelineFormalizers": {
                    "A": {"status": "materialized", "cycle": 1},
                },
                "pipelineFormalizationReviews": {
                    "A": {"status": "passed", "cycle": 1, "attempt": 1},
                },
                "provers": {"A": {"status": "done", "cycle": 1}},
                "pipelineReviews": {
                    "A": {
                        "status": "done",
                        "route": "solved",
                        "cycle": 1,
                        "attempt": 1,
                    },
                },
            }), encoding="utf-8")
            calls = {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 0,
            }

            def unexpected(kind):
                def worker(*_args, **_kwargs):
                    calls[kind] += 1
                    return False
                return worker

            runner = self._runner(
                root=root,
                state=state,
                iter_dir=iter_dir,
                prover_worker=unexpected("prover"),
                review_worker=unexpected("proof_review"),
                formalizer_worker=unexpected("formalizer"),
                formalization_review_worker=unexpected(
                    "formalization_review"
                ),
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
                patch(
                    "archon.commands.loop.prover.runners.persist_session_id"
                ),
            ):
                runner._run_fanout([target], file_modes={})

            self.assertEqual(calls, {
                "formalizer": 0,
                "formalization_review": 0,
                "prover": 0,
                "proof_review": 0,
            })
            report = json.loads(
                (iter_dir / "pipelined-review.json").read_text(encoding="utf-8")
            )
            self.assertTrue(report["complete"])
            self.assertEqual(report["settled_target_files"], ["A.lean"])
            formal = json.loads(
                (state / "formalization-review-gate.json").read_text(
                    encoding="utf-8"
                )
            )["targets"]["A.lean"]
            proof = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )["targets"]["A.lean"]
            self.assertEqual(len(formal["review_events"]), 1)
            self.assertEqual(len(
                [row for row in proof["history"] if row.get("event_id")]
            ), 1)

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
