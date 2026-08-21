from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.command import LoopCommand
from archon.commands.loop.formalization_review_gate import STATE_VERSION
from archon.commands.loop.native_completion import (
    native_iteration_completion,
    native_terminal_partial,
)
from archon.commands.loop.phases.base import PhaseResult
from archon.state import read_stage


class _DonePhase:
    calls = 0

    def __init__(self, _ctx) -> None:
        pass

    def run(self) -> PhaseResult:
        type(self).calls += 1
        return PhaseResult()


class NativeLoopCompletionTest(unittest.TestCase):
    def _state(self, root: Path, *, count: int = 32) -> tuple[Path, Path, Path]:
        state = root / ".archon"
        logs = state / "logs" / "iter-003"
        physics = state / "physics-formalize"
        logs.mkdir(parents=True)
        physics.mkdir(parents=True)
        targets = [f"Problems/P{index:02d}.lean" for index in range(1, count + 1)]
        candidate_sha256: dict[str, str] = {}
        for rel in targets:
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("theorem done : True := by trivial\n", encoding="utf-8")
            candidate_sha256[rel] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
        progress = state / "PROGRESS.md"
        progress.write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Current Objectives\n\n"
            + "\n".join(f"- **`{rel}`** — reviewed" for rel in targets)
            + "\n",
            encoding="utf-8",
        )
        (physics / "latest.json").write_text(json.dumps({
            "command": "physics-formalize",
            "dry_run": False,
            "records": [{"rel_lean": rel} for rel in targets],
        }), encoding="utf-8")
        (state / "formalization-review-gate.json").write_text(json.dumps({
            "version": STATE_VERSION,
            "targets": {
                rel: {
                    "status": "passed",
                    "candidate_sha256": candidate_sha256[rel],
                }
                for rel in targets
            },
        }), encoding="utf-8")
        (state / "proof-review-gate.json").write_text(json.dumps({
            "version": 2,
            "targets": {
                rel: {
                    "status": "solved",
                    "candidate_sha256": candidate_sha256[rel],
                }
                for rel in targets
            },
        }), encoding="utf-8")
        meta = logs / "meta.json"
        meta.write_text(json.dumps({
            "completedAt": "2026-08-13T00:00:00Z",
            "plan": {"status": "done"},
            "prover": {"status": "done"},
            "review": {"status": "done"},
            "sorry_count": 0,
            "finalize": {"lake": {"ok": True}},
        }), encoding="utf-8")
        return state, progress, meta

    def _completion(self, root: Path, state: Path, progress: Path, meta: Path, **kwargs):
        return native_iteration_completion(
            project_path=root,
            state_dir=state,
            progress_file=progress,
            iter_meta=meta,
            formalization_gate_enabled=kwargs.get("formalization_gate_enabled", True),
            proof_gate_enabled=kwargs.get("proof_gate_enabled", True),
            current_sorry_count=kwargs.get("current_sorry_count", 0),
            current_lake_ok=kwargs.get("current_lake_ok", True),
            force_stage=kwargs.get("force_stage"),
        )

    def _terminal(
        self,
        root: Path,
        state: Path,
        progress: Path,
        **kwargs,
    ):
        return native_terminal_partial(
            project_path=root,
            state_dir=state,
            progress_file=progress,
            formalization_gate_enabled=kwargs.get(
                "formalization_gate_enabled", True,
            ),
            proof_gate_enabled=kwargs.get("proof_gate_enabled", True),
            force_stage=kwargs.get("force_stage"),
        )

    def _set_formalization_exhausted(
        self, state: Path, *, count: int = 2,
    ) -> tuple[str, ...]:
        formal_path = state / "formalization-review-gate.json"
        proof_path = state / "proof-review-gate.json"
        formal = json.loads(formal_path.read_text(encoding="utf-8"))
        proof = json.loads(proof_path.read_text(encoding="utf-8"))
        exhausted = tuple(sorted(formal["targets"])[:count])
        for rel in exhausted:
            formal["targets"][rel]["status"] = "review_exhausted"
            proof["targets"].pop(rel)
        formal_path.write_text(json.dumps(formal), encoding="utf-8")
        proof_path.write_text(json.dumps(proof), encoding="utf-8")
        return exhausted

    def test_30_solved_two_formalization_exhausted_stop_before_plan(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, meta = self._state(root)
            exhausted = self._set_formalization_exhausted(state)
            options = SimpleNamespace(
                max_iterations=10,
                skip_first_iter=set(),
                blueprint_server_flag=False,
                formalization_review_gate=True,
                proof_review_gate=True,
            )
            ctx = SimpleNamespace(
                options=options,
                project_path=root,
                project_name="native32-partial",
                state_dir=state,
                progress_file=progress,
                log_dir=state / "logs",
                current_stage="prover",
                iter_dir=meta.parent,
                iter_meta=meta,
                dashboard_url=None,
                blueprint_url=None,
                blueprint_server=None,
                dry_run=False,
                force_stage=lambda: None,
            )
            command = LoopCommand(options)
            command.ctx = ctx
            _DonePhase.calls = 0
            with patch(
                "archon.commands.loop.command.PlanPhase", _DonePhase,
            ):
                self.assertFalse(command._run_iteration(0))
                summary_path = state / "native-terminal.json"
                first_payload = summary_path.read_bytes()
                self.assertFalse(command._run_iteration(1))

            summary = json.loads(first_payload)
            self.assertEqual(_DonePhase.calls, 0)
            self.assertEqual(read_stage(progress), "prover")
            self.assertEqual(command.native_terminal_status, "completed_with_exhausted")
            self.assertEqual(summary["status"], "completed_with_exhausted")
            self.assertEqual(summary["target_count"], 32)
            self.assertEqual(summary["counts"], {
                "solved": 30,
                "formalization_review_exhausted": 2,
                "proof_review_exhausted": 0,
            })
            self.assertEqual(
                summary["targets"]["formalization_review_exhausted"],
                list(exhausted),
            )
            self.assertEqual(summary_path.read_bytes(), first_payload)
            formal_path = state / "formalization-review-gate.json"
            formal = json.loads(formal_path.read_text(encoding="utf-8"))
            formal["targets"][exhausted[0]]["status"] = "retry"
            formal_path.write_text(json.dumps(formal), encoding="utf-8")

            self.assertFalse(
                command._exit_for_native_terminal_partial()
            )
            self.assertFalse(summary_path.exists())
            self.assertIsNone(command.native_terminal_status)

    def test_proof_review_exhausted_is_terminal_but_not_complete(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, _meta = self._state(root, count=3)
            proof_path = state / "proof-review-gate.json"
            proof = json.loads(proof_path.read_text(encoding="utf-8"))
            exhausted = sorted(proof["targets"])[0]
            proof["targets"][exhausted]["status"] = "proof_review_exhausted"
            proof_path.write_text(json.dumps(proof), encoding="utf-8")

            result = self._terminal(root, state, progress)

            self.assertTrue(result.terminal)
            self.assertEqual(result.target_count, 3)
            self.assertEqual(result.proof_review_exhausted, (exhausted,))
            self.assertEqual(len(result.solved), 2)
            self.assertEqual(read_stage(progress), "prover")

    def test_retry_missing_redraft_and_stale_terminal_evidence_do_not_stop(
        self,
    ) -> None:
        mutations = (
            "formal_retry",
            "missing_formal",
            "proof_retry",
            "proof_needs_redraft",
            "missing_proof",
            "stale_hash",
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                state, progress, _meta = self._state(root, count=3)
                self._set_formalization_exhausted(state, count=1)
                formal_path = state / "formalization-review-gate.json"
                proof_path = state / "proof-review-gate.json"
                formal = json.loads(formal_path.read_text(encoding="utf-8"))
                proof = json.loads(proof_path.read_text(encoding="utf-8"))
                proof_rel = sorted(proof["targets"])[0]
                if mutation == "formal_retry":
                    formal["targets"][proof_rel]["status"] = "retry"
                elif mutation == "missing_formal":
                    formal["targets"].pop(sorted(formal["targets"])[0])
                elif mutation == "proof_retry":
                    proof["targets"][proof_rel]["status"] = "retry"
                elif mutation == "proof_needs_redraft":
                    proof["targets"][proof_rel]["status"] = "needs_redraft"
                elif mutation == "missing_proof":
                    proof["targets"].pop(proof_rel)
                else:
                    proof["targets"][proof_rel]["candidate_sha256"] = "0" * 64
                formal_path.write_text(json.dumps(formal), encoding="utf-8")
                proof_path.write_text(json.dumps(proof), encoding="utf-8")

                self.assertFalse(
                    self._terminal(root, state, progress).terminal
                )

    def test_pending_shared_infrastructure_prevents_terminal_partial(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, _meta = self._state(root, count=3)
            self._set_formalization_exhausted(state, count=1)

            with patch(
                "archon.commands.loop.native_completion."
                "pending_shared_infrastructure_objectives",
                return_value=[object()],
            ):
                self.assertFalse(
                    self._terminal(root, state, progress).terminal
                )


    def test_32_solved_targets_exit_before_another_plan(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, meta = self._state(root)
            options = SimpleNamespace(
                max_iterations=10,
                skip_first_iter=set(),
                blueprint_server_flag=False,
                formalization_review_gate=True,
                proof_review_gate=True,
            )
            ctx = SimpleNamespace(
                options=options,
                project_path=root,
                project_name="native32",
                state_dir=state,
                progress_file=progress,
                log_dir=state / "logs",
                current_stage="prover",
                iter_dir=meta.parent,
                iter_meta=meta,
                dashboard_url=None,
                blueprint_url=None,
                blueprint_server=None,
                dry_run=False,
                force_stage=lambda: None,
            )
            command = LoopCommand(options)
            command.ctx = ctx
            _DonePhase.calls = 0
            phase_names = (
                "PlanPhase", "PhysicsGroundingPhase", "ProverPhase",
                "SyncLeanokPhase", "BlueprintDoctorPhase", "AxiomSweepPhase",
                "ReviewPhase",
            )
            patches = [
                patch(f"archon.commands.loop.command.{name}", _DonePhase)
                for name in phase_names
            ]
            with ExitStack() as stack:
                for phase_patch in patches:
                    stack.enter_context(phase_patch)
                stack.enter_context(patch.object(command, "_setup_iteration_dir"))
                stack.enter_context(patch.object(
                    command, "_post_phases_sorry_count",
                    side_effect=lambda: setattr(ctx, "sorry_after", 0),
                ))
                stack.enter_context(patch(
                    "archon.commands.loop.command.FinalizePhase",
                    side_effect=lambda _ctx: SimpleNamespace(
                        run=lambda: (
                            setattr(ctx, "finalize_lake_ok_current", True)
                            or PhaseResult()
                        )
                    ),
                ))
                stack.enter_context(patch(
                    "archon.commands.loop.command.plan_validate.validate_plan_output",
                    return_value=True,
                ))
                stack.enter_context(patch(
                    "archon.commands.loop.command.cost_summary", return_value=None,
                ))
                self.assertFalse(command._run_iteration(0))
                calls_after_terminal_iteration = _DonePhase.calls
                self.assertFalse(command._run_iteration(1))

            self.assertEqual(read_stage(progress), "complete")
            self.assertEqual(_DonePhase.calls, calls_after_terminal_iteration)

    def test_first_iteration_from_prover_accepts_skipped_plan(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, meta = self._state(root)
            value = json.loads(meta.read_text(encoding="utf-8"))
            value["plan"]["status"] = "skipped"
            meta.write_text(json.dumps(value), encoding="utf-8")

            result = self._completion(root, state, progress, meta)

            self.assertTrue(result.complete)
            self.assertEqual(result.target_count, 32)

    def test_unsettled_or_incomplete_evidence_does_not_auto_complete(self) -> None:
        mutations = ("retry", "missing_target", "lake_failed", "sorry", "review_running")
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                state, progress, meta = self._state(root)
                if mutation in {"retry", "missing_target"}:
                    path = state / "proof-review-gate.json"
                    value = json.loads(path.read_text(encoding="utf-8"))
                    first = sorted(value["targets"])[0]
                    if mutation == "retry":
                        value["targets"][first]["status"] = "retry"
                    else:
                        del value["targets"][first]
                    path.write_text(json.dumps(value), encoding="utf-8")
                kwargs = {}
                if mutation not in {"retry", "missing_target"}:
                    value = json.loads(meta.read_text(encoding="utf-8"))
                    if mutation == "lake_failed":
                        kwargs["current_lake_ok"] = False
                    elif mutation == "sorry":
                        kwargs["current_sorry_count"] = 1
                    else:
                        value["review"]["status"] = "running"
                    meta.write_text(json.dumps(value), encoding="utf-8")
                self.assertFalse(
                    self._completion(root, state, progress, meta, **kwargs).complete
                )

    def test_general_or_explicitly_forced_projects_do_not_auto_complete(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state, progress, meta = self._state(root, count=1)
            self.assertFalse(
                self._completion(
                    root, state, progress, meta, proof_gate_enabled=False,
                ).complete
            )
            self.assertFalse(
                self._completion(root, state, progress, meta, force_stage="prover").complete
            )
            progress.write_text(
                progress.read_text(encoding="utf-8").replace("\nprover\n", "\nprover-extra\n"),
                encoding="utf-8",
            )
            self.assertFalse(self._completion(root, state, progress, meta).complete)
            progress.write_text(
                progress.read_text(encoding="utf-8").replace("\nprover-extra\n", "\nprover\n"),
                encoding="utf-8",
            )
            proof_path = state / "proof-review-gate.json"
            proof = json.loads(proof_path.read_text(encoding="utf-8"))
            proof["version"] = 1
            proof_path.write_text(json.dumps(proof), encoding="utf-8")
            self.assertFalse(self._completion(root, state, progress, meta).complete)
            proof["version"] = 2
            proof_path.write_text(json.dumps(proof), encoding="utf-8")
            (state / "physics-formalize/latest.json").unlink()
            self.assertFalse(self._completion(root, state, progress, meta).complete)


if __name__ == "__main__":
    unittest.main()
