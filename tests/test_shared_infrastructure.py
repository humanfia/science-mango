from __future__ import annotations

import json
import hashlib
import tempfile
import time
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.axiom_sweep import AxiomSweepReport
from archon.commands.loop.deterministic_plan import (
    select_deterministic_candidates,
    write_deterministic_objectives,
)
from archon.commands.loop.proof_review_gate import apply_proof_review
from archon.commands.loop.phases.axiom_sweep import AxiomSweepPhase
from archon.commands.loop.phases.finalize import FinalizePhase
from archon.commands.loop.prover.runners import select_prover_mode_for_target
from archon.commands.loop.prover.runners import (
    _restrict_progress_to_pending_shared_modules,
)
from archon.commands.loop.phases.review import ReviewPhase
from archon.commands.loop.phases.prover import ProverPhase
from archon.commands.loop.sorry_count import filter_noop_objectives
from archon.commands.loop.formalization_review_gate import (
    filter_objectives_for_review_gate,
)
from archon.commands.loop.shared_infrastructure import (
    EXTERNAL_KIND,
    PROJECT_LOCAL_KIND,
    _module_declares,
    _module_exports_declarations,
    load_shared_infrastructure_state,
    missing_shared_module_objectives,
    pending_shared_consumer_migrations,
    pending_shared_infrastructure_objectives,
    reconcile_shared_infrastructure,
    register_shared_infrastructure_request,
    reopen_resolved_shared_dependents,
    shared_infrastructure_prompt_block,
)
from archon.state import parse_objectives_with_modes
from archon.commands.tooling.iteration import IterationFinalizationReport


class SharedInfrastructureLoopTest(unittest.TestCase):
    def _project(self, root: Path) -> Path:
        state = root / ".archon"
        state.mkdir()
        (state / "config.json").write_text(json.dumps({
            "loop": {
                "deterministic_plan": True,
                "shared_infrastructure": {
                    "enabled": True,
                    "module_roots": ["IChO2026Chem"],
                    "scaffolder": "chemistry-module-refactor",
                },
            },
        }), encoding="utf-8")
        (state / "PROGRESS.md").write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Stages\n\n- prover\n\n## Current Objectives\n\n"
            "- `Problems/T1.lean`\n\n",
            encoding="utf-8",
        )
        return state

    def _register(
        self, root: Path, state: Path, target: str, declarations: list[str],
    ) -> tuple[dict | None, str]:
        return register_shared_infrastructure_request(
            state_dir=state,
            project_path=root,
            target_rel=target,
            raw_request={
                "kind": PROJECT_LOCAL_KIND,
                "module": "IChO2026Chem/Core/Formula.lean",
                "declarations": declarations,
            },
            reason="shared molecular formula model is missing",
            evidence="unknown identifier Formula",
            iter_num=1,
        )

    def _seed_resolved_module(
        self, root: Path, state: Path, target: str = "Problems/T1.lean",
    ) -> tuple[Path, Path]:
        self._register(root, state, target, ["Formula"])
        module = root / "IChO2026Chem" / "Core" / "Formula.lean"
        module.parent.mkdir(parents=True)
        module.write_text("def Formula := Nat\n", encoding="utf-8")
        consumer = root / target
        consumer.parent.mkdir(parents=True, exist_ok=True)
        consumer.write_text(
            "import IChO2026Chem.Core.Formula\n"
            "theorem t : True := by trivial\n",
            encoding="utf-8",
        )
        queue = load_shared_infrastructure_state(state)
        record = queue["modules"]["IChO2026Chem/Core/Formula.lean"]
        record.update({
            "status": "resolved",
            "verified_iter": 2,
            "resolved_iter": 2,
            "verified_sha256": hashlib.sha256(module.read_bytes()).hexdigest(),
            "consumer_migrations": {
                target: {
                    "status": "resolved",
                    "build_iter": 2,
                    "consumer_sha256": hashlib.sha256(
                        consumer.read_bytes()
                    ).hexdigest(),
                },
            },
        })
        (state / "shared-infrastructure.json").write_text(
            json.dumps(queue), encoding="utf-8",
        )
        return module, consumer

    def test_coalesces_dependents_and_rejects_non_allowlisted_or_external(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            first, error = self._register(
                root, state, "Problems/T1.lean", ["Element", "Formula"],
            )
            self.assertEqual(error, "")
            self.assertEqual(first["kind"], PROJECT_LOCAL_KIND)
            self._register(root, state, "Problems/T9.lean", ["Formula", "charge"])

            queued = pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            )
            self.assertEqual(len(queued), 1)
            self.assertEqual(
                queued[0].dependents,
                ("Problems/T1.lean", "Problems/T9.lean"),
            )
            self.assertEqual(
                queued[0].declarations,
                ("Element", "Formula", "charge"),
            )

            unsafe, unsafe_error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T2.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "Elsewhere/Injected.lean",
                    "declarations": ["Bad"],
                },
                reason="bad path",
                evidence="",
                iter_num=1,
            )
            self.assertIsNone(unsafe)
            self.assertIn("allowlist", unsafe_error)

            invalid, invalid_error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T2.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "IChO2026Chem/Core/Acid-Base.lean",
                    "declarations": ["AcidBase"],
                },
                reason="invalid Lean module path",
                evidence="",
                iter_num=1,
            )
            self.assertIsNone(invalid)
            self.assertIn("identifier path segments", invalid_error)

            external, external_error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T2.lean",
                raw_request={"kind": EXTERNAL_KIND, "package": "crnt-lean"},
                reason="package missing",
                evidence="",
                iter_num=1,
            )
            self.assertEqual(external_error, "")
            self.assertEqual(external, {
                "kind": EXTERNAL_KIND, "package": "crnt-lean",
            })
            # External packages are evidence only and never queue a write.
            self.assertEqual(len(pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            )), 1)

            # Turning the opt-in off quarantines pre-existing queue state.
            (state / "config.json").write_text(json.dumps({
                "loop": {
                    "shared_infrastructure": {
                        "enabled": False,
                        "module_roots": ["IChO2026Chem"],
                    },
                },
            }), encoding="utf-8")
            self.assertEqual(pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            ), [])
            self.assertEqual(
                reconcile_shared_infrastructure(
                    state_dir=state, project_path=root,
                ).reopened_targets,
                (),
            )

    def test_private_declaration_does_not_satisfy_shared_api(self):
        with tempfile.TemporaryDirectory() as td:
            module = Path(td) / "Core.lean"
            module.write_text(
                "private def Formula := Nat\ndef PublicFormula := Nat\n",
                encoding="utf-8",
            )
            self.assertFalse(_module_declares(module, ["Formula"]))
            self.assertTrue(_module_declares(module, ["PublicFormula"]))

    def test_full_declaration_name_is_checked_by_lean_probe(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text(
                'name = "probe"\n', encoding="utf-8",
            )
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text(
                "namespace Wrong\ndef Formula := Nat\nend Wrong\n",
                encoding="utf-8",
            )

            def lean_probe(command, **_kwargs):
                probe = Path(command[-1]).read_text(encoding="utf-8")
                self.assertIn("import IChO2026Chem.Core.Formula", probe)
                return SimpleNamespace(
                    returncode=1 if "#check Right.Formula" in probe else 0,
                )

            with patch(
                "archon.commands.loop.shared_infrastructure.subprocess.run",
                side_effect=lean_probe,
            ):
                self.assertFalse(_module_exports_declarations(
                    root,
                    "IChO2026Chem/Core/Formula.lean",
                    module,
                    ["Right.Formula"],
                ))
                self.assertTrue(_module_exports_declarations(
                    root,
                    "IChO2026Chem/Core/Formula.lean",
                    module,
                    ["Wrong.Formula"],
                ))

    def test_finalize_records_dedicated_lake_completion_epoch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            meta = root / "meta.json"
            ctx = SimpleNamespace(
                dry_run=False,
                options=SimpleNamespace(has_finalize=True),
                iter_meta=meta,
            )
            phase = FinalizePhase(ctx)
            report = IterationFinalizationReport(
                lake_build_ok=True,
                lake_build_completed_epoch=123.0,
            )
            with patch.object(phase, "_invoke_finalizer", return_value=report):
                phase.run()

            lake = json.loads(meta.read_text(encoding="utf-8"))["finalize"][
                "lake"
            ]
            self.assertTrue(lake["ok"])
            self.assertEqual(lake["completedAtEpoch"], 123.0)

    def test_missing_module_yields_full_planner_scaffolding_prompt(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])

            missing = missing_shared_module_objectives(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                [item.module_path for item in missing],
                ["IChO2026Chem/Core/Formula.lean"],
            )
            prompt = shared_infrastructure_prompt_block(
                state_dir=state, project_path=root,
            )
            self.assertIn("chemistry-module-refactor", prompt)
            self.assertIn("scaffold first", prompt)
            self.assertIn("[prover-mode: mathlib-build]", prompt)
            self.assertIn("Do not install or modify Lake dependencies", prompt)

    def test_proof_review_structured_request_registers_automatically(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            target = root / "Problems" / "T1.lean"
            target.parent.mkdir()
            target.write_text("theorem t : True := by sorry\n", encoding="utf-8")
            session = state / "proof-journal" / "sessions" / "session_1"
            session.mkdir(parents=True)
            milestone = {
                "target": {"file": "Problems/T1.lean", "theorem": "t"},
                "status": "blocked",
                "proof_review": {
                    "schema_version": 1,
                    "route": "blocked_infrastructure",
                    "reason": "shared molecular formula model is missing",
                    "evidence": "unknown identifier Formula",
                    "redraft_kind": "not_applicable",
                    "infrastructure_request": {
                        "kind": PROJECT_LOCAL_KIND,
                        "module": "IChO2026Chem/Core/Formula.lean",
                        "declarations": ["Formula"],
                    },
                },
            }
            (session / "milestones.jsonl").write_text(
                json.dumps(milestone) + "\n", encoding="utf-8",
            )

            result = apply_proof_review(
                state_dir=state,
                project_path=root,
                session_dir=session,
                iter_num=1,
                reviewed_objectives=[target],
                max_iterations=3,
            )
            self.assertEqual(result.blocked_infrastructure, ("Problems/T1.lean",))
            queued = pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                [item.module_path for item in queued],
                ["IChO2026Chem/Core/Formula.lean"],
            )
            gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                gate["targets"]["Problems/T1.lean"]["infrastructure_request"]
                    ["kind"],
                PROJECT_LOCAL_KIND,
            )

    def test_deterministic_restore_preserves_mathlib_build_mode(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text(
                "def Formula := Nat\ntheorem formula_ok : True := by trivial\n",
                encoding="utf-8",
            )

            candidates = select_deterministic_candidates(
                project_path=root,
                state_dir=state,
                stage="prover",
                limit=1,
                formalization_gate_enabled=True,
                proof_gate_enabled=True,
            )
            self.assertEqual(
                [item.relative_path for item in candidates],
                ["IChO2026Chem/Core/Formula.lean"],
            )
            self.assertEqual(candidates[0].prover_mode, "mathlib-build")
            write_deterministic_objectives(
                progress_file=state / "PROGRESS.md",
                state_dir=state,
                iter_num=2,
                candidates=candidates,
            )
            parsed = parse_objectives_with_modes(
                state / "PROGRESS.md", root,
            )
            self.assertEqual(parsed, [(module, "mathlib-build")])
            modes = state / "prover-modes"
            modes.mkdir()
            (modes / "mathlib-build.md").write_text("build\n", encoding="utf-8")
            self.assertEqual(
                select_prover_mode_for_target(
                    state, "prover", root, module, explicit_mode="physics",
                ),
                "mathlib-build",
            )
            # Both validation and runner use this filter; zero-sorry pending
            # infrastructure must survive it.
            kept, dropped = filter_noop_objectives(
                [module], progress_file=state / "PROGRESS.md", state_dir=state,
            )
            self.assertEqual(kept, [module])
            self.assertEqual(dropped, [])
            # It is infrastructure, not a source-problem theorem, so it also
            # bypasses the formalization Review certificate gate.
            kept, dropped = filter_objectives_for_review_gate(
                [module], state_dir=state, project_path=root,
                stage="prover", enabled=True,
            )
            self.assertEqual(kept, [module])
            self.assertEqual(dropped, [])

    def test_pending_shared_module_forces_axiom_sweep_when_option_is_off(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text("def Formula := Nat\n", encoding="utf-8")
            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            iter_meta = iter_dir / "meta.json"
            iter_meta.write_text("{}\n", encoding="utf-8")
            ctx = SimpleNamespace(
                skip_now=set(),
                dry_run=False,
                project_path=root,
                state_dir=state,
                options=SimpleNamespace(max_parallel=2),
                current_stage="prover",
                progress_file=state / "PROGRESS.md",
                iter_num=2,
                iter_dir=iter_dir,
                iter_meta=iter_meta,
            )
            report = AxiomSweepReport(
                ran=True,
                files_checked=1,
                target_files=["IChO2026Chem/Core/Formula.lean"],
            )
            with patch(
                "archon.commands.loop.phases.axiom_sweep.run_axiom_sweep",
                return_value=report,
            ) as run:
                AxiomSweepPhase(ctx).run()

            targets = run.call_args.kwargs["targets"]
            self.assertIn(module.resolve(), targets)
            payload = json.loads(
                (iter_dir / "axiom-sweep.json").read_text(encoding="utf-8")
            )
            self.assertTrue(payload["ran"])

    def test_shared_batch_isolated_and_skips_problem_review(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text("def Formula := Nat\n", encoding="utf-8")
            problem = root / "Problems" / "T1.lean"
            problem.parent.mkdir()
            problem.write_text("theorem t : True := by sorry\n", encoding="utf-8")
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Stages\n\n- prover\n\n## Current Objectives\n\n"
                "- **`IChO2026Chem/Core/Formula.lean`**\n"
                "- **`Problems/T1.lean`**\n",
                encoding="utf-8",
            )
            selected = _restrict_progress_to_pending_shared_modules(
                progress_file=state / "PROGRESS.md",
                state_dir=state,
                project_path=root,
            )
            self.assertEqual(selected, [module])
            self.assertEqual(
                parse_objectives_with_modes(state / "PROGRESS.md", root),
                [(module, "mathlib-build")],
            )

            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            iter_meta = iter_dir / "meta.json"
            iter_meta.write_text("{}\n", encoding="utf-8")
            ctx = SimpleNamespace(
                options=SimpleNamespace(
                    formalization_review_gate=False,
                    proof_review_gate=True,
                    no_review=False,
                ),
                current_stage="prover",
                progress_file=state / "PROGRESS.md",
                project_path=root,
                state_dir=state,
                skip_now=set(),
                dry_run=False,
                iter_meta=iter_meta,
                iter_num=2,
            )
            with patch("archon.commands.loop.phases.review.commit_phase"):
                result = ReviewPhase(ctx).run()
            self.assertTrue(result.skipped)
            meta = json.loads(iter_meta.read_text(encoding="utf-8"))
            self.assertEqual(
                meta["review"]["outcome"],
                "shared_infrastructure_deferred",
            )
            self.assertEqual(meta["review"]["status"], "done")

    def test_multilane_execute_falls_back_to_mode_aware_runner(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text("def Formula := Nat\n", encoding="utf-8")
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n"
                "- `IChO2026Chem/Core/Formula.lean`\n"
                "- `Problems/T1.lean`\n",
                encoding="utf-8",
            )
            ctx = SimpleNamespace(
                project_path=root,
                state_dir=state,
                progress_file=state / "PROGRESS.md",
                iter_meta=state / "meta.json",
                dry_run=False,
                options=SimpleNamespace(
                    multilane_preview=False,
                    multilane_execute=True,
                    parallel=False,
                ),
            )
            phase = ProverPhase(ctx)
            with (
                patch.object(
                    phase, "_review_gate_allows_dispatch", return_value=True,
                ),
                patch.object(phase, "_run_serial") as serial,
                patch.object(phase, "_run_parallel") as parallel,
                patch.object(phase, "_run_multilane_execute") as multilane,
            ):
                phase._dispatch()

            serial.assert_called_once_with()
            parallel.assert_not_called()
            multilane.assert_not_called()
            self.assertEqual(
                parse_objectives_with_modes(state / "PROGRESS.md", root),
                [(module, "mathlib-build")],
            )

    def test_multilane_preview_fails_closed_for_shared_batch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text("def Formula := Nat\n", encoding="utf-8")
            (state / "PROGRESS.md").write_text(
                "# Progress\n\n## Current Stage\n\nprover\n\n"
                "## Current Objectives\n\n"
                "- `IChO2026Chem/Core/Formula.lean`\n"
                "- `Problems/T1.lean`\n",
                encoding="utf-8",
            )
            ctx = SimpleNamespace(
                project_path=root,
                state_dir=state,
                progress_file=state / "PROGRESS.md",
                iter_meta=state / "meta.json",
                dry_run=False,
                options=SimpleNamespace(
                    multilane_preview=True,
                    multilane_execute=False,
                    parallel=False,
                ),
            )
            phase = ProverPhase(ctx)
            with (
                patch.object(
                    phase, "_review_gate_allows_dispatch", return_value=True,
                ),
                patch.object(phase, "_run_serial") as serial,
                patch.object(phase, "_run_multilane_preview") as multilane,
            ):
                phase._dispatch()

            serial.assert_not_called()
            multilane.assert_not_called()
            self.assertEqual(
                parse_objectives_with_modes(state / "PROGRESS.md", root),
                [(module, "mathlib-build")],
            )

    def test_successful_build_resolves_module_and_reopens_all_dependents(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._register(root, state, "Problems/T1.lean", ["Formula"])
            self._register(root, state, "Problems/T9.lean", ["charge"])
            module = root / "IChO2026Chem" / "Core" / "Formula.lean"
            module.parent.mkdir(parents=True)
            module.write_text(
                "def Formula := Nat\ndef charge := 0\n"
                "theorem formula_ok : True := by trivial\n",
                encoding="utf-8",
            )
            gate = {
                "version": 2,
                "max_iterations": 3,
                "targets": {
                    target: {
                        "status": "blocked_infrastructure",
                        "attempts": 1,
                        "reason": "missing shared Formula",
                        "infrastructure_request": {
                            "kind": PROJECT_LOCAL_KIND,
                            "module": "IChO2026Chem/Core/Formula.lean",
                            "declarations": ["Formula"],
                        },
                        "history": [],
                    }
                    for target in ("Problems/T1.lean", "Problems/T9.lean")
                },
            }
            (state / "proof-review-gate.json").write_text(
                json.dumps(gate), encoding="utf-8",
            )

            # Placeholder-free source alone is insufficient: a subsequent
            # successful full project build is required.
            before = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(before.resolved_modules, ())

            iter_log = state / "logs" / "iter-002"
            iter_log.mkdir(parents=True)
            (iter_log / "axiom-sweep.json").write_text(json.dumps({
                # Another target may fail in the same sweep; module-specific
                # evidence remains valid when this module itself is clean.
                "ran": False,
                "targetFiles": ["IChO2026Chem/Core/Formula.lean"],
                "failedFiles": ["Problems/Other.lean"],
                "sorryLaunderings": [
                    {"decl": "Other.bad", "axiom": "sorryAx", "file": "Problems/Other.lean"},
                ],
                "otherNonStandardAxioms": [],
            }), encoding="utf-8")
            meta = iter_log / "meta.json"
            meta.write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")
            # Even a clean direct sweep + successful project build does not
            # suffice unless Lake emitted the requested module's olean.
            not_in_graph = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(not_in_graph.resolved_modules, ())
            olean = (
                root / ".lake" / "build" / "lib" / "lean"
                / "IChO2026Chem" / "Core" / "Formula.olean"
            )
            olean.parent.mkdir(parents=True)
            olean.write_bytes(b"compiled")
            result = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                result.verified_modules,
                ("IChO2026Chem/Core/Formula.lean",),
            )
            self.assertEqual(result.resolved_modules, ())
            self.assertEqual(result.reopened_targets, ())
            migrations = pending_shared_consumer_migrations(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                [item.target_path for item in migrations],
                ["Problems/T1.lean", "Problems/T9.lean"],
            )
            migration_prompt = shared_infrastructure_prompt_block(
                state_dir=state, project_path=root,
            )
            self.assertIn("Mandatory consumer import migration", migration_prompt)
            self.assertIn("`refactor`", migration_prompt)
            self.assertIn("import IChO2026Chem.Core.Formula", migration_prompt)
            self.assertIn("no prover dispatch this iter", migration_prompt)
            problems = root / "Problems"
            problems.mkdir()
            for name in ("T1", "T9"):
                (problems / f"{name}.lean").write_text(
                    "import IChO2026Chem.Core.Formula\n"
                    f"theorem {name.lower()} : True := by trivial\n",
                    encoding="utf-8",
                )
            iter3 = state / "logs" / "iter-003"
            iter3.mkdir()
            (iter3 / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")
            migrated = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                migrated.resolved_modules,
                ("IChO2026Chem/Core/Formula.lean",),
            )
            reopened = reopen_resolved_shared_dependents(
                state_dir=state, result=migrated, iter_num=4,
            )
            self.assertEqual(
                reopened, ("Problems/T1.lean", "Problems/T9.lean"),
            )
            updated_gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertTrue(all(
                record["status"] == "retry"
                for record in updated_gate["targets"].values()
            ))
            queue = load_shared_infrastructure_state(state)
            self.assertEqual(
                queue["modules"]["IChO2026Chem/Core/Formula.lean"]["status"],
                "resolved",
            )

            # A new consumer requesting only the existing API reuses module
            # verification and queues migration rather than rebuilding it.
            reused, error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T2.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "IChO2026Chem/Core/Formula.lean",
                    "declarations": ["Formula"],
                },
                reason="another consumer",
                evidence="unknown identifier Formula",
                iter_num=4,
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(reused)
            queue = load_shared_infrastructure_state(state)
            reused_record = queue["modules"]["IChO2026Chem/Core/Formula.lean"]
            self.assertEqual(reused_record["status"], "verified_awaiting_migration")
            self.assertTrue(reused_record["verified_sha256"])

            # A later request enlarging the module contract invalidates every
            # old verification artifact and starts a fresh build epoch.
            updated, error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T1.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "IChO2026Chem/Core/Formula.lean",
                    "declarations": ["Formula", "charge", "molarMass"],
                },
                reason="molar mass is also shared",
                evidence="unknown identifier molarMass",
                iter_num=5,
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(updated)
            queue = load_shared_infrastructure_state(state)
            record = queue["modules"]["IChO2026Chem/Core/Formula.lean"]
            self.assertEqual(record["status"], "pending")
            self.assertEqual(record["requested_iter"], 5)
            self.assertIsNone(record["verified_sha256"])

    def test_target_waits_until_all_shared_modules_are_resolved(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            target = "Problems/T1.lean"
            for module, declaration in (
                ("IChO2026Chem/Core/Formula.lean", "Formula"),
                ("IChO2026Chem/Core/Reaction.lean", "Reaction"),
            ):
                request, error = register_shared_infrastructure_request(
                    state_dir=state,
                    project_path=root,
                    target_rel=target,
                    raw_request={
                        "kind": PROJECT_LOCAL_KIND,
                        "module": module,
                        "declarations": [declaration],
                    },
                    reason="two shared prerequisites",
                    evidence=f"unknown identifier {declaration}",
                    iter_num=1,
                )
                self.assertEqual(error, "")
                self.assertIsNotNone(request)

            formula = root / "IChO2026Chem" / "Core" / "Formula.lean"
            formula.parent.mkdir(parents=True)
            formula.write_text("def Formula := Nat\n", encoding="utf-8")
            formula_olean = (
                root / ".lake" / "build" / "lib" / "lean"
                / "IChO2026Chem" / "Core" / "Formula.olean"
            )
            formula_olean.parent.mkdir(parents=True)
            formula_olean.write_bytes(b"compiled")
            iter2 = state / "logs" / "iter-002"
            iter2.mkdir(parents=True)
            (iter2 / "axiom-sweep.json").write_text(json.dumps({
                "ran": True,
                "targetFiles": ["IChO2026Chem/Core/Formula.lean"],
                "failedFiles": [],
                "sorryLaunderings": [],
                "otherNonStandardAxioms": [],
            }), encoding="utf-8")
            (iter2 / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")
            first = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                first.verified_modules,
                ("IChO2026Chem/Core/Formula.lean",),
            )
            self.assertEqual(first.reopened_targets, ())

            reaction = root / "IChO2026Chem" / "Core" / "Reaction.lean"
            reaction.write_text("def Reaction := Nat\n", encoding="utf-8")
            reaction_olean = (
                root / ".lake" / "build" / "lib" / "lean"
                / "IChO2026Chem" / "Core" / "Reaction.olean"
            )
            reaction_olean.write_bytes(b"compiled")
            iter3 = state / "logs" / "iter-003"
            iter3.mkdir(parents=True)
            (iter3 / "axiom-sweep.json").write_text(json.dumps({
                "ran": True,
                "targetFiles": ["IChO2026Chem/Core/Reaction.lean"],
                "failedFiles": [],
                "sorryLaunderings": [],
                "otherNonStandardAxioms": [],
            }), encoding="utf-8")
            (iter3 / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")
            second = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                second.verified_modules,
                ("IChO2026Chem/Core/Reaction.lean",),
            )
            self.assertEqual(second.reopened_targets, ())
            consumer = root / target
            consumer.parent.mkdir(exist_ok=True)
            consumer.write_text(
                "import IChO2026Chem.Core.Formula\n"
                "import IChO2026Chem.Core.Reaction\n"
                "theorem t : True := by trivial\n",
                encoding="utf-8",
            )
            iter4 = state / "logs" / "iter-004"
            iter4.mkdir(parents=True)
            (iter4 / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")
            migrated = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                migrated.resolved_modules,
                (
                    "IChO2026Chem/Core/Formula.lean",
                    "IChO2026Chem/Core/Reaction.lean",
                ),
            )
            self.assertEqual(migrated.reopened_targets, (target,))

    def test_consumer_edit_invalidates_resolved_migration(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            _, consumer = self._seed_resolved_module(root, state)

            consumer.write_text(
                "theorem t : True := by trivial\n", encoding="utf-8",
            )
            result = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )

            self.assertEqual(result.resolved_modules, ())
            self.assertEqual(result.reopened_targets, ())
            record = load_shared_infrastructure_state(state)["modules"][
                "IChO2026Chem/Core/Formula.lean"
            ]
            self.assertEqual(record["status"], "verified_awaiting_migration")
            self.assertNotIn("Problems/T1.lean", record["consumer_migrations"])
            self.assertEqual(
                pending_shared_consumer_migrations(
                    state_dir=state, project_path=root,
                )[0].target_path,
                "Problems/T1.lean",
            )

    def test_repeat_request_requires_a_new_consumer_build_epoch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            module, _ = self._seed_resolved_module(root, state)
            # --resume may reuse the same iteration directory. Its old build
            # must not satisfy a Review request written later in iter 5.
            old_log = state / "logs" / "iter-005"
            old_log.mkdir(parents=True)
            (old_log / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True, "completedAtEpoch": time.time(),
                }},
            }), encoding="utf-8")

            request, error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T1.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "IChO2026Chem/Core/Formula.lean",
                    "declarations": ["Formula"],
                },
                reason="review requested the shared API again",
                evidence="consumer still failed",
                iter_num=5,
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(request)
            record = load_shared_infrastructure_state(state)["modules"][
                "IChO2026Chem/Core/Formula.lean"
            ]
            self.assertEqual(record["status"], "verified_awaiting_migration")
            self.assertEqual(
                record["consumer_request_iters"]["Problems/T1.lean"], 5,
            )
            self.assertNotIn("Problems/T1.lean", record["consumer_migrations"])

            stale = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(stale.resolved_modules, ())
            self.assertEqual(stale.reopened_targets, ())

            (old_log / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True,
                    "completedAtEpoch": record["consumer_request_epochs"]
                        ["Problems/T1.lean"] + 1.0,
                }},
            }), encoding="utf-8")
            fresh = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(
                fresh.resolved_modules,
                ("IChO2026Chem/Core/Formula.lean",),
            )
            self.assertEqual(fresh.reopened_targets, ("Problems/T1.lean",))
            self.assertTrue(module.is_file())

    def test_proof_edits_preserve_migration_while_import_is_present(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            _, consumer = self._seed_resolved_module(root, state)

            consumer.write_text(
                "import IChO2026Chem.Core.Formula\n"
                "theorem t : 1 + 1 = 2 := by decide\n",
                encoding="utf-8",
            )
            reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            record = load_shared_infrastructure_state(state)["modules"][
                "IChO2026Chem/Core/Formula.lean"
            ]
            self.assertEqual(record["status"], "resolved")
            self.assertIn("Problems/T1.lean", record["consumer_migrations"])

    def test_consumer_must_compile_even_when_default_lake_build_passes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_resolved_module(root, state)
            (root / "lakefile.toml").write_text(
                'name = "consumer_gate"\n', encoding="utf-8",
            )
            request, error = register_shared_infrastructure_request(
                state_dir=state,
                project_path=root,
                target_rel="Problems/T1.lean",
                raw_request={
                    "kind": PROJECT_LOCAL_KIND,
                    "module": "IChO2026Chem/Core/Formula.lean",
                    "declarations": ["Formula"],
                },
                reason="recheck the consumer",
                evidence="",
                iter_num=3,
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(request)
            record = load_shared_infrastructure_state(state)["modules"][
                "IChO2026Chem/Core/Formula.lean"
            ]
            iter3 = state / "logs" / "iter-003"
            iter3.mkdir(parents=True)
            (iter3 / "meta.json").write_text(json.dumps({
                "finalize": {"lake": {
                    "ok": True,
                    "completedAtEpoch": record["consumer_request_epochs"]
                        ["Problems/T1.lean"] + 1.0,
                }},
            }), encoding="utf-8")

            with patch(
                "archon.commands.loop.shared_infrastructure.subprocess.run",
                return_value=SimpleNamespace(returncode=1),
            ):
                failed = reconcile_shared_infrastructure(
                    state_dir=state, project_path=root,
                )
            self.assertEqual(failed.resolved_modules, ())
            self.assertEqual(failed.reopened_targets, ())

            with patch(
                "archon.commands.loop.shared_infrastructure.subprocess.run",
                return_value=SimpleNamespace(returncode=0),
            ):
                passed = reconcile_shared_infrastructure(
                    state_dir=state, project_path=root,
                )
            self.assertEqual(
                passed.resolved_modules,
                ("IChO2026Chem/Core/Formula.lean",),
            )
            self.assertEqual(passed.reopened_targets, ("Problems/T1.lean",))

    def test_external_blocker_is_not_cleared_by_old_local_request(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_resolved_module(root, state)
            gate = {
                "version": 2,
                "targets": {
                    "Problems/T1.lean": {
                        "status": "blocked_infrastructure",
                        "infrastructure_request": {
                            "kind": EXTERNAL_KIND,
                            "package": "crnt-lean",
                        },
                        "history": [],
                    },
                },
            }
            (state / "proof-review-gate.json").write_text(
                json.dumps(gate), encoding="utf-8",
            )

            result = reconcile_shared_infrastructure(
                state_dir=state, project_path=root,
            )
            self.assertEqual(result.reopened_targets, ("Problems/T1.lean",))
            self.assertEqual(
                reopen_resolved_shared_dependents(
                    state_dir=state, result=result, iter_num=3,
                ),
                (),
            )
            unchanged = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                unchanged["targets"]["Problems/T1.lean"]["status"],
                "blocked_infrastructure",
            )


if __name__ == "__main__":
    unittest.main()
