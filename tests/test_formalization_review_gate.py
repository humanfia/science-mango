import json
import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace
from pathlib import Path

from archon.commands.loop.command import parse_from_phase
from archon.commands.loop.phases.review import (
    ReviewPhase,
    _load_domain_reviewer_blockers,
)
from archon.commands.loop.formalization_review_gate import (
    apply_formalization_review,
    apply_target_formalization_review,
    enforce_progress_review_gate,
    load_gate_state,
)
from archon.commands.loop import formalization_review_gate
from archon.commands.loop.review_source_contract import (
    build_review_source_contract,
    source_contract_provenance,
)
from archon.commands.loop.problem_only_review_contract import (
    ProblemOnlyReviewContractError,
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

    def test_state_writer_updates_precreated_inode_when_parent_blocks_tempfile(self):
        path = self.state / "formalization-review-gate.json"
        path.write_text("{}\n", encoding="utf-8")
        inode = path.stat().st_ino
        with mock.patch.object(
            Path, "write_bytes", side_effect=PermissionError("controller-owned parent")
        ):
            formalization_review_gate._write_state(
                self.state, {"version": 1, "targets": {}}
            )
        self.assertEqual(path.stat().st_ino, inode)
        self.assertEqual(json.loads(path.read_text()), {"version": 1, "targets": {}})
        self.assertFalse(path.with_suffix(".json.tmp").exists())

    def _write_progress(self, stage):
        self.progress.write_text(
            "# Progress\n\n## Current Stage\n\n"
            + stage
            + "\n\n## Stages\n\n- autoformalize\n- prover\n\n"
            + "## Current Objectives\n\n- **`Problems/p.lean`** — target\n",
            encoding="utf-8",
        )

    def _set_chemistry_profile(self):
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
        image = self.project / "images" / "p.png"
        image.parent.mkdir()
        image.write_bytes(b"chemistry source image")
        report = self.project / "reports" / "p.source.json"
        report.parent.mkdir()
        previous_parts = []
        report.write_text(json.dumps({
            "output_lean": "Problems/p.lean",
            "entry": {
                "current_question": "Prove p.",
                "answer": "p is true.",
                "previous_parts": previous_parts,
                "image_paths": ["images/p.png"],
            },
            "previous_parts": previous_parts,
        }), encoding="utf-8")
        chapter = (
            self.project / "blueprint" / "src" / "chapters" / "Problems_p.tex"
        )
        chapter.parent.mkdir(parents=True)
        chapter.write_text(
            "% archon:chemistry\n"
            "% archon:source-report reports/p.source.json\n"
            "The official target is p.\n",
            encoding="utf-8",
        )

    def _chemistry_passing_certificate(self) -> dict:
        certificate = self._passing_certificate()
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        certificate.update({
            "source_contract": source_contract_provenance(contract),
            "independent_source_audit": {
                name: {"status": "passed", "evidence": f"{name} audited"}
                for name in (
                    "requested_outputs", "official_answer", "image_grounding",
                    "domain_invariants", "reporting_convention",
                    "adversarial_counterexample",
                )
            },
            "contract_audit": {
                name: {"status": "passed", "evidence": f"{name} audited"}
                for name in (
                    "statement_scope", "hypothesis_derivability",
                    "conclusion_alignment", "bridge_completeness",
                )
            },
            "requested_outputs": [{
                "source_requirement": "prove p",
                "lean_carrier": "p",
                "status": "covered",
                "evidence": "p carries the official output",
            }],
            "official_answer_alignment": {
                "status": "aligned", "evidence": "p matches the rubric",
            },
            "blueprint_conflicts": [],
            "image_audit": [{
                **item,
                "inspected": True,
                "evidence": "source image inspected",
            } for item in source_contract_provenance(contract)["images"]],
            "chemistry_checks": {
                name: {"status": "passed", "evidence": f"{name} audited"}
                for name in (
                    "chemical_semantics", "formula_mass_consistency",
                    "conservation_laws", "units_dimensions",
                    "numerical_reporting", "structure_stereochemistry",
                    "identification_uniqueness", "answer_smuggling",
                )
            },
        })
        return certificate

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

    @staticmethod
    def _grounding_blocker(reason="LeanExplore grounding evidence is incomplete"):
        return {
            "source": "physics_grounding_problems",
            "file": "Problems/p.lean",
            "kind": "incomplete-grounding-log",
            "reason": reason,
        }

    def _review(
        self,
        iteration,
        status,
        reason="review verdict",
        formalization_review=None,
        blockers=(),
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
            blockers=blockers,
        )

    def test_forged_native_batch_milestone_fails_closed(self):
        expected = {"contract_kind": "native_problem_input_only"}
        with mock.patch.object(
            formalization_review_gate,
            "resolve_target_review_source_contract",
            return_value=expected,
        ):
            result = self._review(1, "passed")

        self.assertEqual(result.passed, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertIn("source_contract provenance is missing", record["reason"])

    def test_forged_native_immediate_milestone_fails_closed(self):
        milestone = {
            "status": "solved",
            "target": {"file": "Problems/p.lean", "theorem": "p"},
            "formalization_review": self._passing_certificate(),
        }

        update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=milestone,
            iter_num=1,
            max_iterations=3,
            event_id="pipeline:1:Problems/p.lean:formalization:1",
            expected_source_contract={
                "contract_kind": "native_problem_input_only",
            },
        )

        self.assertFalse(update.passed)
        self.assertEqual(update.status, "retry")
        self.assertIn("source_contract provenance is missing", update.reason)

    def test_bad_native_source_target_does_not_collapse_batch(self):
        good = self.project / "Problems" / "good.lean"
        good.write_text("theorem good : True := by sorry\n", encoding="utf-8")
        session = self.state / "proof-journal" / "sessions" / "session_1"
        session.mkdir(parents=True)
        rows = [
            {
                "status": "solved",
                "target": {"file": "Problems/p.lean", "theorem": "p"},
                "formalization_review": self._passing_certificate(),
            },
            {
                "status": "solved",
                "target": {"file": "Problems/good.lean", "theorem": "good"},
                "formalization_review": self._passing_certificate(),
            },
        ]
        (session / "milestones.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in rows),
            encoding="utf-8",
        )

        def resolve(*, target, **_kwargs):
            if target.name == "p.lean":
                raise ProblemOnlyReviewContractError("sealed report is invalid")
            return {}

        with mock.patch.object(
            formalization_review_gate,
            "resolve_target_review_source_contract",
            side_effect=resolve,
        ):
            result = apply_formalization_review(
                state_dir=self.state,
                project_path=self.project,
                progress_file=self.progress,
                session_dir=session,
                iter_num=1,
                reviewed_objectives=[self.target, good],
                max_iterations=3,
            )

        self.assertEqual(result.passed, ("Problems/good.lean",))
        self.assertEqual(result.retry, ("Problems/p.lean",))
        records = load_gate_state(self.state)["targets"]
        self.assertIn(
            "problem-only source contract validation failed",
            records["Problems/p.lean"]["reason"],
        )
        self.assertEqual(records["Problems/good.lean"]["status"], "passed")

    def test_native_formalization_freshness_ignores_proof_body_hash(self):
        provenance = {
            "contract_kind": "native_problem_input_only",
            "candidate_sha256": "old-formalization-candidate",
        }
        state = {
            "version": 2,
            "max_iterations": 3,
            "targets": {
                "Problems/p.lean": {
                    "status": "passed",
                    "reviews": 1,
                    "certificate": {"source_contract": provenance},
                },
            },
        }

        with (
            mock.patch.object(
                formalization_review_gate,
                "load_domain_profile",
                return_value=SimpleNamespace(name="chemistry-native"),
            ),
            mock.patch.object(
                formalization_review_gate,
                "stored_review_provenance_matches_current",
                return_value=(True, ""),
            ) as freshness,
        ):
            current = formalization_review_gate._invalidate_stale_passes(
                state_dir=self.state,
                project_path=self.project,
                state=state,
            )

        self.assertEqual(
            current["targets"]["Problems/p.lean"]["status"],
            "passed",
        )
        freshness.assert_called_once_with(
            project_path=self.project,
            target=self.target,
            provenance=provenance,
            bind_candidate=False,
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

    def test_semantic_failure_and_grounding_blockers_are_both_preserved(self):
        review = self._passing_certificate()
        review["status"] = "failed"
        review["reason"] = "the requested product is assumed rather than derived"
        review["checks"]["derivability"] = {
            "status": "failed",
            "evidence": "the answer occurs in a structure field",
        }
        blockers = (
            self._grounding_blocker(),
            self._grounding_blocker("local-abstraction evidence is missing"),
        )

        result = self._review(
            1,
            "failed",
            formalization_review=review,
            blockers=blockers,
        )

        self.assertEqual(result.retry, ("Problems/p.lean",))
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertIn(review["reason"], record["reason"])
        self.assertIn(blockers[0]["reason"], record["reason"])
        self.assertIn(blockers[1]["reason"], record["reason"])
        failed_certificate = record["certificate"]["milestones"][0]
        self.assertEqual(failed_certificate["status"], "failed")
        self.assertEqual(
            failed_certificate["checks"]["derivability"]["evidence"],
            "the answer occurs in a structure field",
        )

        clean_result = self._review(
            2,
            "failed",
            formalization_review=review,
        )
        self.assertEqual(clean_result.retry, ("Problems/p.lean",))
        clean_record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertIn(review["reason"], clean_record["reason"])
        self.assertNotIn(blockers[0]["reason"], clean_record["reason"])

    def test_semantic_pass_with_grounding_blocker_retries_and_keeps_certificate(self):
        blocker = self._grounding_blocker()

        result = self._review(1, "passed", blockers=(blocker,))

        self.assertEqual(result.passed, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertIn("all formalization Review entries passed", record["reason"])
        self.assertIn(blocker["reason"], record["reason"])
        passing_certificate = record["certificate"]["milestones"][0]
        self.assertEqual(passing_certificate["schema_version"], 2)
        self.assertEqual(
            passing_certificate["checks"]["derivability"]["status"],
            "passed",
        )

    def test_clean_semantic_pass_remains_eligible_after_grounding_retry(self):
        blocker = self._grounding_blocker()
        blocked = self._review(1, "passed", blockers=(blocker,))
        self.assertEqual(blocked.retry, ("Problems/p.lean",))

        clean = self._review(2, "passed")

        self.assertEqual(clean.passed, ("Problems/p.lean",))
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "passed")
        self.assertEqual(record["reason"], "all formalization Review entries passed")

    def test_batch_gate_persists_verified_official_source_conflict(self):
        self._set_chemistry_profile()
        review = self._chemistry_passing_certificate()
        review["official_answer_alignment"] = {
            "status": "conflict",
            "evidence": "official final answer contradicts the displayed data",
        }
        review["source_inconsistency"] = {
            "kind": "official_internal_contradiction",
            "status": "verified",
            "official_claim": "the rubric says 1.94",
            "derived_claim": "the rubric data derive 1.93",
            "derivation_carrier": "p.source_data_round_to_1_93",
            "evidence": "the Lean carrier proves the displayed-data rounding",
        }

        result = self._review(
            1,
            "passed",
            formalization_review=review,
        )

        self.assertEqual(result.passed, ("Problems/p.lean",))
        certificate = load_gate_state(self.state)["targets"][
            "Problems/p.lean"
        ]["certificate"]["milestones"][0]
        self.assertEqual(
            certificate["official_answer_alignment"],
            review["official_answer_alignment"],
        )
        self.assertEqual(
            certificate["source_inconsistency"],
            review["source_inconsistency"],
        )

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

    def test_chemistry_modes_survive_retry_pass_and_gate_rewrite(self):
        self._set_chemistry_profile()

        failed = self._review(1, "failed")
        self.assertEqual(failed.retry, ("Problems/p.lean",))
        self.assertIn(
            "[prover-mode: chemistry-formalize]",
            self.progress.read_text(encoding="utf-8"),
        )

        passed = self._review(
            2,
            "passed",
            formalization_review=self._chemistry_passing_certificate(),
        )
        self.assertEqual(passed.passed, ("Problems/p.lean",))
        self.assertEqual(read_stage(self.progress), "prover")
        self.assertIn(
            "[prover-mode: chemistry]",
            self.progress.read_text(encoding="utf-8"),
        )

        blocked = self.project / "Problems" / "blocked.lean"
        blocked.write_text("theorem blocked : True := by sorry\n", encoding="utf-8")
        self.progress.write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Stages\n\n- autoformalize\n- prover\n\n"
            "## Current Objectives\n\n"
            "- **`Problems/p.lean`** — passed target\n"
            "- **`Problems/blocked.lean`** — missing certificate\n",
            encoding="utf-8",
        )
        kept, dropped = enforce_progress_review_gate(
            progress_file=self.progress,
            state_dir=self.state,
            project_path=self.project,
            stage="prover",
            enabled=True,
        )
        self.assertEqual(kept, [self.target])
        self.assertEqual(dropped, [(blocked, "missing formalization Review certificate")])
        progress = self.progress.read_text(encoding="utf-8")
        self.assertIn("[prover-mode: chemistry]", progress)
        self.assertNotIn("[prover-mode: physics]", progress)

    def test_chemistry_must_fix_overrides_passing_milestone(self):
        self._set_chemistry_profile()
        reports = self.state / "task_results"
        reports.mkdir()
        report = reports / "chemistry-reviewer-p.md"
        report.write_text(
            "## Must-fix-this-iter\n"
            "- Problems/p.lean:p — current answer is assumed by the contract.\n"
            "\n"
            "## Overall verdict\n"
            "SOUND\n",
            encoding="utf-8",
        )
        blockers = _load_domain_reviewer_blockers(self.state, self.project)

        result = self._review(
            1,
            "passed",
            formalization_review=self._chemistry_passing_certificate(),
            blockers=blockers,
        )

        self.assertEqual(len(blockers), 1)
        self.assertEqual(blockers[0]["source"], "chemistry-reviewer")
        self.assertEqual(result.passed, ())
        self.assertEqual(result.retry, ("Problems/p.lean",))
        self.assertEqual(read_stage(self.progress), "autoformalize")
        record = load_gate_state(self.state)["targets"]["Problems/p.lean"]
        self.assertEqual(record["status"], "retry")
        self.assertIn("semantic Review passed", record["reason"])
        self.assertIn("current answer is assumed by the contract", record["reason"])

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
