from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.formalization_review_gate import (
    apply_target_formalization_review,
    filter_objectives_for_review_gate,
    load_gate_state,
)
from archon.commands.loop.parallel_formalization_review import (
    build_target_formalization_review_prompt,
    load_target_formalization_milestone,
)
from archon.commands.loop.parallel_review import (
    build_target_review_prompt,
    load_target_milestone,
)
from archon.commands.loop.proof_review_gate import (
    apply_proof_review,
    apply_target_proof_review,
    filter_objectives_for_proof_review_gate,
    load_proof_review_state,
)
from archon.commands.loop.review_source_contract import (
    SOURCE_AUTHORITY,
    SOURCE_INCONSISTENCY_KIND,
    build_review_source_contract,
    render_source_contract_prompt,
    source_contract_provenance,
    stored_provenance_matches_current,
    validate_review_source_certificate,
)


class ReviewSourceContractTest(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory()
        self.project = Path(self.tempdir.name)
        self.state = self.project / ".archon"
        self.state.mkdir()
        (self.state / "config.json").write_text(
            json.dumps({"loop": {"domain_profile": {"name": "chemistry"}}}),
            encoding="utf-8",
        )
        self.target = self.project / "Problems" / "T5.lean"
        self.target.parent.mkdir()
        self.target.write_text("theorem identify_X : True := by trivial\n")
        self.chapter = (
            self.project / "blueprint" / "src" / "chapters" / "Problems_T5.tex"
        )
        self.chapter.parent.mkdir(parents=True)
        self.report = self.project / "reports" / "t5.source.json"
        self.report.parent.mkdir()
        self.image = self.project / "images" / "t5.png"
        self.image.parent.mkdir()
        self.image.write_bytes(b"source-image-v1")
        self._write_bundle()

    def tearDown(self):
        self.tempdir.cleanup()

    def _write_bundle(
        self,
        *,
        blueprint_target: str = "The formal target identifies X as IBr.",
        answer: str = "The calculation gives A_Hal = 79.9, so X is IBr.",
    ) -> None:
        self.chapter.write_text(
            "% archon:chemistry\n"
            "% archon:covers Problems/T5.lean\n"
            "% archon:source-report reports/t5.source.json\n"
            f"Official target commentary: {blueprint_target}\n",
            encoding="utf-8",
        )
        previous = [{
            "part_id": "T5-A3",
            "question": "Determine the fatty-acid formula.",
            "answer": "C18H32O2",
        }]
        self.report.write_text(
            json.dumps({
                "schema_version": 2,
                "output_lean": "Problems/T5.lean",
                "domain": "chemistry",
                "entry": {
                    "current_question": (
                        "Determine the molecular formula of X and support it "
                        "with calculations."
                    ),
                    "answer": answer,
                    "previous_parts": previous,
                    "image_paths": ["images/t5.png"],
                },
                "previous_parts": previous,
            }, ensure_ascii=False),
            encoding="utf-8",
        )

    @staticmethod
    def _chemistry_checks(*, numerical: str = "passed") -> dict:
        statuses = {
            "chemical_semantics": "passed",
            "formula_mass_consistency": "passed",
            "conservation_laws": "passed",
            "units_dimensions": "passed",
            "numerical_reporting": numerical,
            "structure_stereochemistry": "not_applicable",
            "identification_uniqueness": "passed",
            "answer_smuggling": "passed",
        }
        return {
            name: {"status": status, "evidence": f"{name} audited"}
            for name, status in statuses.items()
        }

    def _source_audit(
        self,
        contract: dict,
        *,
        output_status: str = "covered",
        alignment: str = "aligned",
        conflicts: list[dict] | None = None,
        numerical: str = "passed",
        source_inconsistency: dict | None = None,
    ) -> dict:
        independent = {
            name: {"status": "passed", "evidence": f"{name} source-only audit"}
            for name in (
                "requested_outputs",
                "official_answer",
                "image_grounding",
                "domain_invariants",
                "reporting_convention",
                "adversarial_counterexample",
            )
        }
        contract_audit = {
            name: {"status": "passed", "evidence": f"{name} contract audit"}
            for name in (
                "statement_scope",
                "hypothesis_derivability",
                "conclusion_alignment",
                "bridge_completeness",
            )
        }
        if output_status == "blocked":
            independent["requested_outputs"]["status"] = "failed"
            contract_audit["conclusion_alignment"]["status"] = "failed"
        if numerical == "failed":
            independent["reporting_convention"]["status"] = "failed"
        audit = {
            "source_contract": source_contract_provenance(contract),
            "independent_source_audit": independent,
            "contract_audit": contract_audit,
            "requested_outputs": [{
                "source_requirement": "identify X and show the calculation",
                "lean_carrier": "identify_X",
                "status": output_status,
                "evidence": "the conclusion states X = IBr",
            }],
            "official_answer_alignment": {
                "status": alignment,
                "evidence": "Lean conclusion compared with official IBr rubric",
            },
            "blueprint_conflicts": conflicts or [],
            "image_audit": [{
                **image,
                "inspected": True,
                "evidence": "reaction scheme and displayed formula inspected",
            } for image in source_contract_provenance(contract)["images"]],
            "chemistry_checks": self._chemistry_checks(numerical=numerical),
        }
        if source_inconsistency is not None:
            audit["source_inconsistency"] = source_inconsistency
        return audit

    @staticmethod
    def _verified_source_inconsistency() -> dict:
        return {
            "kind": SOURCE_INCONSISTENCY_KIND,
            "status": "verified",
            "official_claim": "the official final answer states X = 79.9",
            "derived_claim": "the printed givens derive X = 80.9",
            "derivation_carrier": "identify_X.source_data_imply_80_9",
            "evidence": (
                "Substitution into the official displayed equation yields "
                "80.9, and Lean proves both that value and its conflict with 79.9."
            ),
        }

    def _formalization_milestone(self, contract: dict) -> dict:
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
            "status": "not_applicable", "evidence": "no branch",
        }
        return {
            "status": "solved",
            "target": {"file": "Problems/T5.lean", "theorem": "identify_X"},
            "formalization_review": {
                "schema_version": 2,
                "status": "passed",
                "reason": "official target is represented",
                "checks": checks,
                "bridge_obligations": [{
                    "claim": "the measurements determine IBr",
                    "carrier": "identify_X",
                    "status": "covered",
                    "evidence": "the theorem derives the official output",
                }],
                **self._source_audit(contract),
            },
        }

    def _proof_milestone(self, contract: dict) -> dict:
        return {
            "status": "solved",
            "target": {"file": "Problems/T5.lean", "theorem": "identify_X"},
            "proof_review": {
                "schema_version": 1,
                "route": "solved",
                "reason": "proof and official contract pass",
                "evidence": "Lean preflight and source contract audited",
                "redraft_kind": "not_applicable",
                "infrastructure_request": None,
                **self._source_audit(contract),
            },
        }

    def test_contract_contains_first_class_official_evidence_and_hashes(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        self.assertTrue(contract["valid"])
        self.assertTrue(contract["required"])
        self.assertEqual(len(contract["lean_sha256"]), 64)
        self.assertEqual(len(contract["blueprint_sha256"]), 64)
        self.assertEqual(len(contract["source_sha256"]), 64)
        self.assertEqual(len(contract["answer_sha256"]), 64)
        self.assertEqual(len(contract["images"][0]["sha256"]), 64)
        prompt = render_source_contract_prompt(contract)
        self.assertIn(SOURCE_AUTHORITY, prompt)
        self.assertIn("Determine the molecular formula of X", prompt)
        self.assertIn("so X is IBr", prompt)
        self.assertIn("T5-A3", prompt)

        formalization_prompt = build_target_formalization_review_prompt(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.state / "logs" / "iter-001",
            iter_num=1,
            target=self.target,
            output_dir=self.state / "formalization-review",
            preflight={"compiles": True},
            prior_gate_record=None,
            source_contract=contract,
        )
        proof_prompt = build_target_review_prompt(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.state / "logs" / "iter-001",
            iter_num=1,
            target=self.target,
            output_dir=self.state / "proof-review",
            preflight={"compiles": True},
            prior_gate_record=None,
            source_contract=contract,
        )
        for worker_prompt in (formalization_prompt, proof_prompt):
            self.assertIn("Mandatory source-first two-pass protocol", worker_prompt)
            self.assertIn("independent_source_audit", worker_prompt)
            self.assertIn("contract_audit", worker_prompt)
            self.assertIn(contract["source_sha256"], worker_prompt)
            self.assertIn(contract["answer_sha256"], worker_prompt)

    def test_both_prompts_define_the_narrow_source_inconsistency_route(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        prompts = (
            build_target_formalization_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.state / "logs" / "iter-001",
                iter_num=1,
                target=self.target,
                output_dir=self.state / "formalization-review",
                preflight={"compiles": True},
                prior_gate_record=None,
                source_contract=contract,
            ),
            build_target_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.state / "logs" / "iter-001",
                iter_num=1,
                target=self.target,
                output_dir=self.state / "proof-review",
                preflight={"compiles": True},
                prior_gate_record=None,
                source_contract=contract,
            ),
        )
        for prompt in prompts:
            with self.subTest(prompt=prompt.splitlines()[0]):
                self.assertIn('"source_inconsistency"', prompt)
                self.assertIn(
                    '"kind":"official_internal_contradiction"', prompt,
                )
                self.assertIn('"status":"verified"', prompt)
                self.assertIn("official givens or printed intermediates", prompt)
                self.assertIn("Lean explicitly carries", prompt)
                self.assertIn("Otherwise official_answer_alignment", prompt)

    def test_aligned_legacy_audit_passes_without_source_inconsistency(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        audit = self._source_audit(contract)
        self.assertNotIn("source_inconsistency", audit)
        self.assertEqual(
            validate_review_source_certificate(audit, contract, passing=True),
            "",
        )

    def test_passing_conflict_requires_complete_verified_inconsistency(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        conflict = self._source_audit(contract, alignment="conflict")
        self.assertIn(
            "verified source_inconsistency",
            validate_review_source_certificate(conflict, contract, passing=True),
        )

        complete = self._verified_source_inconsistency()
        for bad_kind in (None, "internal_contradiction", "rounding_dispute"):
            with self.subTest(kind=bad_kind):
                wrong_kind = dict(complete)
                if bad_kind is None:
                    wrong_kind.pop("kind")
                else:
                    wrong_kind["kind"] = bad_kind
                self.assertIn(
                    "source_inconsistency kind must be "
                    "official_internal_contradiction",
                    validate_review_source_certificate(
                        self._source_audit(
                            contract,
                            alignment="conflict",
                            source_inconsistency=wrong_kind,
                        ),
                        contract,
                        passing=True,
                    ),
                )

        unverified = dict(complete, status="suspected")
        self.assertIn(
            "status must be verified",
            validate_review_source_certificate(
                self._source_audit(
                    contract,
                    alignment="conflict",
                    source_inconsistency=unverified,
                ),
                contract,
                passing=True,
            ),
        )
        for missing in (
            "official_claim",
            "derived_claim",
            "derivation_carrier",
            "evidence",
        ):
            with self.subTest(missing=missing):
                incomplete = dict(complete)
                incomplete.pop(missing)
                audit = self._source_audit(
                    contract,
                    alignment="conflict",
                    source_inconsistency=incomplete,
                )
                self.assertIn(
                    f"source_inconsistency {missing} is missing",
                    validate_review_source_certificate(
                        audit, contract, passing=True,
                    ),
                )

    def test_verified_source_inconsistency_allows_passing_conflict(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        audit = self._source_audit(
            contract,
            alignment="conflict",
            source_inconsistency=self._verified_source_inconsistency(),
        )
        self.assertEqual(
            validate_review_source_certificate(audit, contract, passing=True),
            "",
        )

        aligned = self._source_audit(
            contract,
            source_inconsistency=self._verified_source_inconsistency(),
        )
        self.assertIn(
            "official_answer_alignment status=conflict",
            validate_review_source_certificate(aligned, contract, passing=True),
        )

    def test_both_target_loaders_accept_a_verified_source_conflict(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        formalization = self._formalization_milestone(contract)
        proof = self._proof_milestone(contract)
        for milestone, review_key in (
            (formalization, "formalization_review"),
            (proof, "proof_review"),
        ):
            review = milestone[review_key]
            review["official_answer_alignment"]["status"] = "conflict"
            review["source_inconsistency"] = (
                self._verified_source_inconsistency()
            )

        formal_path = self.project / "formal-conflict.jsonl"
        proof_path = self.project / "proof-conflict.jsonl"
        formal_path.write_text(json.dumps(formalization) + "\n", encoding="utf-8")
        proof_path.write_text(json.dumps(proof) + "\n", encoding="utf-8")

        self.assertEqual(
            load_target_formalization_milestone(
                formal_path, "Problems/T5.lean", contract,
            )[1],
            "",
        )
        self.assertEqual(
            load_target_milestone(
                proof_path, "Problems/T5.lean", contract,
            )[1],
            "",
        )

    def test_both_gates_persist_normalized_verified_source_conflict(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )
        formalization = self._formalization_milestone(contract)
        proof = self._proof_milestone(contract)
        for milestone, review_key in (
            (formalization, "formalization_review"),
            (proof, "proof_review"),
        ):
            review = milestone[review_key]
            review["official_answer_alignment"] = {
                "status": "CONFLICT",
                "evidence": "  official final claim contradicts its data  ",
            }
            review["source_inconsistency"] = {
                key: f"  {value}  " if isinstance(value, str) else value
                for key, value in self._verified_source_inconsistency().items()
            }
            # The kind is an exact discriminator rather than a token that may
            # be case/whitespace normalized.
            review["source_inconsistency"]["kind"] = (
                SOURCE_INCONSISTENCY_KIND
            )

        formal_update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=formalization,
            iter_num=1,
            max_iterations=3,
            event_id="formal-conflict-1",
        )
        proof_session = self.state / "proof-conflict-session"
        proof_session.mkdir()
        (proof_session / "milestones.jsonl").write_text(
            json.dumps(proof) + "\n",
            encoding="utf-8",
        )
        proof_update = apply_proof_review(
            state_dir=self.state,
            project_path=self.project,
            session_dir=proof_session,
            iter_num=1,
            reviewed_objectives=[self.target],
            max_iterations=3,
        )

        self.assertTrue(formal_update.passed)
        self.assertEqual(proof_update.solved, ("Problems/T5.lean",))
        formal_certificate = load_gate_state(self.state)["targets"][
            "Problems/T5.lean"
        ]["certificate"]
        proof_certificate = load_proof_review_state(self.state)["targets"][
            "Problems/T5.lean"
        ]
        expected_alignment = {
            "status": "conflict",
            "evidence": "official final claim contradicts its data",
        }
        expected_inconsistency = self._verified_source_inconsistency()
        for certificate in (formal_certificate, proof_certificate):
            with self.subTest(certificate=certificate):
                self.assertEqual(
                    certificate["official_answer_alignment"],
                    expected_alignment,
                )
                self.assertEqual(
                    certificate["source_inconsistency"],
                    expected_inconsistency,
                )

    def test_verified_inconsistency_does_not_relax_other_passing_checks(self):
        contract = build_review_source_contract(
            project_path=self.project,
            target=self.target,
        )

        def verified_audit() -> dict:
            return self._source_audit(
                contract,
                alignment="conflict",
                source_inconsistency=self._verified_source_inconsistency(),
            )

        cases = {}
        independent = verified_audit()
        independent["independent_source_audit"]["domain_invariants"][
            "status"
        ] = "failed"
        cases["independent_source_audit"] = independent

        contract_check = verified_audit()
        contract_check["contract_audit"]["bridge_completeness"][
            "status"
        ] = "failed"
        cases["contract_audit"] = contract_check

        requested = verified_audit()
        requested["requested_outputs"][0]["status"] = "blocked"
        cases["requested output"] = requested

        chemistry = verified_audit()
        chemistry["chemistry_checks"]["conservation_laws"]["status"] = "failed"
        cases["chemistry check"] = chemistry

        blueprint = verified_audit()
        blueprint["blueprint_conflicts"] = [{
            "source_claim": "official givens derive 80.9",
            "blueprint_or_lean_claim": "blueprint asserts 79.9 without derivation",
            "status": "unresolved",
            "evidence": "the generated blueprint conflict remains open",
        }]
        cases["blueprint/source conflict"] = blueprint

        for expected_error, audit in cases.items():
            with self.subTest(expected_error=expected_error):
                self.assertIn(
                    expected_error,
                    validate_review_source_certificate(
                        audit, contract, passing=True,
                    ),
                )

    def test_missing_source_or_image_can_never_receive_a_pass(self):
        self.report.unlink()
        missing_source = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(missing_source["valid"])
        audit = self._source_audit(missing_source)
        error = validate_review_source_certificate(
            audit, missing_source, passing=True,
        )
        self.assertIn("source contract is invalid", error)

        self._write_bundle()
        self.image.unlink()
        missing_image = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(missing_image["valid"])
        error = validate_review_source_certificate(
            self._source_audit(missing_image), missing_image, passing=True,
        )
        self.assertIn("image", error)

    def test_stale_source_answer_blueprint_lean_and_image_hashes_are_rejected(self):
        original = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        audit = self._source_audit(original)
        mutations = (
            lambda: self.target.write_text("theorem identify_X : 1 = 1 := rfl\n"),
            lambda: self.chapter.write_text(self.chapter.read_text() + "% changed\n"),
            lambda: self.report.write_text(self.report.read_text() + "\n"),
            lambda: self.image.write_bytes(b"source-image-v2"),
        )
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                mutate()
                current = build_review_source_contract(
                    project_path=self.project, target=self.target,
                )
                error = validate_review_source_certificate(
                    audit, current, passing=True,
                )
                self.assertTrue(error)
                fresh, freshness_reason = stored_provenance_matches_current(
                    project_path=self.project,
                    target=self.target,
                    provenance=source_contract_provenance(original),
                )
                self.assertFalse(fresh)
                self.assertIn("changed", freshness_reason)
                self._write_bundle()
                self.target.write_text("theorem identify_X : True := by trivial\n")
                self.image.write_bytes(b"source-image-v1")

        self._write_bundle(answer="Updated official rubric answer: X is IBr.")
        changed_answer = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertNotEqual(
            original["answer_sha256"], changed_answer["answer_sha256"],
        )
        self.assertTrue(validate_review_source_certificate(
            audit, changed_answer, passing=True,
        ))

    def test_both_target_loaders_mechanically_reject_stale_provenance(self):
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        formal_path = self.project / "formal.jsonl"
        proof_path = self.project / "proof.jsonl"
        formal_path.write_text(
            json.dumps(self._formalization_milestone(contract)) + "\n",
            encoding="utf-8",
        )
        proof_path.write_text(
            json.dumps(self._proof_milestone(contract)) + "\n",
            encoding="utf-8",
        )
        self.assertEqual(
            load_target_formalization_milestone(
                formal_path, "Problems/T5.lean", contract,
            )[1],
            "",
        )
        self.assertEqual(
            load_target_milestone(
                proof_path, "Problems/T5.lean", contract,
            )[1],
            "",
        )

        self.image.write_bytes(b"changed after certificates")
        current = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertIn(
            "image",
            load_target_formalization_milestone(
                formal_path, "Problems/T5.lean", current,
            )[1],
        )
        self.assertIn(
            "image",
            load_target_milestone(
                proof_path, "Problems/T5.lean", current,
            )[1],
        )

    def test_t5_inversion_and_t4_rounding_conflicts_cannot_claim_pass(self):
        self._write_bundle(
            blueprint_target="The data do not identify X; exhibit counterexamples.",
        )
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        inversion = self._source_audit(
            contract,
            output_status="blocked",
            alignment="conflict",
            conflicts=[{
                "source_claim": "identify X as IBr",
                "blueprint_or_lean_claim": "prove X is not identifiable",
                "status": "unresolved",
                "evidence": "the generated target reverses the official task",
            }],
        )
        error = validate_review_source_certificate(
            inversion, contract, passing=True,
        )
        self.assertIn("failed independent_source_audit", error)
        self.assertEqual(
            validate_review_source_certificate(inversion, contract, passing=False),
            "",
        )

        rounding = self._source_audit(
            contract,
            alignment="conflict",
            numerical="failed",
            conflicts=[{
                "source_claim": "report 7.04e12 using rubric rounding",
                "blueprint_or_lean_claim": "report only the raw 7.034e12 interval",
                "status": "unresolved",
                "evidence": "the official reporting convention is not encoded",
            }],
        )
        error = validate_review_source_certificate(
            rounding, contract, passing=True,
        )
        self.assertIn("failed independent_source_audit", error)

    def test_formalization_pass_reopens_when_blueprint_changes(self):
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=self._formalization_milestone(contract),
            iter_num=1,
            max_iterations=3,
            event_id="formalization-1",
        )
        self.assertTrue(update.passed)
        self.chapter.write_text(self.chapter.read_text() + "% poisoned later\n")

        kept, dropped = filter_objectives_for_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            stage="prover",
            enabled=True,
        )
        self.assertEqual(kept, [])
        self.assertEqual(dropped[0][1], "retry")
        self.assertEqual(
            load_gate_state(self.state)["targets"]["Problems/T5.lean"]["status"],
            "retry",
        )
        kept, _ = filter_objectives_for_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            stage="autoformalize",
            enabled=True,
        )
        self.assertEqual(kept, [self.target])

    def test_proof_solved_does_not_hide_changed_lean_file(self):
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        update = apply_target_proof_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=self._proof_milestone(contract),
            iter_num=1,
            max_iterations=3,
            event_id="proof-1",
        )
        self.assertEqual(update.status, "solved")
        self.target.write_text("theorem identify_X : 2 = 2 := rfl\n")

        kept, dropped = filter_objectives_for_proof_review_gate(
            [self.target],
            state_dir=self.state,
            project_path=self.project,
            enabled=True,
            stage="prover",
        )
        self.assertEqual(kept, [self.target])
        self.assertEqual(dropped, [])
        record = load_proof_review_state(self.state)["targets"]["Problems/T5.lean"]
        self.assertEqual(record["status"], "retry")
        self.assertIn("lean_sha256 changed", record["reason"])


if __name__ == "__main__":
    unittest.main()
