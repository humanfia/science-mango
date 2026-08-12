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
    BLIND_SOURCE_AUTHORITY,
    SOURCE_AUTHORITY,
    SOURCE_INCONSISTENCY_KIND,
    blind_result_payload_sha256,
    build_review_source_contract,
    expected_nonnumeric_result_types,
    expected_numeric_result_types,
    lean_result_type_sha256,
    render_source_contract_prompt,
    source_contract_provenance,
    stored_provenance_matches_current,
    validate_review_source_certificate,
    validate_blind_result_contracts,
)


REPORTING_POLICY = {
    "intermediate_rounding": "forbidden",
    "explicit_precision": "use_only_precision_requested_in_problem",
    "default_final_display": "three_significant_figures",
    "final_precision": {
        "kind": "significant_figures",
        "digits": 3,
        "source": "uniform_blind_evaluation_default",
    },
    "tie_rule": "half_away_from_zero",
    "raw_result_required": True,
}
MEASUREMENT_POLICY = {
    "stipulated_constants": "exact_as_printed_unless_problem_calls_them_measured",
    "measured_display_half_width": "one_half_of_last_displayed_quantum",
    "derived_tolerances": "must_be_proved_from_source_measurement_intervals",
}
CANDIDATE_DOMAIN_POLICY = {
    "allowed_sources": ["problem_text", "problem_image", "derived_theorem"],
    "previous_part_results": "derive_inline_from_problem_only_material",
    "unjustified_search_bounds": "forbidden",
    "underdetermined_result": "must_be_reported",
}


def _classification_candidate() -> dict:
    candidate = {
        "schema_version": 1,
        "protocol": "icho-answer-blind-v1",
        "phase": "solve",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "id": "icho_t5_a3",
        "blind_record_sha256": "d" * 64,
        "result_kind": "classification",
        "raw_result": {
            "expression": "derived from source",
            "lean_expression": "BlindFixture.rawClassificationSpec",
        },
        "reported_result": {
            "value": "IBr",
            "text": "independent candidate",
            "lean_expression": "BlindFixture.reportedClassificationSpec",
            "rounding_rule": "half_away_from_zero",
        },
        "reporting_rule_source": REPORTING_POLICY,
        "tolerance_provenance": {
            "measurement_policy": MEASUREMENT_POLICY,
            "derivation": "not_applicable_to_classification",
        },
        "candidate_domain_provenance": {
            "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
            "derivation": {"kind": "source_enumeration", "evidence": "problem_text"},
        },
        "lean_declarations": [
            "BlindFixture.identifyXRaw",
            "BlindFixture.identifyXReported",
        ],
    }
    types = expected_nonnumeric_result_types(candidate)
    assert types is not None
    candidate["lean_result_contracts"] = [
        {
            "role": role,
            "declaration": declaration,
            "expected_type": types[role],
            "expected_type_sha256": lean_result_type_sha256(types[role]),
            "result_payload_sha256": blind_result_payload_sha256(candidate, role),
        }
        for role, declaration in zip(
            ("raw_result", "reported_result"),
            candidate["lean_declarations"],
            strict=True,
        )
    ]
    return candidate


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
        self.target.write_text(
            "namespace BlindFixture\n"
            "def rawClassificationSpec : Prop := True\n"
            "def reportedClassificationSpec : Prop := rawClassificationSpec\n"
            "theorem identifyXRaw : rawClassificationSpec := by trivial\n"
            "theorem identifyXReported : reportedClassificationSpec := by trivial\n"
            "end BlindFixture\n"
        )
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
        candidate_dir = self.project / "blind_candidates"
        candidate_dir.mkdir(exist_ok=True)
        (candidate_dir / "icho_t5_a3.json").write_text(
            json.dumps(_classification_candidate()),
            encoding="utf-8",
        )

    def _write_blind_bundle(self, *, question_field: str = "question") -> None:
        self.chapter.write_text(
            "% archon:chemistry\n"
            "% archon:covers Problems/T5.lean\n"
            "% archon:source-report reports/t5.source.json\n"
            "Blind problem statement only.\n",
            encoding="utf-8",
        )
        previous = [{
            "source_id": "T5-A3",
            "question": "Determine the fatty-acid formula.",
            "dependency_policy": "frozen_blind_proof_only",
            "frozen_artifact_sha256": "a" * 64,
        }]
        entry = {
            "id": "icho_t5_a3",
            "blind_record_sha256": "d" * 64,
            question_field: (
                "Determine the molecular formula of X and support it with "
                "calculations."
            ),
            "previous_parts": previous,
            "image_paths": ["images/t5.png"],
            "reporting_policy": REPORTING_POLICY,
            "measurement_policy": MEASUREMENT_POLICY,
            "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
            "requested_outputs": [{
                "id": "molecular_formula",
                "source_requirement": "molecular formula of X",
                "kind": "formula",
                "unit": "",
                "reporting_policy": {
                    "kind": "exact_symbolic",
                    "source": "requested_outputs",
                },
            }],
        }
        self.report.write_text(
            json.dumps({
                "schema_version": 3,
                "evaluation_mode": "answer_blind",
                "official_answer_seen": False,
                "phase": "solve",
                "blind_record_sha256": "d" * 64,
                "output_lean": "Problems/T5.lean",
                "domain": "chemistry",
                "entry": entry,
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

    def _blind_source_audit(self, contract: dict) -> dict:
        return {
            "source_contract": source_contract_provenance(contract),
            "blind_source_audit": {
                name: {"status": "passed", "evidence": f"{name} audited"}
                for name in (
                    "answer_independence",
                    "raw_derivation",
                    "reporting_rule_source",
                    "tolerance_provenance",
                    "candidate_domain_provenance",
                    "lean_result_binding",
                )
            },
            "contract_audit": {
                name: {"status": "passed", "evidence": f"{name} audited"}
                for name in (
                    "statement_scope",
                    "hypothesis_derivability",
                    "conclusion_alignment",
                    "bridge_completeness",
                )
            },
            "requested_outputs": [{
                "source_requirement": "identify X from the problem data",
                "lean_carrier": "identify_X",
                "status": "covered",
                "evidence": "the candidate follows from the raw derivation",
            }],
            "blueprint_conflicts": [],
            "image_audit": [{
                **image,
                "inspected": True,
                "evidence": "problem image inspected without answer context",
            } for image in source_contract_provenance(contract)["images"]],
            "chemistry_checks": self._chemistry_checks(),
        }

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

    def test_blind_contract_omits_answer_and_binds_problem_provenance(self):
        self._write_blind_bundle()
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertTrue(contract["valid"])
        self.assertEqual(contract["authority"], BLIND_SOURCE_AUTHORITY)
        self.assertEqual(contract["evaluation_mode"], "answer_blind")
        self.assertFalse(contract["official_answer_seen"])
        self.assertNotIn("answer_sha256", contract)
        self.assertNotIn("official_evidence", contract)
        provenance = source_contract_provenance(contract)
        self.assertNotIn("answer_sha256", provenance)
        self.assertEqual(provenance["question_sha256"], contract["question_sha256"])
        self.assertEqual(provenance["entry_id"], "icho_t5_a3")
        self.assertEqual(provenance["blind_record_sha256"], "d" * 64)
        self.assertEqual(
            contract["blind_candidate_record"],
            "blind_candidates/icho_t5_a3.json",
        )
        self.assertEqual(len(provenance["blind_candidate_sha256"]), 64)
        self.assertEqual(
            provenance["previous_blind_hashes"][0]["sha256"], "a" * 64,
        )
        prompt = render_source_contract_prompt(contract)
        self.assertIn("ANSWER-BLIND PROBLEM CONTRACT", prompt)
        self.assertIn("Authority: problem-only", prompt)
        self.assertNotIn("entry.answer", prompt)

    def test_blind_candidate_is_required_and_hash_bound(self):
        self._write_blind_bundle()
        candidate = self.project / "blind_candidates" / "icho_t5_a3.json"
        candidate.unlink()
        missing = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(missing["valid"])
        self.assertIn("candidate is missing", "; ".join(missing["errors"]))

        self._write_bundle()
        self._write_blind_bundle()
        valid = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        provenance = source_contract_provenance(valid)
        candidate.write_text(candidate.read_text(encoding="utf-8") + "\n", encoding="utf-8")
        ok, reason = stored_provenance_matches_current(
            project_path=self.project, target=self.target, provenance=provenance,
        )
        self.assertFalse(ok)
        self.assertIn("blind_candidate_sha256 changed", reason)

    def test_numeric_contract_preserves_exact_nonterminating_rational(self):
        candidate = {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "phase": "solve",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "id": "icho_t4_a8",
            "blind_record_sha256": "e" * 64,
            "result_kind": "numeric",
            "raw_result": {
                "expression": "raw thermodynamic quotient",
                "lean_expression": "IchoT4A8.rawEnergy",
                "derivation_spec": "IchoT4A8.rawEnergyDerivedFromProblemData",
                "certified_interval": {
                    "lower": "4357297213499999999/619393",
                    "upper": "4357297213500000001/619393",
                },
                "value": "4357297213500000000/619393",
                "unit": "J mol^-1",
            },
            "reported_result": {
                "value": "7.03e12",
                "text": "7.03e12 J mol^-1",
                "unit": "J mol^-1",
                "precision": REPORTING_POLICY["final_precision"],
                "rounding_rule": REPORTING_POLICY["tie_rule"],
            },
            "reporting_rule_source": REPORTING_POLICY,
            "tolerance_provenance": {
                "measurement_policy": MEASUREMENT_POLICY,
                "derivation": "fixed final reporting quantum",
            },
            "candidate_domain_provenance": {
                "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
                "derivation": {"kind": "derived_theorem", "evidence": "quotient bounds"},
            },
            "lean_declarations": [
                "IchoT4A8.rawEnergy_exact",
                "IchoT4A8.reportedEnergy",
            ],
        }
        types = expected_numeric_result_types(candidate)
        self.assertIsNotNone(types)
        assert types is not None
        self.assertIn("IchoT4A8.rawEnergyDerivedFromProblemData", types["raw_result"])
        self.assertIn("4357297213499999999 : ℝ", types["raw_result"])
        self.assertIn("4357297213500000001 : ℝ", types["raw_result"])
        self.assertIn("/ 619393", types["raw_result"])
        self.assertIn("(10000000000 : ℝ)", types["reported_result"])
        candidate["lean_result_contracts"] = [
            {
                "role": role,
                "declaration": declaration,
                "expected_type": types[role],
                "expected_type_sha256": lean_result_type_sha256(types[role]),
                "result_payload_sha256": blind_result_payload_sha256(candidate, role),
            }
            for role, declaration in zip(
                ("raw_result", "reported_result"),
                candidate["lean_declarations"],
                strict=True,
            )
        ]
        self.assertEqual(validate_blind_result_contracts(candidate), [])

        candidate["raw_result"]["value"] = "8714594427000000000/1238786"
        self.assertIn(
            "raw_result.value",
            "; ".join(validate_blind_result_contracts(candidate)),
        )

    def test_arbitrary_candidate_bound_only_to_true_is_rejected(self):
        candidate = _classification_candidate()
        candidate["raw_result"]["lean_expression"] = "True"
        candidate["reported_result"]["lean_expression"] = "True"
        for contract in candidate["lean_result_contracts"]:
            contract["expected_type"] = "True"
            contract["expected_type_sha256"] = lean_result_type_sha256("True")
            contract["result_payload_sha256"] = blind_result_payload_sha256(
                candidate, contract["role"]
            )
        errors = "; ".join(validate_blind_result_contracts(candidate))
        self.assertIn("safe fully-qualified Prop names", errors)

    def test_blind_source_paths_cannot_escape_or_traverse_symlinks(self):
        self._write_blind_bundle()
        outside = self.project.parent / "sealed-solution.json"
        outside.write_text('{"secret":"must not read"}', encoding="utf-8")
        self.chapter.write_text(
            "% archon:source-report ../../sealed-solution.json\n",
            encoding="utf-8",
        )
        escaped = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(escaped["valid"])
        self.assertIn("source report path is unsafe", "; ".join(escaped["errors"]))

        self._write_blind_bundle()
        link = self.project / "images" / "linked-secret.png"
        link.symlink_to(outside)
        loaded = json.loads(self.report.read_text(encoding="utf-8"))
        loaded["entry"]["image_paths"] = ["images/linked-secret.png"]
        self.report.write_text(json.dumps(loaded), encoding="utf-8")
        linked = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(linked["valid"])
        self.assertIn("source image path 1 is unsafe", "; ".join(linked["errors"]))

    def test_blind_report_and_certificate_forbidden_fields_fail_closed(self):
        self._write_blind_bundle()
        loaded = json.loads(self.report.read_text())
        loaded["entry"]["nested"] = {"marking_scheme": "secret"}
        self.report.write_text(json.dumps(loaded), encoding="utf-8")
        poisoned = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(poisoned["valid"])
        self.assertIn("forbidden field", "; ".join(poisoned["errors"]))

        self._write_blind_bundle(question_field="current_question")
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        audit = self._blind_source_audit(contract)
        self.assertEqual(
            validate_review_source_certificate(audit, contract, passing=True), "",
        )
        audit["official_answer_alignment"] = {
            "status": "aligned", "evidence": "looked at the key",
        }
        self.assertIn(
            "forbidden field",
            validate_review_source_certificate(audit, contract, passing=True),
        )
        for key in ("officialAnswer", "workedSolutions", "graderPayload"):
            with self.subTest(key=key):
                poisoned_audit = self._blind_source_audit(contract)
                poisoned_audit["nested"] = {key: "secret"}
                self.assertIn(
                    "forbidden field",
                    validate_review_source_certificate(
                        poisoned_audit, contract, passing=True
                    ),
                )
        nested_seen = self._blind_source_audit(contract)
        nested_seen["nested"] = {"officialAnswerSeen": True}
        self.assertIn(
            "forbidden field",
            validate_review_source_certificate(nested_seen, contract, passing=True),
        )

    def test_blind_audit_requires_all_six_passing_evidenced_checks(self):
        self._write_blind_bundle()
        contract = build_review_source_contract(
            project_path=self.project, target=self.target,
        )
        for name in (
            "answer_independence",
            "raw_derivation",
            "reporting_rule_source",
            "tolerance_provenance",
            "candidate_domain_provenance",
            "lean_result_binding",
        ):
            with self.subTest(name=name):
                audit = self._blind_source_audit(contract)
                audit["blind_source_audit"][name]["status"] = "failed"
                self.assertIn(
                    "failed blind_source_audit",
                    validate_review_source_certificate(
                        audit, contract, passing=True,
                    ),
                )

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
