from __future__ import annotations

import hashlib
import json
import stat
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import Mock, patch

from archon.commands.chemistry_constant import (
    BASELINE_EMPIRICAL_RULE_IDS,
    CONTEST_INTERPRETATION_IDS,
    EMPIRICAL_RULE_IDS,
    REACTION_TEMPLATE_IDS,
)
from archon.agents.codex import CodexAgent

from archon.commands.loop.native_semantic_review import (
    build_independent_rederivation_example,
    build_native_semantic_review_contract,
)
from archon.commands.loop.review_preflight import check_review_target
from archon.commands.loop.formalization_review_gate import (
    apply_target_formalization_review,
    load_gate_state,
)
from archon.commands.loop.review_feedback import (
    build_feedback_event,
    build_repair_task,
)
from archon.commands.loop.parallel_formalization_review import (
    _run_formalization_review_worker,
    build_target_formalization_review_prompt,
    load_target_formalization_milestone,
    run_parallel_formalization_reviews,
)
from archon.commands.loop.parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewSpec,
    TargetReviewOutcome,
    _run_review_worker,
    build_target_review_prompt,
    load_pipelined_review_report,
    load_target_milestone,
    run_parallel_target_reviews,
    validate_parallel_review_session,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from archon.commands.tooling.project_config import HarnessDescriptor
from archon.commands.loop.prover.runners import (
    ParallelProverRunner,
    _native_formalizer_semantic_dag_block,
)
from archon.commands.loop.answer_submission import answer_submission_path
from archon.commands.loop.review_source_contract import (
    normalized_review_source_certificate,
)
from archon.commands.loop.problem_only_review_contract import (
    NATIVE_CONTRACT_KIND,
    ProblemOnlyReviewContractError,
    _validate_native_composition_accounting,
    materialize_controller_review_provenance,
    native_problem_image_args,
    native_source_contract_provenance,
    render_native_chemistry_constant_policy,
    render_native_composition_accounting_prompt,
    render_native_formalizer_answer_submission_prompt,
    resolve_native_formalizer_source_contract,
    resolve_target_review_source_contract,
    validate_native_review_source_certificate,
    validate_review_source_contract_current,
)


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _json_bytes(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


class ProblemOnlyReviewContractTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.project = Path(self.tempdir.name)
        self.state = self.project / ".archon"
        self.iter_dir = self.state / "logs" / "iter-001"
        self.output_root = self.iter_dir / "review"
        self.target = (
            self.project / "IChO2026Problems" / "problem_item_a.lean"
        )
        self.rel = "IChO2026Problems/problem_item_a.lean"
        self.lean_source = "theorem item_a : True := by trivial\n"
        self.image_rel = "icho_2026_source/image/page.png"
        self.bundle_rel = "icho_2026_source/questions_only.jsonl"
        self.report_rel = "reports/icho/problem_item_a.source.json"
        self.image_bytes = b"student-visible page; printed fallback -750"
        self.row = {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": "item_a",
            "index": "item_a",
            "problem_id": "item",
            "part_id": "A",
            "question": (
                "Derive the upstream value from the givens. A later subpart "
                "prints fallback -750 for use only in that later subpart."
            ),
            "current_question": "Derive the upstream requested value.",
            "previous_parts": [],
            "requested_outputs": [{
                "id": "value",
                "kind": "integer",
                "source_requirement": "the independently derived value",
                "reporting_policy": {"kind": "exact_integer"},
                "unit": "",
            }],
            "problem_assets": [{
                "kind": "problem_page",
                "path": "page.png",
                "sha256": _sha256(self.image_bytes),
            }],
            "candidate_domain_policy": {
                "allowed_sources": [
                    "problem_text",
                    "problem_image",
                    "problem_stated_fallback",
                    "derived_theorem",
                ],
                "unjustified_search_bounds": "forbidden",
            },
            "measurement_policy": {
                "derived_tolerances": "prove_from_problem_intervals",
            },
            "reporting_policy": {
                "intermediate_rounding": "forbidden",
                "final_precision": {"kind": "per_requested_output"},
            },
        }
        self.preflight = {
            "file": self.rel,
            "status": "passed",
            "compiles": True,
            "returncode": 0,
            "sorry_count": 0,
            "duration_secs": 0.01,
            "diagnostics": "",
            "numeric_reporting": {
                "active": True,
                "status": "not_applicable",
                "reason": "target has no numeric requested outputs",
                "numeric_outputs": 0,
                "lean_source_sha256": _sha256(self.lean_source.encode()),
                "bundle_sha256": _sha256(_json_bytes(self.row)),
                "certificates": [],
            },
        }
        self._materialize_workspace()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def _materialize_workspace(self) -> None:
        self.iter_dir.mkdir(parents=True, exist_ok=True)
        self.target.parent.mkdir(parents=True, exist_ok=True)
        self.target.write_text(self.lean_source, encoding="utf-8")
        image = self.project / self.image_rel
        image.parent.mkdir(parents=True, exist_ok=True)
        image.write_bytes(self.image_bytes)

        bundle_payload = _json_bytes(self.row)
        bundle = self.project / self.bundle_rel
        bundle.parent.mkdir(parents=True, exist_ok=True)
        bundle.write_bytes(bundle_payload)
        record_sha256 = _sha256(_json_bytes(self.row))

        entry = dict(self.row)
        entry.update({
            "blind_record_sha256": record_sha256,
            "image_paths": [self.image_rel],
            "image_path": self.image_rel,
        })
        report = {
            "schema_version": 3,
            "command": "physics-formalize",
            "domain": "chemistry",
            "evaluation_mode": "answer_blind",
            "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
            "next_stage": "autoformalize",
            "official_answer_seen": False,
            "phase": "solve",
            "status": "prepared",
            "path_base": "project",
            "project_path": ".",
            "proof_mode": "chemistry",
            "prover_mode": "chemistry-formalize",
            "output_lean": self.rel,
            "source_report": self.report_rel,
            "entry": entry,
            "problem_id": self.row["problem_id"],
            "part_id": self.row["part_id"],
            "previous_parts": self.row["previous_parts"],
            "blind_record_sha256": record_sha256,
        }
        report_path = self.project / self.report_rel
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(report, ensure_ascii=False),
            encoding="utf-8",
        )

        manifest = {
            "schema_version": 1,
            "protocol": "icho-problem-only-solver-seed-v1",
            "blind_bundle": {
                "path": self.bundle_rel,
                "row_count": 1,
                "sha256": _sha256(bundle_payload),
                "size": len(bundle_payload),
            },
            "blind_bundle_sha256": _sha256(bundle_payload),
            "target_ids": [self.row["id"]],
            "assets": {self.image_rel: _sha256(self.image_bytes)},
        }
        (self.project / "isolation_manifest.json").write_text(
            json.dumps(manifest),
            encoding="utf-8",
        )

        self.state.mkdir(parents=True, exist_ok=True)
        config = {
            "answer_blind": {
                "protocol": "icho-answer-blind-v1",
                "phase": "solve",
                "authority": "problem-only",
                "official_answer_seen": False,
                "isolation": {
                    "filesystem_answer_blind": True,
                    "network_answer_blind": False,
                },
            },
            "loop": {"domain_profile": {"name": "chemistry-native"}},
        }
        (self.state / "config.json").write_text(
            json.dumps(config),
            encoding="utf-8",
        )
        raw_values = {
            "integer": "7",
            "numeric": "7/2",
            "formula": "H2O",
            "classification": "class-A",
            "finite_set": "{A, B}",
        }
        outputs = []
        for output in self.row["requested_outputs"]:
            raw_value = raw_values.get(output["kind"], "derived-value")
            outputs.append({
                "id": output["id"],
                "kind": output["kind"],
                "raw_value": raw_value,
                "display_value": str(raw_value),
                "unit": output["unit"],
            })
        answer = {
            "schema_version": 1,
            "id": self.row["id"],
            "official_answer_seen": False,
            "outputs": outputs,
        }
        answer_path = answer_submission_path(self.project, self.row["id"])
        answer_path.parent.mkdir(parents=True, exist_ok=True)
        answer_path.write_text(json.dumps(answer), encoding="utf-8")
        reporting = self.preflight["numeric_reporting"]
        if "lean_source_sha256" in reporting:
            reporting["lean_source_sha256"] = _sha256(self.target.read_bytes())
            reporting["bundle_sha256"] = _sha256(bundle_payload)

    def _contract(self) -> dict:
        return resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight=self.preflight,
        )

    def test_native_problem_images_are_verified_before_candidate_exists(self) -> None:
        codex = HarnessDescriptor(name="codex", runner="codex")
        self.target.unlink()
        self.assertEqual(
            native_problem_image_args(
                project_path=self.project,
                target=self.target,
                harness=codex,
            ),
            ["--image", str((self.project / self.image_rel).resolve()), "--"],
        )
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "Codex --image capable",
        ):
            native_problem_image_args(
                project_path=self.project,
                target=self.target,
                harness=HarnessDescriptor(
                    name="claude", runner="claude-code",
                ),
            )
        (self.project / self.image_rel).write_bytes(b"drift")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "does not match|stale or duplicated",
        ):
            native_problem_image_args(
                project_path=self.project,
                target=self.target,
                harness=codex,
            )

    def test_native_image_args_keep_codex_prompt_positional(self) -> None:
        harness = HarnessDescriptor(name="codex", runner="codex")
        extra_args = native_problem_image_args(
            project_path=self.project,
            target=self.target,
            harness=harness,
        )
        prompt = "PROMPT_SENTINEL"
        argv = CodexAgent(descriptor=harness, role="prover").build_argv(
            prompt,
            extra_args=extra_args,
            env_source={},
            lake_root=str(self.project),
        )
        self.assertEqual(argv[-4:], [
            "--image", str((self.project / self.image_rel).resolve()),
            "--", prompt,
        ])

    def _source_audit(self, contract: dict) -> dict:
        passed = {"status": "passed", "evidence": "bound evidence checked"}
        return {
            "source_contract": native_source_contract_provenance(contract),
            "blind_source_audit": {
                name: dict(passed)
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
                name: dict(passed)
                for name in (
                    "statement_scope",
                    "hypothesis_derivability",
                    "conclusion_alignment",
                    "bridge_completeness",
                )
            },
            "requested_outputs": [
                {
                    "output_id": output["id"],
                    "source_requirement": output["source_requirement"],
                    "submission_status": "matched",
                    "reporting_policy_status": "matched",
                    "lean_carrier": f"item_a_{output['id']}",
                    "status": "covered",
                    "evidence": "submission, reporting rule, and carrier agree",
                }
                for output in contract["problem_evidence"]["requested_outputs"]
            ],
            "blueprint_conflicts": [],
            "image_audit": [{
                "path": image["path"],
                "sha256": image["sha256"],
                "inspected": True,
                "evidence": "the bound student-visible page was inspected",
            } for image in contract["images"]],
            "chemistry_checks": {
                name: dict(passed)
                for name in (
                    "chemical_semantics",
                    "formula_mass_consistency",
                    "conservation_laws",
                    "units_dimensions",
                    "numerical_reporting",
                    "structure_stereochemistry",
                    "identification_uniqueness",
                    "answer_smuggling",
                )
            },
        }

    def _proof_milestone(self, contract: dict) -> dict:
        return {
            "timestamp": "2026-08-16T00:00:00Z",
            "target": {"file": self.rel, "theorem": "item_a"},
            "status": "solved",
            "proof_review": {
                "schema_version": 1,
                "route": "solved",
                "reason": "bound source and proof passed",
                "evidence": "candidate and preflight hashes checked",
                "redraft_kind": "not_applicable",
                "infrastructure_request": None,
                **self._source_audit(contract),
            },
            "attempts": [],
            "findings": {
                "blocker": "",
                "verification": "bounded review",
                "key_lemmas_used": [],
            },
            "session": {"id": "session_1", "model": "test"},
            "next_steps": "",
        }

    def _formalization_milestone(self, contract: dict) -> dict:
        semantic_contract = build_native_semantic_review_contract(
            project_path=self.project,
            target=self.target,
        )
        assert isinstance(semantic_contract, dict)
        assert semantic_contract.get("valid")
        passed = {"status": "passed", "evidence": "bound evidence checked"}
        return {
            "timestamp": "2026-08-16T00:00:00Z",
            "target": {"file": self.rel, "theorem": "item_a"},
            "status": "solved",
            "formalization_review": {
                "schema_version": 2,
                "status": "passed",
                "reason": "bound source and statement passed",
                "checks": {
                    name: dict(passed)
                    for name in (
                        "source_faithfulness",
                        "derivability",
                        "abstraction_sufficiency",
                        "countermodel_resistance",
                    )
                } | {
                    "uncertainty_propagation": {
                        "status": "not_applicable",
                        "evidence": "no uncertainty requested",
                    },
                    "branch_orientation": {
                        "status": "not_applicable",
                        "evidence": "no branch requested",
                    },
                },
                "bridge_obligations": [{
                    "claim": "problem relation",
                    "carrier": "item_a",
                    "status": "covered",
                    "evidence": "the declaration carries the relation",
                }],
                "independent_rederivation": (
                    build_independent_rederivation_example(semantic_contract)
                ),
                **self._source_audit(contract),
            },
            "attempts": [],
            "findings": {
                "blocker": "",
                "verification": "bounded review",
                "key_lemmas_used": [],
            },
            "session": {"id": "session_1", "model": "test"},
            "next_steps": "",
        }

    def _failed_formalization_milestone(self, contract: dict) -> dict:
        row = self._formalization_milestone(contract)
        row["status"] = "blocked"
        review = row["formalization_review"]
        review["status"] = "failed"
        review["reason"] = "PANEL_SWAP_SOURCE_DIAGNOSIS"
        review["checks"]["source_faithfulness"] = {
            "status": "failed",
            "evidence": "panel B3 was substituted for source panel A2",
        }
        review["bridge_obligations"][0] = {
            "claim": "source panel B3 plus source panel A2",
            "carrier": "item_a_wrong_panel_ledger",
            "status": "blocked",
            "evidence": "the current carrier swaps the two source panels",
        }
        return row

    def test_contract_binds_problem_candidate_answer_and_constant_dataset(self) -> None:
        contract = self._contract()
        self.assertEqual(contract["contract_kind"], NATIVE_CONTRACT_KIND)
        self.assertEqual(contract["authority"], "problem-only")
        self.assertEqual(contract["evaluation_mode"], "answer_blind")
        self.assertEqual(contract["candidate"], self.rel)
        self.assertEqual(
            contract["candidate_sha256"], _sha256(self.target.read_bytes()),
        )
        self.assertEqual(len(contract["preflight_sha256"]), 64)
        self.assertEqual(contract["images"][0]["path"], self.image_rel)
        answer_path = answer_submission_path(self.project, self.row["id"])
        self.assertEqual(
            contract["answer_submission"],
            answer_path.relative_to(self.project).as_posix(),
        )
        self.assertEqual(
            contract["answer_submission_sha256"], _sha256(answer_path.read_bytes()),
        )
        self.assertEqual(len(contract["chemistry_constant_dataset"]["sha256"]), 64)
        for forbidden in (
            "blueprint",
            "trace",
            "task_results",
            "prior_gate",
            "blind_candidate_record",
        ):
            self.assertNotIn(forbidden, contract)

    def test_chemistry_registry_policy_bounds_contest_interpretation(self) -> None:
        prompt = " ".join(
            render_native_chemistry_constant_policy(self._contract()).split()
        )
        for marker in (
            "contest_interpretation <POLICY_ID>",
            "contest-semantics policy, not a paper",
            "exact problem-text locator",
            "no problem-stated override",
            "Missing, ambiguous, or different-substrate cues fail closed",
            "does not identify the specific reagent",
            "derive that identity from source measurements",
            "exact TEMPLATE_ID allowlist",
            "binary_two_fragment_electrophilic_addition",
            "exact POLICY_ID allowlist",
            "analogous_halogen_addition",
            "full supported registries",
            "no other identifier may be probed",
            "empirical_rule <RULE_ID>",
            f"exact {len(BASELINE_EMPIRICAL_RULE_IDS)}-ID allowlist",
            "Reference-only empirical-rule IDs",
            "never baseline evidence",
            "cannot receive a controller activation receipt",
            "Never borrow a missing protocol condition",
            "if even one lacks exact evidence",
            "Receipt completeness never establishes applicability",
            "Dormant Reviewer-requestable bridge IDs",
            "ordinary lookup",
            "complete controller-built activation receipt",
            "Never guess, enumerate, or probe",
            "unlisted id fails closed",
            "`authority_kind`",
            "peer_reviewed_literature",
            "contest_semantics_policy",
            "bounded policy—not a paper or universal empirical law",
            "complete source-supplied finite candidate set",
            "automatic_problem_instantiation",
            "bounded policy into an open-world rule",
            "base_dataset_sha256",
            "pinned_rule_record_sha256",
            "empirical_registry_manifest_sha256",
            "source.content_sha256",
            "approved review metadata",
        ):
            self.assertIn(marker, prompt)
        for rule_id in EMPIRICAL_RULE_IDS:
            self.assertEqual(prompt.count(rule_id), 1)
        for template_id in REACTION_TEMPLATE_IDS:
            self.assertEqual(prompt.count(template_id), 1)
        for policy_id in CONTEST_INTERPRETATION_IDS:
            self.assertEqual(prompt.count(policy_id), 1)
        self.assertNotIn("symmetry_guided_benzylic_oxidation", prompt)
        self.assertNotIn("benzylic_oxidation_permanganate", prompt)


    def test_review_preflight_producer_flows_into_native_contract(self) -> None:
        process = Mock()
        process.returncode = 0
        process.communicate.return_value = ("", "")
        with patch(
            "archon.commands.loop.review_preflight.subprocess.Popen",
            return_value=process,
        ):
            preflight = check_review_target(
                project_path=self.project,
                target=self.target,
                timeout_sec=30,
            )

        self.assertEqual(
            set(preflight),
            {
                "file",
                "status",
                "compiles",
                "returncode",
                "sorry_count",
                "duration_secs",
                "diagnostics",
                "numeric_reporting",
            },
        )
        self.assertEqual(
            preflight["numeric_reporting"]["status"],
            "not_applicable",
        )
        contract = resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight=preflight,
        )
        self.assertEqual(contract["preflight"], preflight)

    def test_initial_formalizer_contract_needs_no_answer_or_candidate(self) -> None:
        answer_submission_path(self.project, self.row["id"]).unlink()
        self.target.unlink()
        contract = resolve_native_formalizer_source_contract(
            project_path=self.project,
            target=self.target,
        )
        prompt = render_native_formalizer_answer_submission_prompt(contract)
        self.assertIn(
            ".archon/task_results/IChO2026Problems_problem_item_a.answer.json",
            prompt,
        )
        self.assertIn('"id": "value"', prompt)
        self.assertIn('"display_value": "<replace with final displayed string>"', prompt)
        self.assertIn("perform a source-first visual recount", prompt)
        self.assertIn("every relevant panel and legend separately", prompt)
        self.assertIn("enumerate all distinct building-block types", prompt)
        self.assertIn("balance every condensation/addition loss or gain", prompt)
        self.assertIn("state the numerator and denominator", prompt)
        self.assertIn("component mass divided by total mixture mass", prompt)
        self.assertIn("solve that mass-balance equation before substitution", prompt)
        self.target.write_text(self.lean_source, encoding="utf-8")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "answer submission",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=self.preflight,
            )

    def test_answer_submission_change_invalidates_review_contract(self) -> None:
        contract = self._contract()
        path = answer_submission_path(self.project, self.row["id"])
        answer = json.loads(path.read_text(encoding="utf-8"))
        answer["outputs"][0]["display_value"] = "8"
        path.write_text(json.dumps(answer), encoding="utf-8")
        self.assertIn(
            "changed after contract creation",
            validate_review_source_contract_current(
                project_path=self.project,
                contract=contract,
            ),
        )
        self.assertNotEqual(
            contract["answer_submission_sha256"],
            self._contract()["answer_submission_sha256"],
        )

    def test_review_contract_rejects_non_string_display_value(self) -> None:
        path = answer_submission_path(self.project, self.row["id"])
        answer = json.loads(path.read_text(encoding="utf-8"))
        answer["outputs"][0]["display_value"] = 7
        path.write_text(json.dumps(answer), encoding="utf-8")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "display_value.*JSON string",
        ):
            self._contract()

    def test_native_prompts_do_not_read_or_render_legacy_artifacts(self) -> None:
        self.preflight["diagnostics"] = "RAW_PREFLIGHT_DIAGNOSTIC_SECRET"
        contract = self._contract()
        slug = "IChO2026Problems_problem_item_a"
        artifacts = (
            self.project / "blueprint" / "src" / "chapters" / f"{slug}.tex",
            self.iter_dir / "provers" / f"{slug}.jsonl",
            self.iter_dir / "formalizers" / f"{slug}.jsonl",
            self.state / "task_results" / "problem_item_a.lean.md",
        )
        for index, artifact in enumerate(artifacts):
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_text(
                f"LEGACY_ARTIFACT_SECRET_{index}",
                encoding="utf-8",
            )
        prior = {
            "status": "retry",
            "attempts": 1,
            "reason": "RAW_TOP_LEVEL_REASON_SECRET",
            "evidence": "RAW_TOP_LEVEL_EVIDENCE_SECRET",
            "history": [{
                "event_id": "proof-event-1",
                "iter": 1,
                "route": "retry_proof",
                "resulting_status": "retry",
                "attempt": 1,
                "reason": "RAW_PROOF_REASON_SECRET",
                "evidence": "RAW_PROOF_EVIDENCE_SECRET",
                "redraft_kind": "not_applicable",
                "result_spec": {
                    "kind": "integer",
                    "status": "derived",
                    "value": "RESULT_SPEC_SECRET",
                },
            }],
            "review_events": [{
                "event_id": "formalization-event-1",
                "iter": 1,
                "decision": "failed",
                "resulting_status": "retry",
                "attempt": 1,
                "reason": "RAW_FORMALIZATION_REASON_SECRET",
                "certificate": {
                    "result_spec": {"value": "FORMAL_RESULT_SPEC_SECRET"},
                },
            }],
            "certificate": {
                "result_spec": {"value": "TOP_LEVEL_RESULT_SPEC_SECRET"},
            },
        }

        with patch(
            "archon.commands.loop.parallel_review.load_domain_profile",
            side_effect=AssertionError("native prompt touched legacy profile"),
        ):
            proof_prompt = build_target_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.iter_dir,
                iter_num=1,
                target=self.target,
                output_dir=self.output_root / "proof",
                preflight=self.preflight,
                prior_gate_record=prior,
                source_contract=contract,
            )
        with (
            patch(
                "archon.commands.loop.parallel_formalization_review."
                "_result_evidence",
                side_effect=AssertionError("native prompt read task results"),
            ),
            patch(
                "archon.commands.loop.parallel_formalization_review."
                "load_domain_profile",
                side_effect=AssertionError("native prompt touched legacy profile"),
            ),
        ):
            formal_prompt = build_target_formalization_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.iter_dir,
                iter_num=1,
                target=self.target,
                output_dir=self.output_root / "formalization",
                preflight=self.preflight,
                prior_gate_record=prior,
                source_contract=contract,
            )
        self.assertIn(
            "needs_redraft -> blocked (never partial)", proof_prompt,
        )
        self.assertIn('"route": "retry_proof"', proof_prompt)
        self.assertIn('"decision": "failed"', formal_prompt)
        self.assertIn(
            "independently\nstate the numerator and denominator",
            formal_prompt,
        )
        self.assertIn(
            "component mass divided by total mixture mass",
            formal_prompt,
        )
        self.assertIn(
            "valid only when the problem explicitly defines the\n"
            "fraction relative to that base mass",
            formal_prompt,
        )
        self.assertNotIn("proof-event-1", proof_prompt)
        self.assertNotIn("formalization-event-1", formal_prompt)
        for marker in (
            "source-first visual topology pass",
            "For every relevant panel separately",
            "legend encoding",
            "enumerate every distinct building-block",
            "node count, connectivity/degree",
            "construct an atom ledger",
            "condensation/addition loss or gain",
            "before comparing it with the submission or Lean carrier",
            "candidate's formula or prose is never a substitute",
            "fail closed instead of copying",
            "source-first arrow certificate",
            "state the arrowhead\ndirection",
            "enumerate all precursors at the tail",
            "identify the product at the head",
            "trace a\ndistinctive scaffold or motif",
            "Cross-check\nthat scaffold against every adjacent product",
            "expand every chemical abbreviation",
            "terminal or capping group",
            "complete elemental formula",
            "Mark its\nattachment boundary",
            "count\nevery atom exactly once",
        ):
            self.assertIn(marker, formal_prompt)

        for prompt in (proof_prompt, formal_prompt):
            self.assertIn("NATIVE PROBLEM-INPUT-ONLY CONTRACT", prompt)
            self.assertIn("candidate_sha256", prompt)
            self.assertIn(
                '"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>',
                prompt,
            )
            self.assertIn("illustrative, not an allowlist", prompt)
            self.assertIn("Reviewer must verify each used lookup", prompt)
            self.assertIn("exact TEMPLATE_ID allowlist", prompt)
            self.assertIn("binary_two_fragment_electrophilic_addition", prompt)
            self.assertIn("exact POLICY_ID allowlist", prompt)
            self.assertIn("analogous_halogen_addition", prompt)
            self.assertIn("empirical_rule <RULE_ID>", prompt)
            self.assertIn(
                f"exact {len(BASELINE_EMPIRICAL_RULE_IDS)}-ID allowlist",
                prompt,
            )
            self.assertIn("Reference-only empirical-rule IDs", prompt)
            self.assertIn(
                "cannot receive a controller activation receipt", prompt
            )
            self.assertIn(
                "Never borrow a missing protocol condition", prompt
            )
            self.assertIn("if even one lacks exact evidence", prompt)
            self.assertIn(
                "Receipt completeness never establishes applicability",
                " ".join(prompt.split()),
            )
            self.assertIn("source.content_sha256", prompt)
            self.assertIn("bounded policy", prompt)
            self.assertIn("a paper or universal empirical law", prompt)
            for rule_id in EMPIRICAL_RULE_IDS:
                self.assertEqual(prompt.count(rule_id), 1)
            self.assertIn("Problem-stipulated values override", prompt)
            self.assertIn("source uncertainty could change", prompt)
            for template_id in REACTION_TEMPLATE_IDS:
                self.assertEqual(prompt.count(template_id), 1)
            for policy_id in CONTEST_INTERPRETATION_IDS:
                self.assertEqual(prompt.count(policy_id), 1)
            self.assertNotIn("symmetry_guided_benzylic_oxidation", prompt)
            self.assertNotIn("benzylic_oxidation_permanganate", prompt)
            self.assertNotIn("`archon chemistry-constant", prompt)
            self.assertNotIn("preflight_sha256", prompt)
            self.assertIn("printed fallback", prompt)
            self.assertIn("never use a later fallback backward", prompt)
            for secret in (
                "RAW_TOP_LEVEL_REASON_SECRET",
                "RAW_TOP_LEVEL_EVIDENCE_SECRET",
                "RAW_PROOF_REASON_SECRET",
                "RAW_PROOF_EVIDENCE_SECRET",
                "RAW_FORMALIZATION_REASON_SECRET",
                "RESULT_SPEC_SECRET",
                "FORMAL_RESULT_SPEC_SECRET",
                "TOP_LEVEL_RESULT_SPEC_SECRET",
                "RAW_PREFLIGHT_DIAGNOSTIC_SECRET",
            ):
                self.assertNotIn(secret, prompt)
            self.assertNotIn('"result_spec":', prompt)
            self.assertNotIn(str(self.project / self.report_rel), prompt)
            self.assertNotIn("Bound problem-side source report", prompt)
            for artifact in artifacts:
                self.assertNotIn(str(artifact), prompt)
            for marker in (
                "LEGACY_ARTIFACT_SECRET",
                "OFFICIAL SOURCE CONTRACT",
                "official_answer_alignment",
                "entry.answer (official rubric)",
                "Blind solve candidate record",
                "blind_candidates",
                "frozen before any later reveal",
            ):
                self.assertNotIn(marker, prompt)

    def test_native_certificate_binds_exact_provenance(self) -> None:
        contract = self._contract()
        audit = self._source_audit(contract)
        self.assertEqual(
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
            "",
        )
        audit["source_contract"]["candidate_sha256"] = "0" * 64
        self.assertIn(
            "does not match native problem-only evidence",
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
        )
        truncated_audit = json.loads(json.dumps(self._source_audit(contract)))
        source_sha = truncated_audit["source_contract"][
            "source_record_sha256"
        ]
        truncated_audit["source_contract"]["source_record_sha256"] = (
            source_sha[:-4]
        )
        truncated_error = validate_native_review_source_certificate(
            truncated_audit, contract, passing=True,
        )
        self.assertIn("source_record_sha256", truncated_error)
        self.assertIn("length 60, expected 64", truncated_error)
        semantic_audit = json.loads(json.dumps(self._source_audit(contract)))
        semantic_audit["source_contract"]["semantic_dag"]["sha256"] = (
            "f" * 64
        )
        self.assertIn(
            "does not match native problem-only evidence",
            validate_native_review_source_certificate(
                semantic_audit, contract, passing=True,
            ),
        )

    def test_redraft_diagnosis_requires_exact_source_and_output_binding(
        self,
    ) -> None:
        contract = self._contract()
        milestone = self._failed_formalization_milestone(contract)
        certificate = milestone["formalization_review"]
        digest = contract["candidate_sha256"]
        self.assertEqual(
            validate_native_review_source_certificate(
                certificate, contract, passing=False,
            ),
            "",
        )

        def repair_task(review: dict) -> dict:
            event = build_feedback_event(
                review_kind="formalization",
                candidate_sha256=digest,
                event_id="native-formalization-failed",
                iteration=1,
                attempt=1,
                resulting_status="retry",
                certificate=review,
                decision="failed",
                preflight=self.preflight,
            )
            return build_repair_task(
                {
                    "status": "retry",
                    "candidate_sha256": digest,
                    "certificate": review,
                    "repair_events": [event],
                },
                review_kind="formalization",
                worker_stage="formalization",
                candidate_sha256=digest,
                preflight=self.preflight,
                expected_source_contract=contract,
            )

        valid_task = repair_task(certificate)
        source_review = valid_task["source_bound_review"]
        self.assertEqual(
            source_review["reason"], "PANEL_SWAP_SOURCE_DIAGNOSIS"
        )
        self.assertEqual(
            source_review["repair_actions"][0]["source_claim"],
            "source panel B3 plus source panel A2",
        )
        valid_payload = json.dumps(valid_task, ensure_ascii=False)
        for forbidden in (
            "raw_value",
            "display_value",
            "source_requirement",
            "the independently derived value",
        ):
            self.assertNotIn(forbidden, valid_payload)

        wrong_hash = json.loads(json.dumps(certificate))
        original_hash = wrong_hash["source_contract"][
            "source_record_sha256"
        ]
        wrong_hash["source_contract"]["source_record_sha256"] = (
            "0" * 64 if original_hash != "0" * 64 else "1" * 64
        )
        self.assertIn(
            "does not match native problem-only evidence",
            validate_native_review_source_certificate(
                wrong_hash, contract, passing=False,
            ),
        )
        wrong_hash_task = repair_task(wrong_hash)
        self.assertNotIn("source_bound_review", wrong_hash_task)
        self.assertNotIn(
            "PANEL_SWAP_SOURCE_DIAGNOSIS",
            json.dumps(wrong_hash_task, ensure_ascii=False),
        )

        wrong_output = json.loads(json.dumps(certificate))
        wrong_output["requested_outputs"][0]["output_id"] = (
            "unbound-output"
        )
        self.assertIn(
            "output_id is not bound problem evidence",
            validate_native_review_source_certificate(
                wrong_output, contract, passing=False,
            ),
        )
        wrong_output_task = repair_task(wrong_output)
        self.assertNotIn("source_bound_review", wrong_output_task)
        self.assertNotIn(
            "PANEL_SWAP_SOURCE_DIAGNOSIS",
            json.dumps(wrong_output_task, ensure_ascii=False),
        )

    def test_gate_audits_bad_contract_without_forwarding_diagnosis(self) -> None:
        contract = self._contract()
        milestone = self._failed_formalization_milestone(contract)
        certificate = milestone["formalization_review"]
        original_hash = certificate["source_contract"][
            "source_record_sha256"
        ]
        bad_hash = "0" * 64 if original_hash != "0" * 64 else "1" * 64
        certificate["source_contract"]["source_record_sha256"] = bad_hash

        update = apply_target_formalization_review(
            state_dir=self.state,
            project_path=self.project,
            target=self.target,
            milestone=milestone,
            iter_num=1,
            max_iterations=2,
            event_id="native:formalization:bad-source-contract",
            expected_source_contract=contract,
            preflight=self.preflight,
        )
        self.assertEqual(update.status, "retry")
        record = load_gate_state(self.state)["targets"][self.rel]
        self.assertEqual(
            record["certificate"]["source_contract"]["source_record_sha256"],
            bad_hash,
        )
        self.assertEqual(
            record["certificate"]["reason"],
            "PANEL_SWAP_SOURCE_DIAGNOSIS",
        )
        handoff = record["repair_handoff"]
        self.assertNotIn("source_bound_review", handoff)
        handoff_payload = json.dumps(handoff, ensure_ascii=False)
        self.assertNotIn(bad_hash, handoff_payload)
        self.assertNotIn('"source_contract"', handoff_payload)
        self.assertNotIn(
            "PANEL_SWAP_SOURCE_DIAGNOSIS",
            handoff_payload,
        )

    def test_controller_materializes_only_provenance_and_preserves_metadata(
        self,
    ) -> None:
        contract = self._contract()
        expected = native_source_contract_provenance(contract)
        cases = (
            (
                "proof",
                self._proof_milestone,
                "proof_review",
                load_target_milestone,
            ),
            (
                "formalization",
                self._formalization_milestone,
                "formalization_review",
                load_target_formalization_milestone,
            ),
        )
        for name, make_row, review_field, loader in cases:
            with self.subTest(name=name):
                path = self.output_root / name / "milestones.jsonl"
                path.parent.mkdir(parents=True, exist_ok=True)
                row = make_row(contract)
                row[review_field]["source_contract"][
                    "source_record_sha256"
                ] = expected["source_record_sha256"][:-4]
                semantic_before = dict(row[review_field])
                semantic_before.pop("source_contract")
                path.write_text(json.dumps(row) + "\n", encoding="utf-8")
                path.chmod(0o640)
                before = path.stat()
                loaded, validation_error = loader(path, self.rel, contract)
                self.assertIsNone(loaded)
                self.assertIn("length 60, expected 64", validation_error)

                self.assertEqual(
                    materialize_controller_review_provenance(
                        path=path,
                        expected_rel=self.rel,
                        expected_contract=contract,
                        review_field=review_field,
                    ),
                    "",
                )
                after = path.stat()
                self.assertEqual(
                    stat.S_IMODE(after.st_mode),
                    stat.S_IMODE(before.st_mode),
                )
                self.assertEqual(after.st_uid, before.st_uid)
                self.assertEqual(after.st_gid, before.st_gid)
                fixed = json.loads(path.read_text(encoding="utf-8"))
                self.assertEqual(fixed[review_field]["source_contract"], expected)
                semantic_after = dict(fixed[review_field])
                semantic_after.pop("source_contract")
                self.assertEqual(semantic_after, semantic_before)
                loaded, validation_error = loader(path, self.rel, contract)
                self.assertIsNotNone(loaded)
                self.assertEqual(validation_error, "")

                stable_bytes = path.read_bytes()
                stable_inode = path.stat().st_ino
                self.assertEqual(
                    materialize_controller_review_provenance(
                        path=path,
                        expected_rel=self.rel,
                        expected_contract=contract,
                        review_field=review_field,
                    ),
                    "",
                )
                self.assertEqual(path.read_bytes(), stable_bytes)
                self.assertEqual(path.stat().st_ino, stable_inode)

    def test_controller_provenance_temp_and_symlink_fail_closed(self) -> None:
        contract = self._contract()
        expected = native_source_contract_provenance(contract)
        for kind in ("existing_file", "symlink"):
            with self.subTest(kind=kind):
                path = self.output_root / kind / "milestones.jsonl"
                path.parent.mkdir(parents=True, exist_ok=True)
                row = self._proof_milestone(contract)
                row["proof_review"]["source_contract"][
                    "source_record_sha256"
                ] = expected["source_record_sha256"][:-4]
                path.write_text(json.dumps(row) + "\n", encoding="utf-8")
                before = path.read_bytes()
                tmp = path.with_suffix(path.suffix + ".controller.tmp")
                if kind == "existing_file":
                    tmp.write_text("do not replace\n", encoding="utf-8")
                else:
                    tmp.symlink_to(path.parent / "absent")
                error = materialize_controller_review_provenance(
                    path=path,
                    expected_rel=self.rel,
                    expected_contract=contract,
                    review_field="proof_review",
                )
                self.assertIn("cannot persist", error)
                self.assertEqual(path.read_bytes(), before)
                self.assertTrue(tmp.exists() or tmp.is_symlink())

        real = self.output_root / "real-milestone.jsonl"
        real.write_text("{}\n", encoding="utf-8")
        linked = self.output_root / "linked-milestone.jsonl"
        linked.symlink_to(real)
        error = materialize_controller_review_provenance(
            path=linked,
            expected_rel=self.rel,
            expected_contract=contract,
            review_field="proof_review",
        )
        self.assertIn("regular file, not a symlink", error)
        self.assertEqual(real.read_text(encoding="utf-8"), "{}\n")

    def test_final_redraft_normalization_revalidates_source_certificate(self) -> None:
        contract = self._contract()
        row = self._proof_milestone(contract)
        row["status"] = "partial"
        row["proof_review"].update({
            "route": "needs_redraft",
            "reason": "the theorem is underdetermined",
            "evidence": "the source does not fix the required convention",
            "redraft_kind": "underdetermined_contract",
        })
        row["proof_review"]["source_contract"]["candidate_sha256"] = "0" * 64
        milestone_path = self.output_root / "final-redraft.jsonl"
        milestone_path.parent.mkdir(parents=True, exist_ok=True)
        milestone_path.write_text(
            json.dumps(row) + "\n",
            encoding="utf-8",
        )

        milestone, error = load_target_milestone(
            milestone_path,
            self.rel,
            contract,
            final_attempt=True,
        )

        self.assertIsNone(milestone)
        self.assertIn(
            "source_contract does not match native problem-only evidence",
            error,
        )

    def test_answer_bearing_keys_and_ambiguous_reports_fail_closed(self) -> None:
        self.row["nested"] = {"official_solution": "secret"}
        self._materialize_workspace()
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "answer-bearing field",
        ):
            self._contract()

        self.row.pop("nested")
        self._materialize_workspace()
        duplicate = (
            self.project / "reports" / "duplicate"
            / "problem_item_a.source.json"
        )
        duplicate.parent.mkdir(parents=True)
        duplicate.write_bytes((self.project / self.report_rel).read_bytes())
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "exactly one matching",
        ):
            self._contract()

    def test_native_config_and_preflight_fail_closed(self) -> None:
        config_path = self.state / "config.json"
        config = json.loads(config_path.read_text(encoding="utf-8"))
        config.pop("answer_blind")
        config_path.write_text(json.dumps(config), encoding="utf-8")
        calls = 0

        def worker(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            raise AssertionError("worker must not start")

        report = run_parallel_target_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
            preflight={"targets": [self.preflight]},
            prior_gate_targets={},
            requested_jobs=1,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertEqual(calls, 0)
        self.assertFalse(report["complete"])
        self.assertEqual(report["unresolved"], [self.rel])

        self._materialize_workspace()
        incomplete = dict(self.preflight)
        incomplete.pop("diagnostics")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "missing or ambiguous fields",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=incomplete,
            )

        incomplete = dict(self.preflight)
        incomplete.pop("numeric_reporting")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "missing or ambiguous fields",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=incomplete,
            )

        malformed = {
            **self.preflight,
            "numeric_reporting": {
                "active": "yes",
                "status": "passed",
                "reason": "not trusted",
            },
        }
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "numeric_reporting status is invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=malformed,
            )

    def test_numeric_reporting_evidence_is_preserved_strict_and_bounded(
        self,
    ) -> None:
        evidence = {
            "active": True,
            "status": "passed",
            "reason": "trusted numeric reporting checks passed",
            "numeric_outputs": 1,
            "lean_source_sha256": self.preflight[
                "numeric_reporting"
            ]["lean_source_sha256"],
            "bundle_sha256": self.preflight[
                "numeric_reporting"
            ]["bundle_sha256"],
            "certificates": [{
                "output_id": "value",
                "reporting_policy_kind": "significant_figures",
                "reporting_policy_digits": 3,
                "reported_value": "7",
                "reporting_quantum": "1/100",
                "raw_declaration": "Example.rawValue",
                "reporting_declaration": "Example.reportingProof",
            }],
            "lean_probe_passed": True,
        }
        contract = resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight={**self.preflight, "numeric_reporting": evidence},
        )
        self.assertEqual(contract["preflight"]["numeric_reporting"], evidence)

        bad_evidence = {**evidence, "unexpected": True}
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError,
            "numeric_reporting fields are ambiguous",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight={
                    **self.preflight,
                    "numeric_reporting": bad_evidence,
                },
            )

        oversized = {
            **self.preflight["numeric_reporting"],
            "reason": "x" * 4097,
        }
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "numeric_reporting status is invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight={**self.preflight, "numeric_reporting": oversized},
            )

        too_many = {
            **self.preflight["numeric_reporting"],
            "numeric_outputs": 257,
        }
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "numeric_reporting evidence is invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight={**self.preflight, "numeric_reporting": too_many},
            )

        long_certificate = {
            **evidence,
            "certificates": [{
                **evidence["certificates"][0],
                "raw_declaration": "x" * 4097,
            }],
        }
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError,
            "numeric_reporting evidence is invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight={
                    **self.preflight,
                    "numeric_reporting": long_certificate,
                },
            )

    def test_compile_success_numeric_reporting_failure_is_unambiguous(
        self,
    ) -> None:
        reporting_failure = {
            "active": True,
            "status": "failed",
            "reason": "Lean rejected the reporting probe",
            "numeric_outputs": 1,
            "lean_source_sha256": self.preflight[
                "numeric_reporting"
            ]["lean_source_sha256"],
            "bundle_sha256": self.preflight[
                "numeric_reporting"
            ]["bundle_sha256"],
            "certificates": [{
                "output_id": "value",
                "reporting_policy_kind": "significant_figures",
                "reporting_policy_digits": 3,
                "reported_value": "7",
                "reporting_quantum": "1/100",
                "raw_declaration": "Example.rawValue",
                "reporting_declaration": "Example.reportingProof",
            }],
            "lean_probe_passed": False,
        }
        failed = {
            **self.preflight,
            "status": "failed",
            "compiles": True,
            "returncode": 0,
            "numeric_reporting": reporting_failure,
        }
        contract = resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight=failed,
        )
        self.assertEqual(contract["preflight"], failed)

        contradictory = {
            **failed,
            "numeric_reporting": {
                **reporting_failure,
                "active": False,
            },
        }
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError,
            "numeric_reporting is contradictory",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=contradictory,
            )

        timeout = {**failed, "status": "timeout"}
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError,
            "deterministic Lean preflight status is contradictory",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=timeout,
            )

    def test_config_symlink_is_rejected_but_legacy_supplied_contract_remains(self) -> None:
        config_path = self.state / "config.json"
        config_payload = config_path.read_bytes()
        config_path.unlink()
        real_config = self.project / "real-config.json"
        real_config.write_bytes(config_payload)
        config_path.symlink_to(real_config)
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "may not traverse a symlink",
        ):
            self._contract()

        config_path.unlink()
        config_path.write_text(
            json.dumps({"loop": {"domain_profile": {"name": "chemistry"}}}),
            encoding="utf-8",
        )
        supplied = {"legacy": "unchanged"}
        resolved = resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight={},
            supplied_contract=supplied,
        )
        self.assertIs(resolved, supplied)

    def test_milestone_loaders_fail_closed_on_unhashable_output_id(
        self,
    ) -> None:
        contract = self._contract()
        cases = (
            (
                "proof",
                load_target_milestone,
                self._proof_milestone,
                "proof_review",
            ),
            (
                "formalization",
                load_target_formalization_milestone,
                self._formalization_milestone,
                "formalization_review",
            ),
        )
        for name, loader, make_row, review_key in cases:
            with self.subTest(name=name):
                path = self.output_root / name / "malformed.jsonl"
                path.parent.mkdir(parents=True, exist_ok=True)
                row = make_row(contract)
                row[review_key]["requested_outputs"][0]["output_id"] = []
                path.write_text(
                    json.dumps(row) + "\n", encoding="utf-8",
                )
                loaded, error = loader(path, self.rel, contract)
                self.assertIsNone(loaded)
                self.assertIn(
                    "output_id is not bound problem evidence", error,
                )

    def test_pre_worker_input_drift_ignores_valid_stale_milestone(self) -> None:
        cases = (
            (
                "proof",
                _run_review_worker,
                load_target_milestone,
                self._proof_milestone,
                "archon.commands.loop.parallel_review.build_runner",
            ),
            (
                "formalization",
                _run_formalization_review_worker,
                load_target_formalization_milestone,
                self._formalization_milestone,
                "archon.commands.loop.parallel_formalization_review.build_runner",
            ),
        )
        for name, worker, loader, make_row, patch_path in cases:
            with self.subTest(name=name):
                self.target.write_text(self.lean_source, encoding="utf-8")
                contract = self._contract()
                output = self.output_root / name / "pre"
                output.mkdir(parents=True, exist_ok=True)
                milestone = output / "milestones.jsonl"
                milestone.write_text(
                    json.dumps(make_row(contract)) + "\n",
                    encoding="utf-8",
                )
                self.assertEqual(loader(milestone, self.rel, contract)[1], "")
                self.target.write_text(
                    self.lean_source + "-- input drift\n",
                    encoding="utf-8",
                )
                spec = TargetReviewSpec(
                    rel=self.rel,
                    prompt="bounded prompt",
                    output_dir=str(output),
                    log_base=str(output / "agent"),
                    attempt=1,
                    source_contract=contract,
                )
                with patch(patch_path) as build:
                    outcome = worker(
                        spec,
                        project_path=self.project,
                        verbose_logs=False,
                        model=None,
                        backend=None,
                        harness=None,
                    )
                build.assert_not_called()
                self.assertIsNone(outcome.milestone)
                self.assertIn("changed after contract creation", outcome.error)

    def test_post_worker_input_drift_ignores_valid_stale_milestone(self) -> None:
        cases = (
            (
                "proof",
                _run_review_worker,
                load_target_milestone,
                self._proof_milestone,
                "archon.commands.loop.parallel_review.build_runner",
            ),
            (
                "formalization",
                _run_formalization_review_worker,
                load_target_formalization_milestone,
                self._formalization_milestone,
                "archon.commands.loop.parallel_formalization_review.build_runner",
            ),
        )
        for name, worker, loader, make_row, patch_path in cases:
            with self.subTest(name=name):
                self.target.write_text(self.lean_source, encoding="utf-8")
                contract = self._contract()
                output = self.output_root / name / "post"
                output.mkdir(parents=True, exist_ok=True)
                milestone = output / "milestones.jsonl"
                milestone.write_text(
                    json.dumps(make_row(contract)) + "\n",
                    encoding="utf-8",
                )
                self.assertEqual(loader(milestone, self.rel, contract)[1], "")
                runner = Mock()

                def mutate_candidate(*_args, **_kwargs):
                    self.target.write_text(
                        self.lean_source + "-- worker drift\n",
                        encoding="utf-8",
                    )
                    return True

                runner.run.side_effect = mutate_candidate
                spec = TargetReviewSpec(
                    rel=self.rel,
                    prompt="bounded prompt",
                    output_dir=str(output),
                    log_base=str(output / "agent"),
                    attempt=1,
                    source_contract=contract,
                )
                harness = HarnessDescriptor(name="codex", runner="codex")
                with patch(patch_path, return_value=runner):
                    outcome = worker(
                        spec,
                        project_path=self.project,
                        verbose_logs=False,
                        model=None,
                        backend=None,
                        harness=harness,
                    )
                runner.run.assert_called_once()
                self.assertEqual(
                    runner.run.call_args.kwargs["extra_args"],
                    [
                        "--image",
                        str((self.project / self.image_rel).resolve()),
                        "--",
                    ],
                )
                self.assertTrue(outcome.runner_ok)
                self.assertIsNone(outcome.milestone)
                self.assertIn("changed after contract creation", outcome.error)


    def test_requested_outputs_require_exact_one_to_one_coverage(self) -> None:
        self.row["requested_outputs"].append({
            "id": "second_value",
            "kind": "integer",
            "source_requirement": "the independently derived second value",
            "reporting_policy": {"kind": "exact_integer"},
            "unit": "",
        })
        self._materialize_workspace()
        contract = self._contract()
        audit = self._source_audit(contract)
        self.assertEqual(
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
            "",
        )

        variants = {}
        missing = json.loads(json.dumps(audit))
        missing["requested_outputs"].pop()
        variants["missing"] = missing
        duplicate = json.loads(json.dumps(audit))
        duplicate["requested_outputs"][1] = dict(
            duplicate["requested_outputs"][0]
        )
        variants["duplicate"] = duplicate
        bogus = json.loads(json.dumps(audit))
        bogus["requested_outputs"][1]["source_requirement"] = "bogus"
        variants["bogus"] = bogus
        blocked = json.loads(json.dumps(audit))
        blocked["requested_outputs"][1]["status"] = "blocked"
        variants["blocked"] = blocked
        submission_failed = json.loads(json.dumps(audit))
        submission_failed["requested_outputs"][1][
            "submission_status"
        ] = "failed"
        variants["submission_failed"] = submission_failed
        reporting_failed = json.loads(json.dumps(audit))
        reporting_failed["requested_outputs"][1][
            "reporting_policy_status"
        ] = "failed"
        variants["reporting_failed"] = reporting_failed
        swapped = json.loads(json.dumps(audit))
        swapped["requested_outputs"].reverse()
        variants["swapped"] = swapped
        unhashable_output_id = json.loads(json.dumps(audit))
        unhashable_output_id["requested_outputs"][0]["output_id"] = []
        variants["unhashable_output_id"] = unhashable_output_id
        for name, review in variants.items():
            with self.subTest(name=name):
                self.assertNotEqual(
                    validate_native_review_source_certificate(
                        review, contract, passing=True,
                    ),
                    "",
                )

    def test_opt_in_component_accounting_is_bound_and_fail_closed(self) -> None:
        output_contract = self.row["requested_outputs"][0]
        output_contract["audit_requirements"] = [
            "image_component_accounting"
        ]
        self._materialize_workspace()
        contract = self._contract()
        review = self._source_audit(contract)
        output = review["requested_outputs"][0]

        missing_error = validate_native_review_source_certificate(
            review, contract, passing=True,
        )
        self.assertIn("no component accounting audit", missing_error)

        image = contract["images"][0]
        output["composition_accounting"] = {
            "source_images": [{
                "path": image["path"],
                "sha256": image["sha256"],
            }],
            "product_nodes": [
                {
                    "node_id": "repeat_core",
                    "node_kind": "repeat_unit",
                    "formula_or_descriptor": "whole bracketed repeat unit",
                    "source_path": image["path"],
                    "source_locator": "left bracketed unit pattern",
                    "multiplicity": 2,
                },
                {
                    "node_id": "terminal_fragment",
                    "node_kind": "terminal_fragment",
                    "formula_or_descriptor": "whole terminal fragment",
                    "source_path": image["path"],
                    "source_locator": "right terminal fragment",
                    "multiplicity": 1,
                },
                {
                    "node_id": "sodium_adduct",
                    "node_kind": "adduct",
                    "formula_or_descriptor": "sodium adduct",
                    "source_path": image["path"],
                    "source_locator": "requested ion annotation",
                    "multiplicity": 1,
                },
            ],
            "assembly_edges": [
                {
                    "edge_id": "repeat_to_terminal",
                    "from_node_id": "repeat_core",
                    "to_node_id": "terminal_fragment",
                    "relation": "covalent_bond",
                    "multiplicity": 1,
                },
                {
                    "edge_id": "terminal_to_adduct",
                    "from_node_id": "terminal_fragment",
                    "to_node_id": "sodium_adduct",
                    "relation": "adduct_association",
                    "multiplicity": 1,
                },
            ],
            "boundary_checks": [
                {
                    "boundary_id": "repeat_bracket",
                    "boundary_kind": "bracket",
                    "source_path": image["path"],
                    "source_locator": "left repeat bracket",
                    "disposition": "included_in_node",
                    "assembly_edge_id": "none",
                    "status": "resolved",
                },
                {
                    "boundary_id": "outgoing_bond",
                    "boundary_kind": "cross_boundary_bond",
                    "source_path": image["path"],
                    "source_locator": "bond leaving repeat bracket",
                    "disposition": "represented_by_edge",
                    "assembly_edge_id": "repeat_to_terminal",
                    "status": "resolved",
                },
            ],
            "components": [
                {
                    "product_node_id": "repeat_core",
                    "label": "diagram repeat unit",
                    "formula_or_descriptor": "source-labelled unit A",
                    "multiplicity": 2,
                    "role": "repeat_unit",
                },
                {
                    "product_node_id": "terminal_fragment",
                    "label": "terminal fragment",
                    "formula_or_descriptor": "source-labelled terminal",
                    "multiplicity": 1,
                    "role": "terminal_group",
                },
                {
                    "product_node_id": "sodium_adduct",
                    "label": "ion adduct",
                    "formula_or_descriptor": "source-requested ion",
                    "multiplicity": 1,
                    "role": "adduct",
                },
            ],
            "assembly_expression": (
                "2 * repeat_core + terminal_fragment + "
                "sodium_adduct"
            ),
            "combined_formula_or_quantity": "independently combined carrier",
            "lean_carrier": output["lean_carrier"],
            "status": "matched",
            "evidence": "all visual components were independently recounted",
        }
        self.assertEqual(
            validate_native_review_source_certificate(
                review, contract, passing=True,
            ),
            "",
        )
        normalized = normalized_review_source_certificate(review)
        self.assertEqual(
            normalized["requested_outputs"][0]["composition_accounting"],
            output["composition_accounting"],
        )
        self.assertEqual(
            validate_native_review_source_certificate(
                normalized, contract, passing=True,
            ),
            "",
        )

        old_single_bracket = json.loads(json.dumps(review))
        old_accounting = old_single_bracket["requested_outputs"][0][
            "composition_accounting"
        ]
        old_accounting["product_nodes"] = [
            old_accounting["product_nodes"][0],
            old_accounting["product_nodes"][2],
        ]
        old_accounting["assembly_edges"] = [{
            "edge_id": "bracket_to_sodium",
            "from_node_id": "repeat_core",
            "to_node_id": "sodium_adduct",
            "relation": "adduct_association",
            "multiplicity": 1,
        }]
        old_accounting["boundary_checks"] = [
            {
                "boundary_id": "repeat_bracket",
                "boundary_kind": "bracket",
                "source_path": image["path"],
                "source_locator": "single printed bracket",
                "disposition": "included_in_node",
                "assembly_edge_id": "none",
                "status": "resolved",
            },
            {
                "boundary_id": "claimed_outgoing_bond",
                "boundary_kind": "cross_boundary_bond",
                "source_path": image["path"],
                "source_locator": "claimed bracket-to-adduct connection",
                "disposition": "represented_by_edge",
                "assembly_edge_id": "bracket_to_sodium",
                "status": "resolved",
            },
        ]
        old_accounting["components"] = [
            old_accounting["components"][0],
            old_accounting["components"][2],
        ]
        old_accounting["assembly_expression"] = "single bracket residue + Na"
        self.assertIn(
            "at least two non-adduct product nodes",
            validate_native_review_source_certificate(
                old_single_bracket, contract, passing=True,
            ),
        )

        variants: dict[str, dict] = {}
        failed = json.loads(json.dumps(review))
        failed["requested_outputs"][0]["composition_accounting"][
            "status"
        ] = "failed"
        variants["failed"] = failed
        empty = json.loads(json.dumps(review))
        empty["requested_outputs"][0]["composition_accounting"][
            "components"
        ] = []
        variants["empty"] = empty
        bad_role = json.loads(json.dumps(review))
        bad_role["requested_outputs"][0]["composition_accounting"][
            "components"
        ][0]["role"] = "invented_role"
        variants["bad_role"] = bad_role
        bad_multiplicity = json.loads(json.dumps(review))
        bad_multiplicity["requested_outputs"][0]["composition_accounting"][
            "components"
        ][0]["multiplicity"] = "2"
        variants["bad_multiplicity"] = bad_multiplicity
        unbound_image = json.loads(json.dumps(review))
        unbound_image["requested_outputs"][0]["composition_accounting"][
            "source_images"
        ][0]["path"] = "unbound.png"
        variants["unbound_image"] = unbound_image
        mismatched_carrier = json.loads(json.dumps(review))
        mismatched_carrier["requested_outputs"][0][
            "composition_accounting"
        ]["lean_carrier"] = "different_carrier"
        variants["mismatched_carrier"] = mismatched_carrier
        extra_field = json.loads(json.dumps(review))
        extra_field["requested_outputs"][0]["composition_accounting"][
            "derived_value"
        ] = "unbound"
        variants["extra_field"] = extra_field
        duplicate_node = json.loads(json.dumps(review))
        duplicate_node["requested_outputs"][0]["composition_accounting"][
            "product_nodes"
        ][1]["node_id"] = "repeat_core"
        variants["duplicate_node"] = duplicate_node
        bad_node_multiplicity = json.loads(json.dumps(review))
        bad_node_multiplicity["requested_outputs"][0][
            "composition_accounting"
        ]["product_nodes"][0]["multiplicity"] = 0
        variants["bad_node_multiplicity"] = bad_node_multiplicity
        bad_edge_ref = json.loads(json.dumps(review))
        bad_edge_ref["requested_outputs"][0]["composition_accounting"][
            "assembly_edges"
        ][0]["to_node_id"] = "missing_node"
        variants["bad_edge_ref"] = bad_edge_ref
        bad_edge_multiplicity = json.loads(json.dumps(review))
        bad_edge_multiplicity["requested_outputs"][0][
            "composition_accounting"
        ]["assembly_edges"][0]["multiplicity"] = True
        variants["bad_edge_multiplicity"] = bad_edge_multiplicity
        disconnected = json.loads(json.dumps(review))
        disconnected["requested_outputs"][0]["composition_accounting"][
            "assembly_edges"
        ].pop()
        variants["disconnected"] = disconnected
        ambiguous = json.loads(json.dumps(review))
        ambiguous_boundary = ambiguous["requested_outputs"][0][
            "composition_accounting"
        ]["boundary_checks"][1]
        ambiguous_boundary["disposition"] = "ambiguous"
        ambiguous_boundary["assembly_edge_id"] = "none"
        ambiguous_boundary["status"] = "ambiguous"
        variants["ambiguous"] = ambiguous
        duplicate_boundary = json.loads(json.dumps(review))
        duplicate_boundary["requested_outputs"][0][
            "composition_accounting"
        ]["boundary_checks"][1]["boundary_id"] = "repeat_bracket"
        variants["duplicate_boundary"] = duplicate_boundary
        omitted_component = json.loads(json.dumps(review))
        omitted_component["requested_outputs"][0][
            "composition_accounting"
        ]["components"].pop(1)
        variants["omitted_component"] = omitted_component
        mismatched_component_multiplicity = json.loads(json.dumps(review))
        mismatched_component_multiplicity["requested_outputs"][0][
            "composition_accounting"
        ]["components"][0]["multiplicity"] = 1
        variants[
            "mismatched_component_multiplicity"
        ] = mismatched_component_multiplicity
        bad_component_ref = json.loads(json.dumps(review))
        bad_component_ref["requested_outputs"][0][
            "composition_accounting"
        ]["components"][1]["product_node_id"] = "missing_node"
        variants["bad_component_ref"] = bad_component_ref
        assembly_omits_node = json.loads(json.dumps(review))
        assembly_omits_node["requested_outputs"][0][
            "composition_accounting"
        ]["assembly_expression"] = "repeat_core + sodium_adduct"
        variants["assembly_omits_node"] = assembly_omits_node
        missing_node_error = validate_native_review_source_certificate(
            assembly_omits_node, contract, passing=True,
        )
        self.assertIn(
            'missing=["terminal_fragment"]', missing_node_error,
        )
        for name, variant in variants.items():
            with self.subTest(name=name):
                self.assertNotEqual(
                    validate_native_review_source_certificate(
                        variant, contract, passing=True,
                    ),
                    "",
                )

        expanded_contract = json.loads(json.dumps(contract))
        expanded_contract["images"].append({
            "path": "icho_2026_source/image/preceding-page.png",
            "sha256": "e" * 64,
        })
        self.assertIn(
            "source_images do not cover every bound image",
            _validate_native_composition_accounting(
                review["requested_outputs"][0],
                contract["problem_evidence"]["requested_outputs"][0],
                expanded_contract,
                index=1,
                passing=True,
            ),
        )

    def test_component_accounting_marker_and_prompts_are_controller_bound(
        self,
    ) -> None:
        self.row["requested_outputs"][0]["audit_requirements"] = [
            "image_component_accounting"
        ]
        self._materialize_workspace()
        contract = self._contract()
        shared = render_native_composition_accounting_prompt(contract)
        self.assertIn("MANDATORY IMAGE COMPONENT ACCOUNTING", shared)
        self.assertIn('"value"', shared)
        self.assertIn("not_applicable is forbidden", shared)
        formalizer_prompt = _native_formalizer_semantic_dag_block(
            project_path=self.project, target=self.target,
        )
        self.assertIn("MANDATORY WHOLE-PRODUCT IMAGE TOPOLOGY", formalizer_prompt)
        self.assertIn("NEVER add composition_accounting", formalizer_prompt)

        proof_prompt = build_target_review_prompt(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            target=self.target,
            output_dir=self.output_root / "component-proof",
            preflight=self.preflight,
            prior_gate_record={},
            source_contract=contract,
        )
        formal_prompt = build_target_formalization_review_prompt(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            target=self.target,
            output_dir=self.output_root / "component-formalization",
            preflight=self.preflight,
            prior_gate_record={},
            source_contract=contract,
        )
        for prompt in (proof_prompt, formal_prompt):
            self.assertIn("MANDATORY IMAGE COMPONENT ACCOUNTING", prompt)
            self.assertIn("composition_accounting", prompt)
            self.assertIn("source_images must exactly cover all bound", prompt)
            self.assertIn("product_nodes", prompt)
            self.assertIn("printed formula label may denote only", prompt)
            self.assertIn("preceding-page unit pattern", prompt)
            self.assertIn("complete node graph connected", prompt)
            self.assertIn(
                "assembly_expression must contain every "
                "product_nodes[].node_id verbatim",
                prompt,
            )

    def test_unknown_or_empty_component_audit_marker_is_rejected(self) -> None:
        for marker in ([], ["unknown"], ["image_component_accounting"] * 2):
            with self.subTest(marker=marker):
                self.row["requested_outputs"][0]["audit_requirements"] = marker
                self._materialize_workspace()
                with self.assertRaisesRegex(
                    ProblemOnlyReviewContractError, "audit_requirements",
                ):
                    self._contract()

    def test_unbound_component_accounting_is_rejected(self) -> None:
        contract = self._contract()
        review = self._source_audit(contract)
        output = review["requested_outputs"][0]
        output["composition_accounting"] = {
            "source_images": [],
            "components": [],
            "assembly_expression": "",
            "combined_formula_or_quantity": "",
            "lean_carrier": output["lean_carrier"],
            "status": "failed",
            "evidence": "not controller selected",
        }
        self.assertIn(
            "unbound composition_accounting",
            validate_native_review_source_certificate(
                review, contract, passing=False,
            ),
        )

    def test_source_report_pollution_and_nonfinite_evidence_fail_closed(self) -> None:
        report_path = self.project / self.report_rel
        report = json.loads(report_path.read_text(encoding="utf-8"))
        report["notes"] = "unbound generated note"
        report_path.write_text(json.dumps(report), encoding="utf-8")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "unexpected or missing fields",
        ):
            self._contract()

        self._materialize_workspace()
        bad_preflight = dict(self.preflight)
        bad_preflight["duration_secs"] = float("inf")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "diagnostics are invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=bad_preflight,
            )

        self.row["measurement_policy"]["nonfinite"] = float("nan")
        self._materialize_workspace()
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "non-finite JSON constant",
        ):
            self._contract()

    def test_bad_target_does_not_block_good_target_in_either_batch(self) -> None:
        bad = self.target.with_name("problem_missing.lean")
        bad.write_text(self.lean_source, encoding="utf-8")
        bad_rel = bad.relative_to(self.project).as_posix()
        bad_preflight = {**self.preflight, "file": bad_rel}

        proof_calls: list[str] = []

        def proof_worker(spec, **_kwargs):
            proof_calls.append(spec.rel)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._proof_milestone(spec.source_contract),
            )

        proof_report = run_parallel_target_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target, bad],
            preflight={"targets": [self.preflight, bad_preflight]},
            prior_gate_targets={},
            requested_jobs=2,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=proof_worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertFalse(proof_report["complete"])
        self.assertEqual(proof_report["reviewed"], 1)
        self.assertEqual(proof_report["unresolved"], [bad_rel])
        self.assertEqual(proof_calls, [self.rel])

        formal_calls: list[str] = []

        def formal_worker(spec, **_kwargs):
            formal_calls.append(spec.rel)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._formalization_milestone(spec.source_contract),
            )

        formal_report = run_parallel_formalization_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target, bad],
            preflight={"targets": [self.preflight, bad_preflight]},
            prior_gate_targets={},
            requested_jobs=2,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=formal_worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertFalse(formal_report["complete"])
        self.assertEqual(formal_report["reviewed"], 1)
        self.assertEqual(formal_report["unresolved"], [bad_rel])
        self.assertEqual(formal_calls, [self.rel])

    def test_lifecycle_keeps_formal_contract_after_proof_body_change(self) -> None:
        (self.iter_dir / "provers").mkdir(parents=True, exist_ok=True)
        (self.state / "task_results").mkdir(parents=True, exist_ok=True)
        (self.iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
        formal_contracts: list[dict] = []
        proof_contracts: list[dict] = []
        formalizer_prompts: list[str] = []
        answer_path = answer_submission_path(self.project, self.row["id"])
        answer_payload = answer_path.read_text(encoding="utf-8")
        answer_path.unlink()

        def preflight_checker(*, project_path, target, timeout_sec):
            del project_path, timeout_sec
            source = target.read_text(encoding="utf-8")
            return {
                **self.preflight,
                "sorry_count": source.count("sorry"),
                "numeric_reporting": {
                    **self.preflight["numeric_reporting"],
                    "lean_source_sha256": _sha256(source.encode()),
                },
            }

        def formalizer(*_args, **_kwargs):
            formalizer_prompts.append(_args[0])
            self.target.write_text(
                "theorem item_a : True := by sorry\n", encoding="utf-8",
            )
            result = self.state / "task_results" / "problem_item_a.lean.md"
            result.write_text("# Native redraft\n", encoding="utf-8")
            answer_path.write_text(answer_payload, encoding="utf-8")
            return True

        def formal_review(spec, **_kwargs):
            formal_contracts.append(spec.source_contract)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._formalization_milestone(spec.source_contract),
            )

        def prover(*_args, **_kwargs):
            self.target.write_text(self.lean_source, encoding="utf-8")
            return True

        def proof_review(spec, **_kwargs):
            proof_contracts.append(spec.source_contract)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._proof_milestone(spec.source_contract),
            )

        runner = ParallelProverRunner(
            project_name="project",
            project_path=self.project,
            state_dir=self.state,
            stage="autoformalize",
            iter_dir=self.iter_dir,
            iter_meta=self.iter_dir / "meta.json",
            iter_num=1,
            max_parallel=1,
            max_objectives=1,
            block_on_blocked_deps=False,
            verbose_logs=False,
            model="test",
            pipeline_review=PipelinedTargetReviewConfig(
                requested_jobs=1,
                max_attempts=1,
                backoff_sec=0,
                formalization_review_enabled=True,
                formalization_review_max_attempts=1,
                formalization_review_backoff_sec=0,
            ),
            executor_factory=ThreadPoolExecutor,
            prover_worker=prover,
            review_worker=proof_review,
            formalization_review_worker=formal_review,
            formalizer_worker=formalizer,
            preflight_checker=preflight_checker,
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
            runner._run_fanout([self.target], file_modes={})

        self.assertEqual(len(formalizer_prompts), 1)
        self.assertIn("CONTROLLER SEMANTIC DAG", formalizer_prompts[0])
        self.assertIn('"requested_output_ids": ["value"]', formalizer_prompts[0])
        self.assertIn("TARGET ANSWER SUBMISSION CONTRACT", formalizer_prompts[0])
        self.assertIn("IChO2026Problems_problem_item_a.answer.json", formalizer_prompts[0])
        self.assertEqual(len(formal_contracts), 1)
        self.assertEqual(len(proof_contracts), 1)
        self.assertNotEqual(
            formal_contracts[0]["candidate_sha256"],
            proof_contracts[0]["candidate_sha256"],
        )
        report = json.loads(
            (self.iter_dir / "pipelined-review.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertTrue(report["complete"])
        self.assertTrue(report["gate_events_applied"])
        self.assertTrue(
            report["formalizer_results"][self.rel]["answer_submission_valid"]
        )
        self.assertEqual(
            [event["kind"] for event in report["gate_events"]],
            ["formalization", "proof"],
        )
        formal_gate = json.loads(
            (self.state / "formalization-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        proof_gate = json.loads(
            (self.state / "proof-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertEqual(formal_gate["targets"][self.rel]["status"], "passed")
        self.assertEqual(proof_gate["targets"][self.rel]["status"], "solved")

    def test_changed_incomplete_redraft_evicts_stale_proof_outcome(self) -> None:
        (self.iter_dir / "provers").mkdir(parents=True, exist_ok=True)
        (self.state / "task_results").mkdir(parents=True, exist_ok=True)
        (self.iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")

        def preflight_checker(*, project_path, target, timeout_sec):
            del project_path, target, timeout_sec
            return dict(self.preflight)

        def proof_review(spec, **_kwargs):
            milestone = self._proof_milestone(spec.source_contract)
            milestone["status"] = "blocked"
            milestone["proof_review"].update({
                "route": "needs_redraft",
                "reason": "the statement must be redrafted",
                "evidence": "the candidate statement omits a source relation",
                "redraft_kind": "other_modeling_defect",
            })
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=milestone,
            )

        def incomplete_formalizer(*_args, **_kwargs):
            self.target.write_text(
                self.lean_source + "-- changed without a task result\n",
                encoding="utf-8",
            )
            return True

        def unexpected_formal_review(*_args, **_kwargs):
            raise AssertionError("incomplete redraft must not be reviewed")

        runner = ParallelProverRunner(
            project_name="project",
            project_path=self.project,
            state_dir=self.state,
            stage="prover",
            iter_dir=self.iter_dir,
            iter_meta=self.iter_dir / "meta.json",
            iter_num=1,
            max_parallel=1,
            max_objectives=1,
            block_on_blocked_deps=False,
            verbose_logs=False,
            model="test",
            pipeline_review=PipelinedTargetReviewConfig(
                requested_jobs=1,
                max_attempts=1,
                backoff_sec=0,
                formalization_review_enabled=True,
                formalization_review_max_attempts=1,
                formalization_review_backoff_sec=0,
            ),
            executor_factory=ThreadPoolExecutor,
            prover_worker=lambda *_args, **_kwargs: True,
            review_worker=proof_review,
            formalization_review_worker=unexpected_formal_review,
            formalizer_worker=incomplete_formalizer,
            preflight_checker=preflight_checker,
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
            runner._run_fanout([self.target], file_modes={})

        report = json.loads(
            (self.iter_dir / "pipelined-review.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertFalse(report["complete"])
        self.assertEqual(report["status"], "incomplete")
        self.assertEqual(report["settled_target_files"], [])
        self.assertEqual(report["unresolved"], [self.rel])
        self.assertEqual(report["pending_formalization_targets"], [self.rel])
        self.assertFalse(report["gate_events_applied"])
        self.assertEqual(report["proof_review_target_files"], [])
        self.assertEqual(report["reviewed"], 0)
        self.assertIn(
            "did not update its task result",
            report["errors"][self.rel],
        )
        self.assertTrue(report["formalizer_results"][self.rel]["changed"])
        self.assertFalse(
            report["formalizer_results"][self.rel]["task_result_updated"],
        )
        session = (
            self.state / "proof-journal" / "sessions" / "session_1"
            / "milestones.jsonl"
        )
        self.assertFalse(session.exists())
        proof_gate = json.loads(
            (self.state / "proof-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        formal_gate = json.loads(
            (self.state / "formalization-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertEqual(
            proof_gate["targets"][self.rel]["status"], "needs_redraft",
        )
        self.assertEqual(
            formal_gate["targets"][self.rel]["status"], "retry",
        )

    def test_durable_native_session_rejects_stale_source_and_preflight(self) -> None:
        contract = self._contract()
        milestone = self._proof_milestone(contract)
        nested = milestone.pop("proof_review")
        milestone["findings"]["proof_review"] = nested
        outcome = TargetReviewOutcome(
            rel=self.rel,
            attempt=1,
            runner_ok=True,
            milestone=milestone,
        )
        session_dir = (
            self.state / "proof-journal" / "sessions" / "session_1"
        )
        write_parallel_review_session(
            session_dir=session_dir,
            iter_num=1,
            outcomes={self.rel: outcome},
        )
        self.assertEqual(
            validate_parallel_review_session(
                session_dir=session_dir,
                expected_rels=[self.rel],
                project_path=self.project,
            ),
            "",
        )

        preflight = {
            "iteration": 1,
            "jobs": 1,
            "duration_secs": self.preflight["duration_secs"],
            "summary": {"total": 1, "passed": 1, "failed": 0},
            "targets": [self.preflight],
        }
        report = {
            "iteration": 1,
            "complete": True,
            "status": "complete",
            "pipeline_mode": "target_lifecycle",
            "starts_at": "formalizer",
            "target_files": [self.rel],
            "settled_target_files": [self.rel],
            "proof_review_target_files": [self.rel],
            "targets": 1,
            "reviewed": 1,
            "unresolved": [],
            "preflight": preflight,
            "gate_events_applied": False,
        }
        write_pipelined_review_report(iter_dir=self.iter_dir, report=report)
        loaded, error = load_pipelined_review_report(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(loaded)

        report["pending_formalization_targets"] = [self.rel]
        write_pipelined_review_report(iter_dir=self.iter_dir, report=report)
        loaded, error = load_pipelined_review_report(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
        )
        self.assertIsNone(loaded)
        self.assertIn(
            "still has pending formalization targets",
            error,
        )
        report["pending_formalization_targets"] = []
        self.target.write_text(
            self.lean_source + "-- stale candidate\n", encoding="utf-8",
        )
        self.assertIn(
            "does not match native problem-only evidence",
            validate_parallel_review_session(
                session_dir=session_dir,
                expected_rels=[self.rel],
                project_path=self.project,
            ),
        )
        self.target.write_text(self.lean_source, encoding="utf-8")

        failed_row = {
            **self.preflight,
            "status": "failed",
            "compiles": False,
            "returncode": 1,
            "sorry_count": 0,
            "diagnostics": "compile failed",
        }
        report["preflight"] = {
            **preflight,
            "summary": {"total": 1, "passed": 0, "failed": 1},
            "targets": [failed_row],
        }
        write_pipelined_review_report(iter_dir=self.iter_dir, report=report)
        loaded, error = load_pipelined_review_report(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
        )
        self.assertIsNone(loaded)
        self.assertIn("lacks successful", error)

if __name__ == "__main__":
    unittest.main()
