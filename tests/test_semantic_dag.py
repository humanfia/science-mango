from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from archon.commands.loop.problem_only_review_contract import (
    render_native_formalizer_semantic_dag_prompt,
)
from archon.commands.loop.prover.runners import (
    MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES,
    _ImmediateRedraftPromptError,
    _native_formalizer_semantic_dag_block,
    _sealed_mode_reference,
    build_immediate_redraft_prompt,
)
from archon.commands.loop.review_feedback import (
    MAX_REPAIR_TASK_PROMPT_BYTES,
    build_feedback_event,
    build_repair_task,
    render_repair_task,
)
from archon.commands.loop.semantic_dag import (
    SemanticDagError,
    build_semantic_dag,
    render_solver_semantic_dag_prompt,
    semantic_dag_provenance,
)


def _source_bound_repair_task(
    *, truncated: bool = False, evidence_size: int = 32,
) -> dict:
    action = {
        "check_id": "bridge_obligations[0]",
        "source_claim": "derive the source-stated residue identity",
        "current_carrier": "missing open-air classification bridge",
        "evidence": "e" * evidence_size,
    }
    return {
        "schema_version": 1,
        "kind": "controller_sanitized_review_repair",
        "review_kind": "formalization",
        "worker_stage": "formalization",
        "candidate_sha256": "a" * 64,
        "reason_codes": ["failed_structured_checks"],
        "failed_check_ids": ["bridge_obligations[0]"],
        "required_actions": [
            "repair_the_statement_or_model_then_revalidate",
        ],
        "history": {
            "events": [{
                "event_id": "pipeline:1:Problem.lean:formalization:1",
                "iteration": 1,
                "attempt": 1,
            }],
        },
        "source_bound_review": {
            "certificate_sha256": "b" * 64,
            "source_contract_sha256": "c" * 64,
            "source_binding": {
                "candidate_sha256": "a" * 64,
                "source_bundle_sha256": "1" * 64,
                "source_record_sha256": "2" * 64,
                "answer_submission_sha256": "3" * 64,
                "question_sha256": "4" * 64,
                "requested_outputs_sha256": "5" * 64,
            },
            "reason": "the source bridge is missing",
            "repair_action_projection": {
                "bridge_obligations_count": 1,
                "failed_bridge_count": 1,
                "retained_count": 0 if truncated else 1,
                "truncated": truncated,
                "bridge_obligations_sha256": "d" * 64,
            },
            "repair_actions": [] if truncated else [action],
        },
    }


def _a6_cycle_three_repair_task() -> dict:
    """Reproduce the accepted 8,700-byte A6 cycle-three hand-off shape."""
    digest = "a" * 64
    failed_check_ids = [
        "blind_source_audit.candidate_domain_provenance",
        "blind_source_audit.raw_derivation",
        "blind_source_audit.tolerance_provenance",
        "bridge_obligations[10]",
        "bridge_obligations[12]",
        "bridge_obligations[13]",
        "bridge_obligations[15]",
        "bridge_obligations[16]",
        "bridge_obligations[2]",
        "bridge_obligations[3]",
        "bridge_obligations[5]",
        "bridge_obligations[7]",
        "bridge_obligations[8]",
        "checks.abstraction_sufficiency",
        "checks.countermodel_resistance",
        "checks.derivability",
        "checks.source_faithfulness",
        "checks.uncertainty_propagation",
        "chemistry_checks.answer_smuggling",
        "chemistry_checks.chemical_semantics",
        "chemistry_checks.conservation_laws",
        "chemistry_checks.identification_uniqueness",
        "chemistry_checks.structure_stereochemistry",
        "contract_audit.bridge_completeness",
        "contract_audit.hypothesis_derivability",
        "contract_audit.statement_scope",
        "requested_outputs[0]",
        "requested_outputs[1]",
    ]
    bridge_indices = [2, 3, 5, 7, 8, 10, 12, 13, 15, 16]
    repair_actions = [
        {
            "check_id": f"bridge_obligations[{index}]",
            "source_claim": (
                f"Source-ground the complete chemistry bridge {index}; "
                + "c" * 64
            ),
            "current_carrier": (
                f"current_answer_blind_carrier_{index}_" + "k" * 36
            ),
            "evidence": (
                f"Independent source audit blocker {index}: " + "e" * 150
            ),
        }
        for index in bridge_indices
    ]
    task = {
        "schema_version": 1,
        "kind": "controller_sanitized_review_repair",
        "review_kind": "formalization",
        "worker_stage": "formalization",
        "candidate_sha256": digest,
        "reason_codes": [
            "failed_structured_checks",
            "failed_source_bound_bridges",
        ],
        "failed_check_ids": failed_check_ids,
        "required_actions": [
            "repair_the_statement_or_model_then_revalidate",
        ],
        "preflight": {
            "status": "passed",
            "compiles": True,
            "returncode": 0,
            "sorry_count": 17,
            "duration_bucket": "under_60s",
        },
        "history": {
            "schema_version": 1,
            "review_kind": "formalization",
            "current_status": "retry",
            "reviews": 2,
            "events": [{
                "schema_version": 1,
                "review_kind": "formalization",
                "candidate_sha256": digest,
                "iteration": 1,
                "attempt": 2,
                "decision": "failed",
                "resulting_status": "retry",
                "failed_check_ids": failed_check_ids,
                "preflight": {
                    "status": "passed",
                    "compiles": True,
                    "returncode": 0,
                    "sorry_count": 17,
                },
            }],
        },
        "source_bound_review": {
            "certificate_sha256": "b" * 64,
            "source_contract_sha256": "c" * 64,
            "source_binding": {
                "candidate_sha256": digest,
                "source_bundle_sha256": "1" * 64,
                "source_record_sha256": "2" * 64,
                "answer_submission_sha256": "3" * 64,
                "question_sha256": "4" * 64,
                "requested_outputs_sha256": "5" * 64,
            },
            "reason": "r" * 455,
            "repair_action_projection": {
                "bridge_obligations_count": 17,
                "failed_bridge_count": 10,
                "retained_count": 10,
                "truncated": False,
                "bridge_obligations_sha256": "d" * 64,
            },
            "repair_actions": repair_actions,
        },
    }
    padding = 8_700 - len(render_repair_task(task).encode("utf-8"))
    if padding < 0:
        raise AssertionError("cycle-three fixture exceeded its observed size")
    repair_actions[-1]["evidence"] += "p" * padding
    assert len(render_repair_task(task).encode("utf-8")) == 8_700
    return task


class SemanticDagTest(unittest.TestCase):
    def setUp(self) -> None:
        self.evidence = {
            "question": "Shared source facts and measurements.",
            "shared_context": "A source-stated relation connects the parts.",
            "current_question": "Determine both requested quantities.",
            "previous_parts": [{
                "source_id": "item_a1",
                "part_id": "A.1",
                "question": "Determine the upstream identity.",
                "dependency_policy": "derive_in_blind_run",
            }],
            "requested_outputs": [
                {
                    "id": "formula",
                    "kind": "formula",
                    "source_requirement": "chemical formula",
                    "unit": "",
                    "reporting_policy": {"kind": "exact_symbolic"},
                },
                {
                    "id": "count",
                    "kind": "integer",
                    "source_requirement": "requested count",
                    "unit": "",
                    "reporting_policy": {"kind": "exact_integer"},
                },
            ],
            "reporting_policy": {"final_precision": "per_output"},
            "measurement_policy": {"tolerance": "source_derived"},
            "candidate_domain_policy": {"bounds": "source_derived"},
        }

    def _dag(self) -> dict:
        return build_semantic_dag(
            record_id="item_a2",
            problem_evidence=self.evidence,
        )

    def test_dag_is_deterministic_answer_free_and_connects_every_output(self) -> None:
        dag = self._dag()
        reordered = {key: self.evidence[key] for key in reversed(self.evidence)}
        self.assertEqual(
            dag,
            build_semantic_dag(
                record_id="item_a2", problem_evidence=reordered,
            ),
        )
        provenance = semantic_dag_provenance(dag)
        self.assertEqual(provenance["node_count"], 8)
        self.assertEqual(provenance["edge_count"], 10)
        self.assertEqual(
            provenance["requested_output_ids"], ["formula", "count"],
        )
        self.assertEqual(
            provenance["previous_part_source_ids"], ["item_a1"],
        )

        nodes = {node["id"]: node for node in dag["nodes"]}
        self.assertEqual(
            nodes["previous:0"]["state"], "requires_blind_derivation",
        )
        self.assertEqual(nodes["output:formula"]["state"], "unresolved")
        self.assertEqual(nodes["output:count"]["state"], "unresolved")
        for output_id in ("formula", "count"):
            incoming = {
                edge["from"]
                for edge in dag["edges"]
                if edge["to"] == f"derive:{output_id}"
            }
            self.assertEqual(
                incoming,
                {
                    "source:question",
                    "source:shared_context",
                    "source:current_question",
                    "previous:0",
                },
            )

        serialized = json.dumps(dag, ensure_ascii=False, sort_keys=True)
        for forbidden in (
            "result_spec",
            "official_solution",
            "official_answer",
            '"value"',
        ):
            self.assertNotIn(forbidden, serialized)

    def test_explicit_prior_reference_excludes_unrelated_context(self) -> None:
        evidence = copy.deepcopy(self.evidence)
        evidence["current_question"] = (
            "Using the value from 2.4, determine both requested quantities."
        )
        evidence["previous_parts"] = [
            {
                "source_id": "item_p2_q4",
                "part_id": "P2-Q4",
                "question": "Determine the upstream value.",
                "dependency_policy": "derive_in_blind_run",
            },
            {
                "source_id": "item_p2_q8",
                "part_id": "P2-Q8",
                "question": "Determine an unrelated neighboring value.",
                "dependency_policy": "derive_in_blind_run",
            },
        ]

        dag = build_semantic_dag(
            record_id="item_p2_q9", problem_evidence=evidence,
        )
        provenance = semantic_dag_provenance(dag)
        self.assertEqual(
            provenance["previous_part_source_ids"], ["item_p2_q4"],
        )
        self.assertFalse(
            any(node["id"] == "previous:1" for node in dag["nodes"])
        )
        self.assertFalse(
            any(edge["from"] == "previous:1" for edge in dag["edges"])
        )

        leaky = copy.deepcopy(evidence)
        leaky["previous_parts"][1]["answer"] = "SECRET"
        with self.assertRaisesRegex(SemanticDagError, "answer-bearing field"):
            build_semantic_dag(
                record_id="item_p2_q9", problem_evidence=leaky,
            )

    def test_fragment_reference_does_not_narrow_curated_data_flow(self) -> None:
        evidence = copy.deepcopy(self.evidence)
        evidence["current_question"] = (
            "Determine the molecular formula of the fatty acid (RCOOH), if "
            "the non-ionised form of PL1 contains 255 bonds in total. If you "
            "were unable to find the structural formula of PL1, you can use "
            "a-d fragments from 5.1."
        )
        evidence["previous_parts"] = [
            {
                "source_id": "item_t5_a1",
                "part_id": "T5-A1",
                "question": "Determine the a-d fragment inventory.",
                "dependency_policy": "derive_in_blind_run",
            },
            {
                "source_id": "item_t5_a2",
                "part_id": "T5-A2",
                "question": "Determine the structural formula of PL1.",
                "dependency_policy": "derive_in_blind_run",
            },
        ]

        dag = build_semantic_dag(
            record_id="item_t5_a3", problem_evidence=evidence,
        )
        self.assertEqual(
            semantic_dag_provenance(dag)["previous_part_source_ids"],
            ["item_t5_a1", "item_t5_a2"],
        )
        for output_id in ("formula", "count"):
            incoming = {
                edge["from"]
                for edge in dag["edges"]
                if edge["to"] == f"derive:{output_id}"
            }
            self.assertTrue({"previous:0", "previous:1"} <= incoming)

    def test_hash_changes_with_source_facts_or_output_contract(self) -> None:
        original = semantic_dag_provenance(self._dag())["sha256"]
        changed_fact = copy.deepcopy(self.evidence)
        changed_fact["shared_context"] += " Additional source fact."
        fact_hash = semantic_dag_provenance(build_semantic_dag(
            record_id="item_a2", problem_evidence=changed_fact,
        ))["sha256"]
        changed_output = copy.deepcopy(self.evidence)
        changed_output["requested_outputs"][0]["unit"] = "mol"
        output_hash = semantic_dag_provenance(build_semantic_dag(
            record_id="item_a2", problem_evidence=changed_output,
        ))["sha256"]
        self.assertEqual(len(original), 64)
        self.assertNotEqual(original, fact_hash)
        self.assertNotEqual(original, output_hash)

    def test_component_accounting_marker_is_strict_and_preserved(self) -> None:
        evidence = copy.deepcopy(self.evidence)
        evidence["requested_outputs"][0]["audit_requirements"] = [
            "image_component_accounting"
        ]
        dag = build_semantic_dag(
            record_id="item_a2", problem_evidence=evidence,
        )
        output = next(
            node for node in dag["nodes"] if node["id"] == "output:formula"
        )
        self.assertEqual(
            output["audit_requirements"], ["image_component_accounting"],
        )
        prompt = render_solver_semantic_dag_prompt(
            dag, semantic_dag_provenance(dag),
        )
        self.assertIn("connected whole-product topology", prompt)
        self.assertIn("printed formula can be a residue", prompt)
        self.assertIn("preceding-page unit pattern", prompt)
        self.assertIn("component ledger", prompt)
        self.assertIn("cannot be marked not_applicable", prompt)

        for invalid in ([], ["unknown"], ["image_component_accounting"] * 2):
            with self.subTest(invalid=invalid):
                bad = copy.deepcopy(self.evidence)
                bad["requested_outputs"][0]["audit_requirements"] = invalid
                with self.assertRaisesRegex(SemanticDagError, "invalid"):
                    build_semantic_dag(
                        record_id="item_a2", problem_evidence=bad,
                    )

    def test_answer_bearing_fields_fail_closed(self) -> None:
        for path, value in (
            (("previous_parts", 0, "answer"), "SECRET"),
            (("requested_outputs", 0, "result_spec"), {"value": "SECRET"}),
            (("official_solution",), "SECRET"),
        ):
            with self.subTest(path=path):
                evidence = copy.deepcopy(self.evidence)
                cursor = evidence
                for key in path[:-1]:
                    cursor = cursor[key]
                cursor[path[-1]] = value
                with self.assertRaisesRegex(
                    SemanticDagError, "answer-bearing field",
                ):
                    build_semantic_dag(
                        record_id="item_a2", problem_evidence=evidence,
                    )

    def test_renderer_rejects_stale_provenance(self) -> None:
        dag = self._dag()
        provenance = semantic_dag_provenance(dag)
        prompt = render_solver_semantic_dag_prompt(dag, provenance)
        self.assertIn("CONTROLLER SEMANTIC DAG", prompt)
        self.assertIn('"state": "unresolved"', prompt)
        stale = dict(provenance)
        stale["sha256"] = "0" * 64
        with self.assertRaisesRegex(SemanticDagError, "stale or mismatched"):
            render_solver_semantic_dag_prompt(dag, stale)
        leaky = copy.deepcopy(dag)
        leaky["official_solution"] = "SECRET"
        with self.assertRaisesRegex(
            SemanticDagError, "answer-bearing field",
        ):
            render_solver_semantic_dag_prompt(leaky)

    def test_native_formalizer_block_uses_fresh_controller_contract(self) -> None:
        dag = self._dag()
        provenance = semantic_dag_provenance(dag)
        contract = {
            "contract_kind": "native_problem_input_only",
            "target": "IChO/problem_semantic_case.lean",
            "semantic_dag": dag,
            "semantic_dag_provenance": provenance,
        }
        expected = (
            "CONSTANT\n\n" + render_native_formalizer_semantic_dag_prompt(contract)
            + "\n\nCOMPONENT\n\nANSWER"
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
                return_value=contract,
            ) as resolve,
            patch(
                "archon.commands.loop.prover.runners."
                "render_native_chemistry_constant_policy",
                return_value="CONSTANT",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "render_native_formalizer_composition_accounting_prompt",
                return_value="COMPONENT",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "render_native_formalizer_answer_submission_prompt",
                return_value="ANSWER",
            ),
        ):
            actual = _native_formalizer_semantic_dag_block(
                project_path=Path("/project"),
                target=Path("/project/Problem.lean"),
            )
        self.assertEqual(actual, expected)
        resolve.assert_called_once_with(
            project_path=Path("/project"),
            target=Path("/project/Problem.lean"),
        )

    def test_sealed_mode_reference_is_hash_bound_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_dir = Path(temp_dir) / ".archon"
            modes_dir = state_dir / "prover-modes"
            modes_dir.mkdir(parents=True)
            mode_file = modes_dir / "chemistry-formalize.md"
            payload = b"---\nname: chemistry-formalize\n---\nmandatory mode body\n"
            mode_file.write_bytes(payload)

            reference = _sealed_mode_reference(
                state_dir, "chemistry-formalize",
            )
            self.assertIsNotNone(reference)
            self.assertIn(str(mode_file.resolve()), reference)
            self.assertIn(hashlib.sha256(payload).hexdigest(), reference)
            self.assertIn(f"bytes={len(payload)}", reference)

            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "sealed prover mode name is invalid",
            ):
                _sealed_mode_reference(state_dir, "../escape")

            linked_state_dir = Path(temp_dir) / "linked-state"
            linked_state_dir.mkdir()
            (linked_state_dir / "prover-modes").symlink_to(
                modes_dir, target_is_directory=True,
            )
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "sealed prover mode reference is unavailable",
            ):
                _sealed_mode_reference(
                    linked_state_dir, "chemistry-formalize",
                )

            linked_mode = modes_dir / "linked-mode.md"
            linked_mode.symlink_to(mode_file)
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "sealed prover mode reference is unavailable",
            ):
                _sealed_mode_reference(state_dir, "linked-mode")

            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "sealed prover mode reference is unavailable",
            ):
                _sealed_mode_reference(state_dir, "missing-mode")

            (modes_dir / "empty-mode.md").write_bytes(b"")
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "sealed prover mode reference is empty",
            ):
                _sealed_mode_reference(state_dir, "empty-mode")

            (modes_dir / "oversized-mode.md").write_bytes(
                b"x" * (32 * 1024 + 1)
            )
            with patch.object(
                Path, "read_bytes",
                side_effect=AssertionError("oversized mode must not be read"),
            ) as read_bytes:
                with self.assertRaisesRegex(
                    _ImmediateRedraftPromptError,
                    "sealed prover mode reference exceeds 32 KiB",
                ):
                    _sealed_mode_reference(state_dir, "oversized-mode")
            read_bytes.assert_not_called()

            with patch.object(Path, "read_bytes", return_value=payload + b"x"):
                with self.assertRaisesRegex(
                    _ImmediateRedraftPromptError,
                    "sealed prover mode reference changed during read",
                ):
                    _sealed_mode_reference(
                        state_dir, "chemistry-formalize",
                    )

    def test_all_packaged_sealed_modes_fit_the_32_kib_limit(self) -> None:
        state_dir = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "archon"
            / ".archon-src"
        )
        modes_dir = state_dir / "prover-modes"
        mode_files = sorted(modes_dir.glob("*.md"))
        self.assertTrue(mode_files)
        sizes = [mode_file.stat().st_size for mode_file in mode_files]
        self.assertGreater(max(sizes), 16 * 1024)
        self.assertLessEqual(max(sizes), 32 * 1024)
        for mode_file in mode_files:
            reference = _sealed_mode_reference(state_dir, mode_file.stem)
            self.assertIsNotNone(reference)
            self.assertIn(f"bytes={mode_file.stat().st_size}", reference)

    def test_immediate_redraft_prompt_contains_semantic_dag(self) -> None:
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="BASE FORMALIZER PROMPT",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="SEMANTIC DAG SENTINEL",
            ),
        ):
            prompt = build_immediate_redraft_prompt(
                project_name="project",
                project_path=Path("/project"),
                state_dir=Path("/project/.archon"),
                iter_num=1,
                target=Path("/project/Problem.lean"),
                review_certificate={"failed_check_ids": ["coverage"]},
                debug_feedback=False,
            )
        self.assertIn("SEMANTIC DAG SENTINEL", prompt)
        self.assertIn('"failed_check_ids"', prompt)
        self.assertNotIn(
            "Mandatory source-closure repair decision procedure", prompt,
        )

    def test_immediate_redraft_prompt_keeps_large_accepted_feedback(self) -> None:
        digest = "a" * 64
        passed = {"status": "passed", "evidence": "source-bound check passed"}
        certificate = {
            "schema_version": 2,
            "status": "failed",
            "reason": "OPEN_AIR_BRIDGE_IS_NOT_SOURCE_DERIVED",
            "checks": {
                "source_faithfulness": {
                    "status": "failed",
                    "evidence": "the residue identity is an answer-shaped premise",
                },
                "derivability": {
                    "status": "failed",
                    "evidence": "the requested identity is not uniquely derived",
                },
                "abstraction_sufficiency": dict(passed),
                "uncertainty_propagation": {
                    "status": "not_applicable",
                    "evidence": "no source uncertainty applies",
                },
                "branch_orientation": {
                    "status": "not_applicable",
                    "evidence": "no algebraic branch applies",
                },
                "countermodel_resistance": dict(passed),
            },
            "bridge_obligations": [
                {
                    "claim": f"source-bound bridge {index}",
                    "carrier": f"missing_carrier_{index}",
                    "status": "blocked",
                    "evidence": f"repair this exact missing bridge {index}",
                }
                for index in range(6)
            ],
            "source_contract": {
                "schema_version": 1,
                "contract_kind": "native_problem_input_only",
                "authority": "problem-only",
                "evaluation_mode": "answer_blind",
                "target": "IChO2026Problems/Problem.lean",
                "source_bundle": "icho_2026_source/questions_only.jsonl",
                "source_record_id": "problem",
                "candidate": "IChO2026Problems/Problem.lean",
                "candidate_sha256": digest,
                "source_bundle_sha256": "1" * 64,
                "source_record_sha256": "2" * 64,
                "answer_submission_sha256": "3" * 64,
                "question_sha256": "4" * 64,
                "requested_outputs_sha256": "5" * 64,
            },
            "blind_source_audit": {
                "answer_independence": {
                    "status": "passed",
                    "evidence": "review remained answer blind",
                },
            },
            # Accepted certificates retain richer audit evidence than the
            # controller-safe hand-off projection. Reproduce the >24 KiB case
            # that previously crashed before the projection could be used.
            "controller_audit_padding": "x" * (25 * 1024),
        }
        certificate_bytes = json.dumps(
            certificate,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        self.assertGreater(len(certificate_bytes), 24 * 1024)
        event = build_feedback_event(
            review_kind="formalization",
            candidate_sha256=digest,
            event_id="pipeline:1:Problem.lean:formalization:1",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate=certificate,
            decision="failed",
            preflight={
                "status": "passed",
                "compiles": True,
                "returncode": 0,
                "sorry_count": 2,
            },
        )
        record = {
            "status": "retry",
            "reviews": 1,
            "candidate_sha256": digest,
            "certificate": certificate,
            "repair_events": [event],
        }
        with patch(
            "archon.commands.loop.review_feedback."
            "validate_native_review_source_certificate",
            return_value="",
        ):
            repair_task = build_repair_task(
                record,
                review_kind="formalization",
                worker_stage="formalization",
                candidate_sha256=digest,
                expected_source_contract={
                    "contract_kind": "native_problem_input_only",
                },
            )
        source_review = repair_task["source_bound_review"]
        self.assertEqual(len(source_review["repair_actions"]), 6)
        projection = source_review["repair_action_projection"]
        self.assertEqual(projection["failed_bridge_count"], 6)
        self.assertEqual(projection["retained_count"], 6)
        self.assertFalse(projection["truncated"])
        self.assertEqual(
            source_review["source_binding"],
            {
                "candidate_sha256": digest,
                "source_bundle_sha256": "1" * 64,
                "source_record_sha256": "2" * 64,
                "answer_submission_sha256": "3" * 64,
                "question_sha256": "4" * 64,
                "requested_outputs_sha256": "5" * 64,
            },
        )
        self.assertEqual(len(repair_task["history"]["events"]), 1)
        self.assertEqual(
            repair_task["history"]["events"][0]["iteration"], 1,
        )
        expected_certificate_sha256 = hashlib.sha256(certificate_bytes).hexdigest()
        self.assertEqual(
            source_review["certificate_sha256"], expected_certificate_sha256,
        )
        mode_reference = (
            "Read `/project/.archon/prover-modes/chemistry-formalize.md` "
            f"sha256={'f' * 64} bytes=10295"
        )

        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value=mode_reference,
            ) as sealed_mode,
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                side_effect=lambda *_args, **kwargs: (
                    "B" * 2_200 + kwargs["mode_content"]
                ),
            ) as base_prompt,
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="S" * 12_095,
            ),
        ):
            prompt = build_immediate_redraft_prompt(
                project_name="project",
                project_path=Path("/project"),
                state_dir=Path("/project/.archon"),
                iter_num=1,
                target=Path("/project/Problem.lean"),
                review_certificate=repair_task,
                debug_feedback=False,
                handoff_label="formalization Review",
            )

        self.assertLessEqual(len(prompt.encode("utf-8")), MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES)
        self.assertIn(
            "/project/.archon/prover-modes/chemistry-formalize.md", prompt,
        )
        sealed_mode.assert_called_once_with(
            Path("/project/.archon"), "chemistry-formalize",
        )
        self.assertEqual(
            base_prompt.call_args.kwargs["mode_content"],
            mode_reference,
        )
        self.assertIn("OPEN_AIR_BRIDGE_IS_NOT_SOURCE_DERIVED", prompt)
        self.assertIn(expected_certificate_sha256, prompt)
        self.assertIn('"iteration":1', prompt)
        self.assertIn('"attempt":1', prompt)
        for index in range(6):
            self.assertIn(f'"check_id":"bridge_obligations[{index}]"', prompt)
        self.assertNotIn("controller_audit_padding", prompt)
        self.assertNotIn(".archon/prompts/prover-autoformalize.md", prompt)

    def test_immediate_redraft_prompt_keeps_a6_cycle_three_feedback(
        self,
    ) -> None:
        repair_task = _a6_cycle_three_repair_task()
        self.assertEqual(MAX_REPAIR_TASK_PROMPT_BYTES, 24 * 1024)
        self.assertEqual(MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES, 128 * 1024)
        rendered_task = render_repair_task(repair_task)
        self.assertEqual(len(rendered_task.encode("utf-8")), 8_700)
        self.assertLess(
            len(rendered_task.encode("utf-8")),
            MAX_REPAIR_TASK_PROMPT_BYTES,
        )

        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="B" * 2_200,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="S" * 12_095,
            ),
        ):
            prompt = build_immediate_redraft_prompt(
                project_name="project",
                project_path=Path("/project"),
                state_dir=Path("/project/.archon"),
                iter_num=1,
                target=Path("/project/Problem.lean"),
                review_certificate=repair_task,
                debug_feedback=False,
                handoff_label="formalization Review",
            )

        prompt_bytes = len(prompt.encode("utf-8"))
        self.assertGreater(prompt_bytes, MAX_REPAIR_TASK_PROMPT_BYTES)
        self.assertLess(prompt_bytes, MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES)
        source_review = repair_task["source_bound_review"]
        projection = source_review["repair_action_projection"]
        self.assertEqual(projection["failed_bridge_count"], 10)
        self.assertEqual(projection["retained_count"], 10)
        self.assertFalse(projection["truncated"])
        self.assertEqual(len(source_review["repair_actions"]), 10)
        self.assertIn('"attempt":2', prompt)
        self.assertIn('"candidate_sha256":"' + "a" * 64 + '"', prompt)
        self.assertIn('"certificate_sha256":"' + "b" * 64 + '"', prompt)
        for index in [2, 3, 5, 7, 8, 10, 12, 13, 15, 16]:
            self.assertIn(
                f'"check_id":"bridge_obligations[{index}]"',
                prompt,
            )


    def test_immediate_redraft_prompt_only_drops_old_history_events(self) -> None:
        oversized_task = {
            "failed_check_ids": ["coverage"],
            "required_actions": [
                "repair_the_statement_or_model_then_revalidate",
            ],
            "history": {
                "events": [
                    {"event_id": str(index), "codes": ["历史" * 200]}
                    for index in range(20)
                ],
            },
        }
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="B" * 20_000,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="SEMANTIC DAG SENTINEL",
            ),
        ):
            prompt = build_immediate_redraft_prompt(
                project_name="project",
                project_path=Path("/project"),
                state_dir=Path("/project/.archon"),
                iter_num=1,
                target=Path("/project/Problem.lean"),
                review_certificate=oversized_task,
                debug_feedback=False,
            )
        self.assertLessEqual(len(prompt.encode("utf-8")), MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES)
        self.assertIn("\"failed_check_ids\":[\"coverage\"]", prompt)
        self.assertIn("\"event_id\":\"19\"", prompt)
        self.assertNotIn("\"event_id\":\"0\"", prompt)
    def test_immediate_redraft_prompt_rejects_truncated_source_feedback(
        self,
    ) -> None:
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="BASE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="",
            ),
        ):
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "cannot retain complete repair feedback",
            ):
                build_immediate_redraft_prompt(
                    project_name="project",
                    project_path=Path("/project"),
                    state_dir=Path("/project/.archon"),
                    iter_num=1,
                    target=Path("/project/Problem.lean"),
                    review_certificate=_source_bound_repair_task(
                        truncated=True,
                    ),
                    debug_feedback=False,
                )

    def test_immediate_redraft_prompt_rejects_dropped_source_feedback(
        self,
    ) -> None:
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="B" * 20_000,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="",
            ),
        ):
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "cannot retain complete repair feedback",
            ):
                build_immediate_redraft_prompt(
                    project_name="project",
                    project_path=Path("/project"),
                    state_dir=Path("/project/.archon"),
                    iter_num=1,
                    target=Path("/project/Problem.lean"),
                    review_certificate=_source_bound_repair_task(
                        evidence_size=MAX_REPAIR_TASK_PROMPT_BYTES,
                    ),
                    debug_feedback=False,
                )

    def test_immediate_redraft_prompt_rejects_empty_non_source_projection(
        self,
    ) -> None:
        repair_task = {
            "schema_version": 1,
            "kind": "controller_sanitized_review_repair",
            "candidate_sha256": "a" * 64,
            "failed_check_ids": ["coverage"],
            "required_actions": ["preserve the required repair"],
        }
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="BASE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="",
            ),
            patch(
                "archon.commands.loop.prover.runners.bound_repair_task",
                return_value={},
            ),
        ):
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "cannot retain complete repair feedback",
            ):
                build_immediate_redraft_prompt(
                    project_name="project",
                    project_path=Path("/project"),
                    state_dir=Path("/project/.archon"),
                    iter_num=1,
                    target=Path("/project/Problem.lean"),
                    review_certificate=repair_task,
                    debug_feedback=False,
                )

    def test_immediate_redraft_prompt_rejects_over_128_kib(self) -> None:
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._sealed_mode_reference",
                return_value="SEALED MODE REFERENCE",
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="B" * MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "_native_formalizer_semantic_dag_block",
                return_value="",
            ),
        ):
            with self.assertRaisesRegex(
                _ImmediateRedraftPromptError,
                "exceeds 128 KiB",
            ):
                build_immediate_redraft_prompt(
                    project_name="project",
                    project_path=Path("/project"),
                    state_dir=Path("/project/.archon"),
                    iter_num=1,
                    target=Path("/project/Problem.lean"),
                    review_certificate={
                        "failed_check_ids": ["coverage"],
                    },
                    debug_feedback=False,
                )



if __name__ == "__main__":
    unittest.main()
